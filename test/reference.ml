(** Brute-force reference semantics of policies (Figure 5) as explicit matrices over packets, and
    randomized checks of wSPPs against it.

    Packets range over [num_values] values in every field. Policies only mention the constants below
    [num_constants]; the other values stand for "all other values", which the constants cannot tell
    apart. Two fresh values are enough to catch a default confused with identity. *)

open! Core
module Policy = Wspp.Policy

type config = { num_fields : int; num_constants : int; num_values : int }

let packets cfg =
  let rec go f =
    if f = cfg.num_fields then [ [] ]
    else
      List.concat_map (go (f + 1)) ~f:(fun rest -> List.init cfg.num_values ~f:(fun v -> v :: rest))
  in
  Array.of_list_map (go 0) ~f:Array.of_list

(* Field 0 varies fastest in [packets]. *)
let index cfg packet = Array.fold_right packet ~init:0 ~f:(fun v acc -> (acc * cfg.num_values) + v)

let rec holds (pkt : int array) : (int, int) Policy.pred -> bool = function
  | True -> true
  | False -> false
  | Test (f, v) -> pkt.(f) = v
  | Neg p -> not (holds pkt p)
  | And (p, q) -> holds pkt p && holds pkt q
  | Or (p, q) -> holds pkt p || holds pkt q

module Make (W : Wspp.Semiring.S) = struct
  type policy = (int, int, W.t) Policy.t
  type matrix = W.t array array

  let matrix_init n ~f = Array.init n ~f:(fun i -> Array.init n ~f:(fun j -> f i j))

  let mat_mul (a : matrix) (b : matrix) =
    let n = Array.length a in
    matrix_init n ~f:(fun i j ->
        let acc = ref W.zero in
        for k = 0 to n - 1 do
          acc := W.add !acc (W.mul a.(i).(k) b.(k).(j))
        done;
        !acc)

  (* Lehmann's (Floyd-Warshall-Kleene) algorithm: valid in every Conway semiring, and independent
     of the symbolic state elimination under test. *)
  let mat_star (a : matrix) =
    let n = Array.length a in
    let a = Array.map a ~f:Array.copy in
    for k = 0 to n - 1 do
      let c = W.star a.(k).(k) in
      let col = Array.init n ~f:(fun i -> a.(i).(k)) in
      let row = Array.copy a.(k) in
      for i = 0 to n - 1 do
        if not (W.equal col.(i) W.zero) then
          let ic = W.mul col.(i) c in
          for j = 0 to n - 1 do
            a.(i).(j) <- W.add a.(i).(j) (W.mul ic row.(j))
          done
      done
    done;
    matrix_init n ~f:(fun i j -> W.add (if i = j then W.one else W.zero) a.(i).(j))

  let rec denote cfg pkts (e : policy) : matrix =
    let n = Array.length pkts in
    match e with
    | Filter p -> matrix_init n ~f:(fun i j -> if i = j && holds pkts.(i) p then W.one else W.zero)
    | Assign (f, v) ->
        let target i =
          let pkt = Array.copy pkts.(i) in
          pkt.(f) <- v;
          index cfg pkt
        in
        matrix_init n ~f:(fun i j -> if j = target i then W.one else W.zero)
    | Seq (p, q) -> mat_mul (denote cfg pkts p) (denote cfg pkts q)
    | Choice (p, q) ->
        let a = denote cfg pkts p and b = denote cfg pkts q in
        matrix_init n ~f:(fun i j -> W.add a.(i).(j) b.(i).(j))
    | Weighted (w, p) -> Array.map (denote cfg pkts p) ~f:(Array.map ~f:(W.mul w))
    | Star p -> mat_star (denote cfg pkts p)

  let semantics_of_wspp cfg pkts t : matrix =
    let fields = List.init cfg.num_fields ~f:Fn.id in
    matrix_init (Array.length pkts) ~f:(fun i j ->
        Wspp.eval t ~fields ~input:(fun f -> pkts.(i).(f)) ~output:(fun f -> pkts.(j).(f)))

  let matrix_equal (a : matrix) b = Array.equal (Array.equal W.equal) a b
  let string_of_policy e =
    Sexp.to_string_hum (Policy.sexp_of_t Int.sexp_of_t Int.sexp_of_t W.sexp_of_t e)

  (* ------------------------------------------------------------------------------------------ *)
  (* Random policies                                                                            *)
  (* ------------------------------------------------------------------------------------------ *)

  let gen_pred cfg rng : (int, int) Policy.pred =
    let field () = Random.State.int rng cfg.num_fields in
    let value () = Random.State.int rng cfg.num_constants in
    let rec go depth : (int, int) Policy.pred =
      match Random.State.int rng (if depth = 0 then 3 else 7) with
      | 0 | 1 -> Test (field (), value ())
      | 2 -> if Random.State.bool rng then True else False
      | 3 -> Neg (go (depth - 1))
      | 4 | 5 -> And (go (depth - 1), go (depth - 1))
      | _ -> Or (go (depth - 1), go (depth - 1))
    in
    go 2

  let gen cfg ~weights rng ~depth : policy =
    let field () = Random.State.int rng cfg.num_fields in
    let value () = Random.State.int rng cfg.num_constants in
    let weight () = List.nth_exn weights (Random.State.int rng (List.length weights)) in
    (* A weighted guarded command [t ; w ⊙ f ← v], or a weighted filter: the typical summands
       of a loop body, which make stars exercise every pass of the elimination. *)
    let guarded () : policy =
      if Random.State.bool rng then
        Seq (Filter (gen_pred cfg rng), Weighted (weight (), Assign (field (), value ())))
      else Weighted (weight (), Filter (gen_pred cfg rng))
    in
    let rec go depth : policy =
      match Random.State.int rng (if depth = 0 then 3 else 12) with
      | 0 -> Filter (gen_pred cfg rng)
      | 1 -> Assign (field (), value ())
      | 2 -> guarded ()
      | 3 | 4 -> Seq (go (depth - 1), go (depth - 1))
      | 5 | 6 -> Choice (go (depth - 1), go (depth - 1))
      | 7 | 8 -> Weighted (weight (), go (depth - 1))
      | 9 -> Star (Choice (guarded (), Choice (guarded (), guarded ())))
      | _ -> Star (go (depth - 1))
    in
    go depth

  (** Hand-picked policies whose shapes the random generator rarely hits. They need five constants.
  *)
  let regression_policies ~weights : policy list =
    let w i = List.nth_exn weights (i % List.length weights) in
    let open Policy in
    let test f v : policy = Filter (Test (f, v))
    and neq f v : policy = Filter (Neg (Test (f, v))) in
    let plus a b : policy = Choice (a, b) in
    (* A default assignment that shadows the default identity at the value it writes. *)
    let shadow = plus (Assign (0, 1)) (Weighted (w 0, neq 0 1)) in
    (* The running example 4.8 of the paper, on field 0. *)
    let running =
      List.reduce_exn ~f:plus
        [
          Seq (test 0 1, Weighted (w 0, Assign (0, 1)));
          Seq (test 0 1, Weighted (w 1, Assign (0, 4)));
          Seq (test 0 2, Weighted (w 0, Assign (0, 1)));
          Seq (neq 0 1, Seq (neq 0 2, Weighted (w 1, Assign (0, 1))));
          Seq (neq 0 1, Seq (neq 0 2, Weighted (w 0, Assign (0, 3))));
          Seq (neq 0 1, Seq (neq 0 2, Seq (neq 0 3, Weighted (w 1, Filter True))));
        ]
    in
    (* An entry that can fall through the default identity (Pass I). *)
    let fall_through = plus (Seq (test 0 0, Assign (0, 1))) (Weighted (w 0, neq 0 0)) in
    (* A local variable (field 1) that is written but never read: untested-field decomposition. *)
    let local =
      plus
        (Seq (test 0 0, Seq (Weighted (w 0, Assign (1, 2)), Assign (0, 1))))
        (Seq (test 0 1, Seq (Weighted (w 1, Assign (1, 3)), Assign (0, 0))))
    in
    (* [shadow] writing a local variable: splitting it on field 1 leaves a dead default that
       must keep shadowing the identity. *)
    let shadow_local =
      plus (Seq (Assign (0, 1), Weighted (w 0, Assign (1, 2)))) (Weighted (w 1, neq 0 1))
    in
    [
      shadow_local;
      Star shadow_local;
      Seq (Star shadow_local, test 0 1);
      Star (Seq (shadow_local, local));
      shadow;
      Seq (shadow, shadow);
      Seq (shadow, Seq (test 0 1, Assign (0, 2)));
      Choice (shadow, Seq (shadow, Assign (0, 3)));
      Star shadow;
      running;
      Star running;
      Seq (Star running, test 0 1);
      Star fall_through;
      Seq (Star fall_through, neq 0 1);
      local;
      Star local;
      Seq (Star local, Assign (1, 0));
      Star (Seq (local, Weighted (w 1, local)));
    ]

  (* ------------------------------------------------------------------------------------------ *)
  (* Checks                                                                                     *)
  (* ------------------------------------------------------------------------------------------ *)

  let all_optimizations =
    List.concat_map [ true; false ] ~f:(fun untested_field_decomposition ->
        List.map [ true; false ] ~f:(fun trailing_star ->
            { Wspp.untested_field_decomposition; trailing_star }))

  let report_mismatch pkts e expected actual =
    let n = Array.length pkts in
    let string_of_packet p =
      String.concat ~sep:"," (Array.to_list (Array.map p ~f:Int.to_string))
    in
    let string_of_weight w = Sexp.to_string (W.sexp_of_t w) in
    print_endline [%string "MISMATCH for policy: %{string_of_policy e}"];
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        if not (W.equal expected.(i).(j) actual.(i).(j)) then
          print_endline
            [%string
              "  [%{string_of_packet pkts.(i)}] -> [%{string_of_packet pkts.(j)}]: expected \
               %{string_of_weight expected.(i).(j)}, got %{string_of_weight actual.(i).(j)}"]
      done
    done

  (* Compiles [e] under every optimization setting; checks the result against the reference
     semantics and that every setting yields the same canonical node. *)
  let check_policy man cfg pkts e =
    let expected = denote cfg pkts e in
    let compiled =
      List.map all_optimizations ~f:(fun o ->
          Wspp.Man.set_optimizations man o;
          Wspp.of_policy man e)
    in
    Wspp.Man.set_optimizations man (List.hd_exn all_optimizations);
    let first = List.hd_exn compiled in
    let actual = semantics_of_wspp cfg pkts first in
    if not (matrix_equal expected actual) then (
      report_mismatch pkts e expected actual;
      false)
    else if not (List.for_all compiled ~f:(Wspp.equal first)) then (
      print_endline [%string "MISMATCH: optimization settings disagree on %{string_of_policy e}"];
      false)
    else true

  (** Checks each of [policies]; returns the number of failures. *)
  let check_policies man cfg policies =
    let pkts = packets cfg in
    List.count policies ~f:(fun e -> not (check_policy man cfg pkts e))

  (** Checks [count] random policies; returns the number of failures. *)
  let check_semantics man cfg ~weights ~count ~depth ~seed =
    let rng = Random.State.make [| seed |] in
    check_policies man cfg (List.init count ~f:(fun _ -> gen cfg ~weights rng ~depth))

  (** Checks algebraic laws as identities of canonical nodes (Theorem 6.1), and that semantic
      equality of random pairs implies node equality. Returns the number of failures. *)
  let check_canonicity man cfg ~weights ~count ~depth ~seed =
    let rng = Random.State.make [| seed |] in
    let pkts = packets cfg in
    let failures = ref 0 in
    let law name lhs rhs =
      if not (Wspp.equal lhs rhs) then (
        incr failures;
        print_endline [%string "LAW FAILED: %{name}"])
    in
    let one = Wspp.one man in
    let add = Wspp.add and seq = Wspp.seq and star = Wspp.star in
    for _ = 1 to count do
      let a = Wspp.of_policy man (gen cfg ~weights rng ~depth) in
      let b = Wspp.of_policy man (gen cfg ~weights rng ~depth) in
      let c = Wspp.of_policy man (gen cfg ~weights rng ~depth) in
      law "add commutative" (add a b) (add b a);
      law "add associative" (add a (add b c)) (add (add a b) c);
      law "seq associative" (seq a (seq b c)) (seq (seq a b) c);
      law "left distributive" (seq a (add b c)) (add (seq a b) (seq a c));
      law "right distributive" (seq (add a b) c) (add (seq a c) (seq b c));
      law "star unfold left" (star a) (add one (seq a (star a)));
      law "star unfold right" (star a) (add one (seq (star a) a));
      law "star_then" (Wspp.star_then a b) (seq (star a) b);
      law "denesting" (star (add a b)) (seq (star a) (star (seq b (star a))));
      let sa = semantics_of_wspp cfg pkts a and sb = semantics_of_wspp cfg pkts b in
      if matrix_equal sa sb && not (Wspp.equal a b) then (
        incr failures;
        print_endline "CANONICITY FAILED: semantically equal wSPPs are different nodes")
    done;
    !failures
end
