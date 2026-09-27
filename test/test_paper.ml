(** The worked examples of the paper, as expect tests. *)

open! Core
open Wspp_rational

(* Field values mixing numbers and symbols, e.g. switch ids and transmission states. *)
module Value = struct
  type t = Num of int | Sym of string [@@deriving compare, equal, hash, sexp_of]
end

let num n = Value.Num n
let sym s = Value.Sym s

let print_document doc =
  let buf = Buffer.create 256 in
  PPrint.ToBuffer.pretty 0.8 100 buf doc;
  print_endline (Buffer.contents buf)

(* [⟦p⟧(α)(β)] for packets given as association lists over the same fields. *)
let weight_between p alpha beta =
  let lookup packet f = List.Assoc.find_exn packet f ~equal:String.equal in
  Wspp.eval p ~fields:(List.map alpha ~f:fst) ~input:(lookup alpha) ~output:(lookup beta)

let%expect_test "Example 2.1: arctic and tropical choice" =
  let example (type w) (module W : Wspp.Semiring.S with type t = w) (w : int -> w) =
    let man = Wspp.Man.create (module String) (module Value) (module W) in
    let open Wspp in
    let p =
      sum man
        [
          scale (w 2) (test man "f" (num 1));
          scale (w 4) (assign man "f" (num 2));
          scale (w 10) (assign man "f" (num 2));
        ]
    in
    let show v =
      Sexp.to_string (W.sexp_of_t (weight_between p [ ("f", num 1) ] [ ("f", num v) ]))
    in
    print_endline [%string "1 -> 1: %{show 1}, 1 -> 2: %{show 2}, 1 -> 3: %{show 3}"]
  in
  example (module Wspp.Semiring.Arctic) (fun n -> Fin n);
  example (module Wspp.Semiring.Tropical) Wspp.Semiring.Tropical.of_int;
  [%expect
    {|
    1 -> 1: (Fin 2), 1 -> 2: (Fin 10), 1 -> 3: Neg_inf
    1 -> 1: (Fin 2), 1 -> 2: (Fin 4), 1 -> 3: Inf
    |}]

(* The retry protocol of Figures 1 and 2 over exact probabilities. *)
let%expect_test "Figures 1 and 2: iterating a probabilistic retry protocol" =
  let man = Wspp.Man.create (module String) (module Value) (module Prob) in
  let open Wspp in
  let q n d = Prob.of_ints n d in
  let slot =
    seq
      (test man "sw" (num 1))
      (sum man
         [
           seq
             (test man "st" (sym "rdy"))
             (sum man
                [
                  scale (q 1 4) (assign man "sw" (num 2));
                  scale (q 1 2) (assign man "st" (sym "wait"));
                  scale (q 1 4) (zero man);
                ]);
           seq
             (test man "st" (sym "wait"))
             (sum man
                [
                  scale (q 1 2) (one man);
                  scale (q 1 4) (assign man "st" (sym "rdy"));
                  scale (q 1 4) (zero man);
                ]);
         ])
  in
  print_document (pp slot);
  let delivered = star_then slot (test_neq man "sw" (num 1)) in
  print_document (pp delivered);
  let from st =
    weight_between delivered [ ("sw", num 1); ("st", sym st) ] [ ("sw", num 2); ("st", sym "rdy") ]
  in
  print_s [%sexp (from "rdy" : Prob.t), (from "wait" : Prob.t)];
  [%expect
    {|
    wspp(st,
      {(Sym rdy) ↦ {(Sym rdy) ↦ wspp(sw,
        {(Num 1) ↦ {(Num 2) ↦ (Fin 1/4)}},
        {},
        (Fin 0)),
      (Sym wait) ↦ wspp(sw, {(Num 1) ↦ {(Num 1) ↦ (Fin 1/2)}}, {}, (Fin 0))},
      (Sym wait) ↦ {(Sym rdy) ↦ wspp(sw,
        {(Num 1) ↦ {(Num 1) ↦ (Fin 1/4)}},
        {},
        (Fin 0)),
      (Sym wait) ↦ wspp(sw, {(Num 1) ↦ {(Num 1) ↦ (Fin 1/2)}}, {}, (Fin 0))}},
      {},
      (Fin 0))
    wspp(st,
      {(Sym rdy) ↦ {(Sym rdy) ↦ wspp(sw,
        {(Num 1) ↦ {(Num 2) ↦ (Fin 1/3)}},
        {},
        (Fin 1))},
      (Sym wait) ↦ {(Sym rdy) ↦ wspp(sw,
        {(Num 1) ↦ {(Num 2) ↦ (Fin 1/6)}},
        {},
        (Fin 0)),
      (Sym wait) ↦ wspp(sw, {(Num 1) ↦ {}}, {}, (Fin 1))}},
      {},
      wspp(sw, {(Num 1) ↦ {}}, {}, (Fin 1)))
    ((Fin 1/3) (Fin 1/6))
    |}]

module Cost = Wspp.Pareto.Pair (Wspp.Pareto.Latency) (Wspp.Pareto.Bandwidth)
module Frontier = Wspp.Pareto.Frontier (Cost)
module Traced_frontier = Wspp.Pareto.Frontier (Wspp.Pareto.Trace (Cost) (String))

let cost l b = (Wspp.Pareto.Latency.of_int l, Wspp.Pareto.Bandwidth.of_int b)
let unbounded = (Wspp.Pareto.Latency.of_int 0, Wspp.Semiring.Int_ext.Pos_inf)

(* The two-class bypass chain of Figure 3, generic in how a weight [(cost, event)] is encoded. *)
let bypass_chain man ~weigh =
  let open Wspp in
  let upgrade =
    add (one man)
      (seq
         (test man "cls" (sym "be"))
         (scale (weigh (cost 1 25) [ "u" ]) (assign man "cls" (sym "gold"))))
  in
  let segment i =
    add
      (seq
         (test man "sw" (num (i - 1)))
         (scale (weigh (cost 0 (10 * i)) []) (assign man "sw" (num i))))
      (seq
         (test man "cls" (sym "gold"))
         (scale (weigh (cost i 80) [ [%string "d%{i#Int}"] ]) (assign man "sw" (num i))))
  in
  product man
    (scale (weigh unbounded [ "adm" ]) (one man) :: upgrade :: List.map [ 1; 2; 3; 4 ] ~f:segment)

let%expect_test "Figure 3: latency-bandwidth frontiers of the bypass chain" =
  let man = Wspp.Man.create (module String) (module Value) (module Frontier) in
  let p = bypass_chain man ~weigh:(fun c _ -> Frontier.of_list [ c ]) in
  let from cls =
    weight_between p [ ("sw", num 0); ("cls", sym cls) ] [ ("sw", num 4); ("cls", sym "gold") ]
  in
  print_s [%sexp (from "gold" : Frontier.t)];
  print_s [%sexp (from "be" : Frontier.t)];
  [%expect
    {|
    (((Fin 0) (Fin 10)) ((Fin 1) (Fin 20)) ((Fin 3) (Fin 30)) ((Fin 6) (Fin 40))
     ((Fin 10) (Fin 80)))
    (((Fin 1) (Fin 10)) ((Fin 2) (Fin 20)) ((Fin 4) (Fin 25)))
    |}]

let%expect_test "Section 2.5: every trade-off with its witness" =
  let man = Wspp.Man.create (module String) (module Value) (module Traced_frontier) in
  let p = bypass_chain man ~weigh:(fun c trace -> Traced_frontier.of_list [ (c, trace) ]) in
  let from cls =
    weight_between p [ ("sw", num 0); ("cls", sym cls) ] [ ("sw", num 4); ("cls", sym "gold") ]
  in
  print_s [%sexp (from "gold" : Traced_frontier.t)];
  print_s [%sexp (from "be" : Traced_frontier.t)];
  [%expect
    {|
    ((((Fin 0) (Fin 10)) (adm)) (((Fin 1) (Fin 20)) (adm d1))
     (((Fin 3) (Fin 30)) (adm d1 d2)) (((Fin 6) (Fin 40)) (adm d1 d2 d3))
     (((Fin 10) (Fin 80)) (adm d1 d2 d3 d4)))
    ((((Fin 1) (Fin 10)) (adm u)) (((Fin 2) (Fin 20)) (adm u d1))
     (((Fin 4) (Fin 25)) (adm u d1 d2)))
    |}]

let%expect_test "Example 5.7: witnesses through a monitoring loop" =
  let man = Wspp.Man.create (module String) (module Value) (module Traced_frontier) in
  let open Wspp in
  let w l b event = Traced_frontier.of_list [ (cost l b, [ event ]) ] in
  let hop src dst weight =
    seq (test man "sw" (sym src)) (scale weight (assign man "sw" (sym dst)))
  in
  let loop = Traced_frontier.of_list [ (Cost.one, [ "c" ]) ] in
  let p =
    product man
      [
        add (hop "s" "h" (w 5 2 "a")) (hop "s" "h" (w 1 1 "b"));
        star (hop "h" "h" loop);
        add (hop "h" "t" (w 2 3 "d")) (hop "h" "t" (w 2 5 "e"));
      ]
  in
  print_s [%sexp (weight_between p [ ("sw", sym "s") ] [ ("sw", sym "t") ] : Traced_frontier.t)];
  [%expect
    {|
    ((((Fin 3) (Fin 1)) (b d)) (((Fin 3) (Fin 1)) (b e))
     (((Fin 7) (Fin 2)) (a d)) (((Fin 7) (Fin 2)) (a e)))
    |}]

let%expect_test "Example 4.8: the running example of the star algorithm" =
  let man = Wspp.Man.create (module String) (module Int) (module Prob) in
  let open Wspp in
  let q n d = Prob.of_ints n d in
  let move u v w = seq (test man "f" u) (scale w (assign man "f" v)) in
  let untested = product man [ test_neq man "f" 1; test_neq man "f" 2 ] in
  let rho =
    sum man
      [
        move 1 1 (q 1 2);
        move 1 4 Prob.one;
        move 2 1 (q 1 2);
        seq untested (scale (q 1 5) (assign man "f" 1));
        seq untested (scale (q 1 4) (assign man "f" 3));
        seq untested
          (seq (product man [ test_neq man "f" 1; test_neq man "f" 3 ]) (weight man (q 1 3)));
      ]
  in
  print_document (pp rho);
  let rho_star = star rho in
  print_document (pp rho_star);
  let at u v = Wspp.eval rho_star ~fields:[ "f" ] ~input:(fun _ -> u) ~output:(fun _ -> v) in
  print_s [%sexp (at 2 1 : Prob.t), (at 5 5 : Prob.t), (at 1 4 : Prob.t)];
  [%expect
    {|
    wspp(f,
      {1 ↦ {1 ↦ (Fin 1/2),
      4 ↦ (Fin 1)},
      2 ↦ {1 ↦ (Fin 1/2)}},
      {1 ↦ (Fin 1/5),
      3 ↦ (Fin 1/4)},
      (Fin 1/3))
    wspp(f,
      {1 ↦ {1 ↦ (Fin 10),
      3 ↦ (Fin 5),
      4 ↦ (Fin 15)},
      2 ↦ {1 ↦ (Fin 5),
      2 ↦ (Fin 1),
      3 ↦ (Fin 5/2),
      4 ↦ (Fin 15/2)},
      3 ↦ {1 ↦ (Fin 8/3),
      3 ↦ (Fin 8/3),
      4 ↦ (Fin 4)},
      4 ↦ {1 ↦ (Fin 4),
      3 ↦ (Fin 5/2),
      4 ↦ (Fin 15/2)}},
      {1 ↦ (Fin 4),
      3 ↦ (Fin 5/2),
      4 ↦ (Fin 6)},
      (Fin 3/2))
    ((Fin 5) (Fin 3/2) (Fin 15))
    |}]
