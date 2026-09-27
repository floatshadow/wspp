(** Pareto frontier semirings (Section 5.1) and trace-carrying weights (Section 5.2). *)

open! Core

(** A partially ordered monoid whose [mul] is monotone in both arguments, oriented so that bigger is
    better. [compare] is an arbitrary total order compatible with [equal], used only to keep
    frontiers in a canonical order. *)
module type Po_monoid = sig
  type t [@@deriving compare, equal, hash, sexp_of]

  val one : t
  val mul : t -> t -> t
  val leq : t -> t -> bool
end

(** Latency [(N ∪ {∞}, +, 0)], smaller is better. Bounded: the unit [0] is the top element. *)
module Latency : sig
  include Po_monoid with type t = Semiring.Nat_inf.t

  val of_int : int -> t
end = struct
  include Semiring.Nat_inf

  let of_int = of_int ~context:"Latency.of_int"
  let one = Fin 0
  let mul = add
  let leq a b = compare a b >= 0
end

(** Bandwidth [(Z ∪ {±∞}, min, ∞)], bigger is better. Bounded: the unit [∞] is the top. *)
module Bandwidth : sig
  include Po_monoid with type t = Semiring.Int_ext.t

  val of_int : int -> t
end = struct
  include Semiring.Int_ext

  let of_int n = Fin n
  let one = Pos_inf
  let mul = min
  let leq a b = compare a b <= 0
end

(** Componentwise product: multi-objective cost vectors. *)
module Pair (A : Po_monoid) (B : Po_monoid) : Po_monoid with type t = A.t * B.t = struct
  type t = A.t * B.t [@@deriving compare, equal, hash, sexp_of]

  let one = (A.one, B.one)
  let mul (a1, b1) (a2, b2) = (A.mul a1 a2, B.mul b1 b2)
  let leq (a1, b1) (a2, b2) = A.leq a1 a2 && B.leq b1 b2
end

(** [is_subsequence v u]: [v] can be obtained from [u] by deleting events. *)
let rec is_subsequence ~equal v u =
  match (v, u) with
  | [], _ -> true
  | _ :: _, [] -> false
  | x :: v', y :: u' ->
      if equal x y then is_subsequence ~equal v' u' else is_subsequence ~equal v u'

(** Weighted traces [T × Σ*] (Definition 5.4): costs multiply and traces concatenate. A trace is
    better than another if it is a subsequence of it, except that the empty trace is comparable only
    to itself, so a run that logged nothing never absorbs one that logged something. *)
module Trace (T : Po_monoid) (Event : Key.S) : Po_monoid with type t = T.t * Event.t list = struct
  type t = T.t * Event.t list [@@deriving compare, equal, hash, sexp_of]

  let one = (T.one, [])

  (* Traces concatenate by definition; [mul] is not recursive, so the append is linear. *)
  (* nosemgrep: ocaml.perf.append-in-recursive-function *)
  let mul (p, u) (q, v) = (T.mul p q, u @ v)

  let trace_leq u v =
    match (u, v) with
    | [], [] -> true
    | _, [] -> false
    | _, _ :: _ -> is_subsequence ~equal:Event.equal v u

  let leq (p, u) (q, v) = T.leq p q && trace_leq u v
end

(** The frontier semiring [Fr(T)] (Definition 5.2): finite antichains of [T] under Pareto dominance,
    kept sorted by [T.compare] so that [equal] is list equality. For trace-carrying frontiers use
    [Frontier (Trace (T) (Event))]. *)
module Frontier (T : Po_monoid) : sig
  include Semiring.S with type t = private T.t list

  val of_list : T.t list -> t
  (** The frontier of the maximal elements of a finite set. *)

  val to_list : t -> T.t list
end = struct
  type t = T.t list [@@deriving equal, hash, sexp_of]

  let dominated_by p q = T.leq p q && not (T.equal p q)

  let of_list ps =
    let ps = List.dedup_and_sort ps ~compare:T.compare in
    List.filter ps ~f:(fun p -> not (List.exists ps ~f:(dominated_by p)))

  let to_list f = f
  let zero = []
  let one = [ T.one ]
  let add f g = of_list (List.rev_append f g)
  let mul f g = of_list (List.concat_map f ~f:(fun p -> List.map g ~f:(T.mul p)))

  (* [F⊛ = G_N] for the first [N] with [G_{N+1} = G_N], where [G_0 = 1], [G_{n+1} = 1 + F·G_n].
     This stabilizes at once for bounded [T] and after two rounds for trace-carrying [T]. *)
  let max_star_iterations = 10_000

  let star f =
    let rec go g i =
      if i > max_star_iterations then
        failwith "Pareto.Frontier.star: iteration does not stabilize (is T bounded?)"
      else
        let g' = add one (mul f g) in
        if equal g g' then g else go g' (i + 1)
    in
    go one 0
end
