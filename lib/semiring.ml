(** Computable star semirings (Definition 4.2 of the paper) and common instances (Figure 14).
    Semirings over exact rationals live in the [wspp.rational] library, Pareto frontiers in
    [Pareto]. *)

open! Core

(** Required laws, all with respect to [equal]:
    - [(t, add, zero)] is a commutative monoid and [(t, mul, one)] is a monoid. [mul] is {e not}
      required to be commutative;
    - [mul] distributes over [add] on both sides, and [zero] annihilates;
    - [star a] is the infinite sum [one + a + a·a + ...] taken in some ω-continuous semiring that
      [t] embeds into (Definition 4.3). In particular [star a = one + a · star a].

    Canonicity of wSPPs (syntactic equality iff semantic equality) additionally needs [equal] to be
    semantic equality of weights and [hash] to be compatible with it. *)
module type S = sig
  type t [@@deriving equal, hash, sexp_of]

  val zero : t
  val one : t
  val add : t -> t -> t
  val mul : t -> t -> t
  val star : t -> t
end

(** Reachability: [({false, true}, ∨, ∧, false, true)]. Bounded, so [a* = true]. With this semiring
    wSPPs are exactly KATch's SPPs. *)
module Bool : S with type t = bool = struct
  type t = bool [@@deriving equal, hash, sexp_of]

  let zero = false
  let one = true
  let add = ( || )
  let mul = ( && )
  let star _ = true
end

(** Extended naturals [N ∪ {∞}], the carrier of [Tropical] and [Counting]. *)
module Nat_inf = struct
  type t = Fin of int | Inf [@@deriving compare, equal, hash, sexp_of]

  let of_int ~context n =
    if n < 0 then failwith [%string "%{context}: negative weight %{n#Int}"] else Fin n

  let add a b = match (a, b) with Inf, _ | _, Inf -> Inf | Fin x, Fin y -> Fin (x + y)

  let min a b = if compare a b <= 0 then a else b
end

(** Integers extended with both infinities, the carrier of the max-based semirings. *)
module Int_ext = struct
  type t = Neg_inf | Fin of int | Pos_inf [@@deriving compare, equal, hash, sexp_of]

  let min a b = if compare a b <= 0 then a else b
  let max a b = if compare a b >= 0 then a else b
end

(** Latency: [(N ∪ {∞}, min, +, ∞, 0)]. Weights are non-negative, so the semiring is bounded and
    [a* = 0]. *)
module Tropical : sig
  include S with type t = Nat_inf.t

  val of_int : int -> t
end = struct
  include Nat_inf

  let of_int = of_int ~context:"Tropical.of_int"
  let zero = Inf
  let one = Fin 0
  let add = min
  let mul = Nat_inf.add
  let star _ = one
end

(** Worst-case cost: the arctic semiring [(Z ∪ {±∞}, max, +, -∞, 0)]. Not bounded: a positive cycle
    has star [∞]. [-∞] annihilates, including against [∞]. *)
module Arctic : S with type t = Int_ext.t = struct
  include Int_ext

  let zero = Neg_inf
  let one = Fin 0
  let add = max

  let mul a b =
    match (a, b) with
    | Neg_inf, _ | _, Neg_inf -> Neg_inf
    | Pos_inf, _ | _, Pos_inf -> Pos_inf
    | Fin x, Fin y -> Fin (x + y)

  let star a = if compare a one <= 0 then one else Pos_inf
end

(** Bandwidth: the bottleneck semiring [(Z ∪ {±∞}, max, min, -∞, ∞)], bounded. *)
module Bottleneck : S with type t = Int_ext.t = struct
  include Int_ext

  let zero = Neg_inf
  let one = Pos_inf
  let add = max
  let mul = min
  let star _ = one
end

(** Path counting: [(N ∪ {∞}, +, ·, 0, 1)] with [0* = 1] and [a* = ∞] otherwise. *)
module Counting : sig
  include S with type t = Nat_inf.t

  val of_int : int -> t
end = struct
  include Nat_inf

  let of_int = of_int ~context:"Counting.of_int"
  let zero = Fin 0
  let one = Fin 1
  let add = Nat_inf.add

  let mul a b =
    match (a, b) with
    | Fin 0, _ | _, Fin 0 -> zero
    | Inf, _ | _, Inf -> Inf
    | Fin x, Fin y -> Fin (x * y)

  let star a = if equal a zero then one else Inf
end

(** Probabilities / expected values over floats: [([0, ∞], +, ·, 0, 1)], [a* = 1/(1-a)] for [a < 1]
    and [∞] otherwise.

    NOTE: rounding makes [equal] only approximate semantic equality, so canonicity (and cache hits)
    is best-effort; results are still correct up to floating-point error. Prefer
    [Wspp_rational.Prob] for exact arithmetic. *)
module Float_prob : S with type t = float = struct
  type t = float [@@deriving equal, hash, sexp_of]

  let zero = 0.
  let one = 1.
  let add = ( +. )

  (* [0 · ∞ = 0], as the semiring requires; IEEE would give nan. *)
  let mul a b = if Float.equal a 0. || Float.equal b 0. then 0. else a *. b
  let star a = if Float.( < ) a 1. then 1. /. (1. -. a) else Float.infinity
end

(** A bounded distributive lattice, e.g. security levels. *)
module type Bounded_lattice = sig
  type t [@@deriving equal, hash, sexp_of]

  val bottom : t
  val top : t
  val join : t -> t -> t
  val meet : t -> t -> t
end

(** [(L, join, meet, bottom, top)]. Bounded, so [a* = top]. *)
module Lattice (L : Bounded_lattice) : S with type t = L.t = struct
  include L

  let zero = bottom
  let one = top
  let add = join
  let mul = meet
  let star _ = top
end

(** The product semiring runs two analyses at once; the star is taken componentwise. *)
module Product (A : S) (B : S) : S with type t = A.t * B.t = struct
  type t = A.t * B.t [@@deriving equal, hash, sexp_of]

  let zero = (A.zero, B.zero)
  let one = (A.one, B.one)
  let add (a1, b1) (a2, b2) = (A.add a1 a2, B.add b1 b2)
  let mul (a1, b1) (a2, b2) = (A.mul a1 a2, B.mul b1 b2)
  let star (a, b) = (A.star a, B.star b)
end
