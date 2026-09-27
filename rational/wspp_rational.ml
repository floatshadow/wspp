(** Star semirings over exact rationals (zarith), embedded into their real-valued ω-continuous
    counterparts (Figure 14 and Appendix C of the paper). Exact arithmetic keeps [equal] semantic,
    so wSPPs over these weights are canonical. *)

open! Core

(** Zarith rationals with the functions ppx_jane's derivers expect. *)
module Rat = struct
  type t = Q.t

  let compare = Q.compare
  let equal = Q.equal

  (* zarith provides [Z.hash] but no ppx_hash folding; fold the hashes of the (normalized)
     numerator and denominator. *)
  let hash_fold_t state q =
    Hash.fold_int (Hash.fold_int state (Z.hash (Q.num q))) (Z.hash (Q.den q))

  let hash q = Hash.get_hash_value (hash_fold_t (Hash.create ()) q)
  let sexp_of_t q = Sexp.Atom (Q.to_string q)
end

(** Probabilities / expected values: [(Q≥0 ∪ {∞}, +, ·, 0, 1)] with the geometric series
    [a* = 1/(1-a)] for [a < 1] and [∞] otherwise (Example C.1). *)
module Prob : sig
  type t = Fin of Rat.t | Inf

  include Wspp.Semiring.S with type t := t

  val of_q : Q.t -> t

  val of_ints : int -> int -> t
  (** [of_ints n d] is [n/d]. *)
end = struct
  type t = Fin of Rat.t | Inf [@@deriving equal, hash, sexp_of]

  let of_q q =
    if Q.sign q < 0 || not (Q.is_real q) then
      failwith [%string "Prob.of_q: %{Q.to_string q} is not a non-negative rational"]
    else Fin q

  let of_ints n d = of_q (Q.of_ints n d)
  let zero = Fin Q.zero
  let one = Fin Q.one

  let add a b = match (a, b) with Inf, _ | _, Inf -> Inf | Fin x, Fin y -> Fin (Q.add x y)

  let mul a b =
    (* [0 · ∞ = 0]: zero annihilates. *)
    if equal a zero || equal b zero then zero
    else match (a, b) with Inf, _ | _, Inf -> Inf | Fin x, Fin y -> Fin (Q.mul x y)

  let star = function Fin x when Q.lt x Q.one -> Fin (Q.inv (Q.sub Q.one x)) | Fin _ | Inf -> Inf
end

(** Reliability of the best run: the Viterbi semiring [(Q ∩ [0, 1], max, ·, 0, 1)], bounded. *)
module Viterbi : sig
  include Wspp.Semiring.S with type t = Rat.t

  val of_ints : int -> int -> t
end = struct
  type t = Rat.t [@@deriving equal, hash, sexp_of]

  let of_ints n d =
    let q = Q.of_ints n d in
    if Q.lt q Q.zero || Q.gt q Q.one then
      failwith [%string "Viterbi.of_ints: %{Q.to_string q} is not in [0, 1]"]
    else q

  let zero = Q.zero
  let one = Q.one
  let add = Q.max
  let mul = Q.mul
  let star _ = Q.one
end

(** Failure rates: the probabilistic-union semiring [((Q ∩ [0, 1]) ∪ {-∞}, max, ⊎, -∞, 0)] with
    [a ⊎ b = a + b - a·b] (Example C.2). Not bounded; [a* = 1] for [a > 0]. *)
module Prob_union : sig
  type t = Neg_inf | Rate of Rat.t

  include Wspp.Semiring.S with type t := t

  val of_ints : int -> int -> t
end = struct
  type t = Neg_inf | Rate of Rat.t [@@deriving equal, hash, sexp_of]

  let of_ints n d =
    let q = Q.of_ints n d in
    if Q.lt q Q.zero || Q.gt q Q.one then
      failwith [%string "Prob_union.of_ints: %{Q.to_string q} is not in [0, 1]"]
    else Rate q

  let zero = Neg_inf
  let one = Rate Q.zero

  let add a b =
    match (a, b) with Neg_inf, x | x, Neg_inf -> x | Rate x, Rate y -> Rate (Q.max x y)

  let mul a b =
    match (a, b) with
    | Neg_inf, _ | _, Neg_inf -> Neg_inf
    | Rate x, Rate y -> Rate (Q.sub (Q.add x y) (Q.mul x y))

  let star = function Rate x when Q.gt x Q.zero -> Rate Q.one | Rate _ | Neg_inf -> one
end
