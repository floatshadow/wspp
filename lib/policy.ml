(** A small policy language, dup-free weighted NetKAT (Figure 5), compiled to wSPPs. *)

open! Core

type ('f, 'v) pred =
  | True
  | False
  | Test of 'f * 'v
  | Neg of ('f, 'v) pred
  | And of ('f, 'v) pred * ('f, 'v) pred
  | Or of ('f, 'v) pred * ('f, 'v) pred
[@@deriving sexp_of]

type ('f, 'v, 'w) t =
  | Filter of ('f, 'v) pred
  | Assign of 'f * 'v
  | Seq of ('f, 'v, 'w) t * ('f, 'v, 'w) t
  | Choice of ('f, 'v, 'w) t * ('f, 'v, 'w) t
  | Weighted of 'w * ('f, 'v, 'w) t
  | Star of ('f, 'v, 'w) t
[@@deriving sexp_of]

(* Negation is pushed to the literals by De Morgan, because [¬] has no wSPP counterpart. *)
let rec negate = function
  | True -> False
  | False -> True
  | Test (f, v) -> Neg (Test (f, v))
  | Neg p -> p
  | And (p, q) -> Or (negate p, negate q)
  | Or (p, q) -> And (negate p, negate q)

let rec compile_pred man = function
  | True -> Canonical.one man
  | False -> Canonical.zero man
  | Test (f, v) -> Canonical.test man f v
  | Neg (Test (f, v)) -> Canonical.test_neq man f v
  | Neg p -> compile_pred man (negate p)
  | And (p, q) -> Algebra.seq (compile_pred man p) (compile_pred man q)
  (* Choice is not idempotent (Example 3.2), so a disjunction must be a disjoint sum. *)
  | Or (p, q) ->
      Algebra.add (compile_pred man p)
        (Algebra.seq (compile_pred man (negate p)) (compile_pred man q))

let rec compile man = function
  | Filter p -> compile_pred man p
  | Assign (f, v) -> Canonical.assign man f v
  | Seq (Star p, q) -> Star.star_then (compile man p) (compile man q)
  | Seq (p, q) -> Algebra.seq (compile man p) (compile man q)
  | Choice (p, q) -> Algebra.add (compile man p) (compile man q)
  | Weighted (w, p) -> Algebra.scale w (compile man p)
  | Star p -> Star.star (compile man p)
