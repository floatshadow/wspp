(** The representation shared by the implementation modules. Users go through [Wspp].

    A wSPP is either a leaf [w] or a node [wspp(f, b, m, d)] reading field [f] of the input packet.
    On input value [u] the node takes the branch

    - [b(u)] if [u] is an explicit row of [b];
    - [m ∪ {u ↦ d}] if [u] is mentioned neither by [b] nor by [m] and [d ≠ 0];
    - [m] otherwise,

    where a branch (a row) maps each output value of [f] to the continuation on the remaining
    fields. Sub-wSPPs only mention fields strictly greater than [f] (well-formedness). *)

open! Core

type 'a key = {
  compare : 'a -> 'a -> int;
  equal : 'a -> 'a -> bool;
  hash : 'a -> int;
  sexp_of : 'a -> Sexp.t;
}
(** The operations of a [Key.S], unpacked once when a manager is created. *)

type 'w semiring = {
  zero : 'w;
  one : 'w;
  add : 'w -> 'w -> 'w;
  mul : 'w -> 'w -> 'w;
  star : 'w -> 'w;
  equal : 'w -> 'w -> bool;
  hash : 'w -> int;
  sexp_of : 'w -> Sexp.t;
}
(** The operations of a [Semiring.S], unpacked once when a manager is created. *)

type optimizations = {
  untested_field_decomposition : bool;
      (** Split off a field whose input value is irrelevant before eliminating a star. *)
  trailing_star : bool;  (** Fold the policy after a star into the star's right factors. *)
}
[@@deriving sexp_of]
(** Switches for the algorithmic optimizations of Section 6.1. Canonicalization is always on,
    because hash-consing and equality of wSPPs rely on it. *)

module Pair_key = struct
  type t = int * int [@@deriving compare, hash, sexp_of]
end

(* [id] is unique across all managers; [hkey] caches the structural hash used for
   hash-consing. Every node points to the manager that interned it. *)
type ('f, 'v, 'w) t = { id : int; hkey : int; man : ('f, 'v, 'w) man; view : ('f, 'v, 'w) view }

and ('f, 'v, 'w) view =
  | Leaf of 'w
  | Node of {
      field : 'f;
      branches : ('v * ('f, 'v, 'w) row) list;  (** Sorted by input value. *)
      defaults : ('f, 'v, 'w) row;
      identity : ('f, 'v, 'w) t;
    }

(* Sorted by output value, without duplicate keys. *)
and ('f, 'v, 'w) row = ('v * ('f, 'v, 'w) t) list

and ('f, 'v, 'w) man = {
  uid : int;
  field : 'f key;
  value : 'v key;
  weight : 'w semiring;
  intern : ('f, 'v, 'w) view -> ('f, 'v, 'w) t;
      (** Returns the unique node with the given (already canonical) view. *)
  leaf_zero : ('f, 'v, 'w) t Lazy.t;
  leaf_one : ('f, 'v, 'w) t Lazy.t;
  add_cache : (Pair_key.t, ('f, 'v, 'w) t) Hashtbl.t;
  seq_cache : (Pair_key.t, ('f, 'v, 'w) t) Hashtbl.t;
  star_cache : (Pair_key.t, ('f, 'v, 'w) t) Hashtbl.t;
  field_cache : (int, 'f list * 'f list) Hashtbl.t;
  mutable optimizations : optimizations;
}
