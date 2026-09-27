(** Packet fields and field values.

    Any totally ordered, hashable, sexp-printable type is a key; Core's [Int] and [String] qualify
    directly. For fields, [compare] fixes the order in which a wSPP reads them (smaller fields
    closer to the root).

    NOTE: value domains are unbounded, as in the paper: a node's defaults stand for "every value not
    mentioned explicitly". This is what makes the canonical form unique. *)

open! Core

module type S = sig
  type t [@@deriving compare, equal, hash, sexp_of]
end
