(** Weighted symbolic packet programs (wSPPs) over arbitrary star semirings, after Lu et al., "A
    Fast Quantitative Analyzer for NetKAT" (arXiv 2607.14420).

    A wSPP of type [('f, 'v, 'w) t] symbolically represents a weighted relation on packets, maps
    from fields ['f] to values ['v], with weights ['w] from a star semiring. As with Core's [Map],
    the operations need no module arguments: every wSPP carries its manager, created once from
    first-class modules:

    {[
    let man = Wspp.Man.create (module Int) (module Int) (module Wspp.Semiring.Bool) in
    let p = Wspp.seq (Wspp.test man 0 1) (Wspp.assign man 1 2) in
    Wspp.star p
    ]}

    Wspps are hash-consed and canonical: two wSPPs of the same manager are semantically equivalent
    iff [equal] (a constant-time id comparison). *)

open! Core
module Key = Key
module Semiring = Semiring
module Pareto = Pareto

include (
  struct
    type optimizations = Types.optimizations = {
      untested_field_decomposition : bool;
      trailing_star : bool;
    }
    [@@deriving sexp_of]

    type ('f, 'v, 'w) t = ('f, 'v, 'w) Types.t
    type ('f, 'v, 'w) row = ('f, 'v, 'w) Types.row

    type ('f, 'v, 'w) view = ('f, 'v, 'w) Types.view =
      | Leaf of 'w
      | Node of {
          field : 'f;
          branches : ('v * ('f, 'v, 'w) row) list;
          defaults : ('f, 'v, 'w) row;
          identity : ('f, 'v, 'w) t;
        }

    module Man = Man
    module Policy = Policy

    let manager (t : _ t) = t.man
    let view (t : _ t) = t.view
    let id (t : _ t) = t.id
    let equal = Canonical.equal
    let compare (a : _ t) (b : _ t) = Int.compare a.id b.id
    let hash (t : _ t) = t.hkey
    let zero = Canonical.zero
    let one = Canonical.one
    let weight = Canonical.leaf
    let test = Canonical.test
    let test_neq = Canonical.test_neq
    let assign = Canonical.assign
    let add = Algebra.add
    let seq = Algebra.seq
    let scale = Algebra.scale
    let scale_right = Algebra.scale_right
    let sum = Algebra.sum
    let product = Algebra.product
    let star = Star.star
    let star_then = Star.star_then
    let of_policy = Policy.compile
    let eval = Inspect.eval
    let size = Inspect.size
    let fields = Fields.fields
    let pp = Inspect.pp
  end :
    sig
      type optimizations = {
        untested_field_decomposition : bool;
            (** Split off a field whose input value is irrelevant before eliminating a star. *)
        trailing_star : bool;  (** Fold the policy after a star into the star's right factors. *)
      }
      [@@deriving sexp_of]
      (** Switches for the algorithmic optimizations of Section 6.1. Canonicalization, hash-consing
          and memoization are always on. *)

      type ('f, 'v, 'w) t
      (** A wSPP; see the module documentation. *)

      type ('f, 'v, 'w) row = ('v * ('f, 'v, 'w) t) list
      (** A row maps output values to continuations; sorted by value, without duplicate keys. *)

      (** The shape of a wSPP: a weighted leaf [w] (output the input packet with weight [w]), or a
          node [wspp(f, b, m, d)] reading field [f]. On input value [u] a node takes the row [b(u)]
          if [u] is an explicit row, else the default assignments [m] together with [u ↦ d] unless
          [m] mentions [u] or [d = 0]. Children only mention fields greater than [f]. *)
      type ('f, 'v, 'w) view =
        | Leaf of 'w
        | Node of {
            field : 'f;
            branches : ('v * ('f, 'v, 'w) row) list;  (** Sorted by input value. *)
            defaults : ('f, 'v, 'w) row;
            identity : ('f, 'v, 'w) t;
          }

      (** Managers own the hash-consing table and memoization caches of wSPPs over fixed field,
          value and weight types. They are not safe to share between domains. *)
      module Man : sig
        type ('f, 'v, 'w) t

        val create :
          ?optimizations:optimizations ->
          (module Key.S with type t = 'f) ->
          (module Key.S with type t = 'v) ->
          (module Semiring.S with type t = 'w) ->
          ('f, 'v, 'w) t

        val clear_caches : ('f, 'v, 'w) t -> unit
        (** Drops the memoization caches; interned wSPPs and [equal] are unaffected. *)

        val optimizations : ('f, 'v, 'w) t -> optimizations
        val set_optimizations : ('f, 'v, 'w) t -> optimizations -> unit
      end

      (** Dup-free weighted NetKAT policies (Figure 5), compiled by [of_policy]. *)
      module Policy : sig
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
      end

      val manager : ('f, 'v, 'w) t -> ('f, 'v, 'w) Man.t
      (** The manager that interned the wSPP. *)

      val view : ('f, 'v, 'w) t -> ('f, 'v, 'w) view

      val id : ('f, 'v, 'w) t -> int
      (** Unique among all wSPPs alive in the program. *)

      val equal : ('f, 'v, 'w) t -> ('f, 'v, 'w) t -> bool
      (** Semantic equivalence, in constant time. *)

      val compare : ('f, 'v, 'w) t -> ('f, 'v, 'w) t -> int
      val hash : ('f, 'v, 'w) t -> int

      (** {1 Constants and atoms} *)

      val zero : ('f, 'v, 'w) Man.t -> ('f, 'v, 'w) t
      (** [drop], the constant-0 relation. *)

      val one : ('f, 'v, 'w) Man.t -> ('f, 'v, 'w) t
      (** [skip], the identity relation with weight 1. *)

      val weight : ('f, 'v, 'w) Man.t -> 'w -> ('f, 'v, 'w) t
      (** [weight man w] is [w ⊙ skip]. *)

      val test : ('f, 'v, 'w) Man.t -> 'f -> 'v -> ('f, 'v, 'w) t
      (** [test man f v] is the test [f = v]. *)

      val test_neq : ('f, 'v, 'w) Man.t -> 'f -> 'v -> ('f, 'v, 'w) t
      (** [test_neq man f v] is the test [f ≠ v]. *)

      val assign : ('f, 'v, 'w) Man.t -> 'f -> 'v -> ('f, 'v, 'w) t
      (** [assign man f v] is the assignment [f ← v]. *)

      (** {1 Operations}

          Binary operations raise if their operands belong to different managers. *)

      val add : ('f, 'v, 'w) t -> ('f, 'v, 'w) t -> ('f, 'v, 'w) t
      (** Choice [p ⊕ q]: the pointwise sum of weighted relations. *)

      val seq : ('f, 'v, 'w) t -> ('f, 'v, 'w) t -> ('f, 'v, 'w) t
      (** Sequential composition [p ; q]: the matrix product. *)

      val scale : 'w -> ('f, 'v, 'w) t -> ('f, 'v, 'w) t
      (** [scale w p] is [w ⊙ p]: multiplies every weight by [w] from the left. *)

      val scale_right : ('f, 'v, 'w) t -> 'w -> ('f, 'v, 'w) t
      (** [scale_right p w] is [p ; (w ⊙ skip)]: multiplies every weight by [w] from the right. *)

      val sum : ('f, 'v, 'w) Man.t -> ('f, 'v, 'w) t list -> ('f, 'v, 'w) t
      val product : ('f, 'v, 'w) Man.t -> ('f, 'v, 'w) t list -> ('f, 'v, 'w) t

      val star : ('f, 'v, 'w) t -> ('f, 'v, 'w) t
      (** Kleene star [p*] (Figure 9). *)

      val star_then : ('f, 'v, 'w) t -> ('f, 'v, 'w) t -> ('f, 'v, 'w) t
      (** [star_then p q] is [p* ; q], computed with the trailing-policy optimization. *)

      val of_policy : ('f, 'v, 'w) Man.t -> ('f, 'v, 'w) Policy.t -> ('f, 'v, 'w) t
      (** Compiles a policy; [Seq (Star p, q)] uses [star_then]. *)

      (** {1 Inspection} *)

      val eval : ('f, 'v, 'w) t -> fields:'f list -> input:('f -> 'v) -> output:('f -> 'v) -> 'w
      (** [eval p ~fields ~input ~output] is the weight [⟦p⟧(α)(β)] (Corollary 4.13) where [input f]
          and [output f] are the values of field [f] in [α] and [β]. [fields] must contain every
          field on which [α] and [β] may differ. *)

      val size : ('f, 'v, 'w) t -> int
      (** Number of distinct nodes (leaves included) reachable from the wSPP. *)

      val fields : ('f, 'v, 'w) t -> 'f list
      (** Fields mentioned by the wSPP, in increasing order. *)

      val pp : ('f, 'v, 'w) t -> PPrint.document
      (** Prints the wSPP as a tree; shared subterms are printed repeatedly. *)
    end)
