(** Managers: the per-instance state of wSPPs over fixed field, value and weight types, i.e. the
    hash-consing table and the memoization caches (Section 6).

    NOTE: managers are not safe to share between domains. *)

open! Core
open Types

type ('f, 'v, 'w) t = ('f, 'v, 'w) man

let default_optimizations = { untested_field_decomposition = true; trailing_star = true }

(* Node ids come from one counter shared by all managers, so ids never collide across
   managers. *)
let next_id = ref 0
let next_uid = ref 0

let key_of_module (type a) (module K : Key.S with type t = a) : a key =
  { compare = K.compare; equal = K.equal; hash = K.hash; sexp_of = K.sexp_of_t }

let semiring_of_module (type w) (module W : Semiring.S with type t = w) : w semiring =
  {
    zero = W.zero;
    one = W.one;
    add = W.add;
    mul = W.mul;
    star = W.star;
    equal = W.equal;
    hash = W.hash;
    sexp_of = W.sexp_of_t;
  }

let combine h x = ((h * 65599) + x) land Int.max_value

let create (type f v w) ?(optimizations = default_optimizations)
    (field_module : (module Key.S with type t = f)) (value_module : (module Key.S with type t = v))
    (weight_module : (module Semiring.S with type t = w)) : (f, v, w) t =
  let field = key_of_module field_module in
  let value = key_of_module value_module in
  let weight = semiring_of_module weight_module in
  (* Children are compared by id: they are already interned. *)
  let equal_row r1 r2 =
    List.equal (fun (v1, c1) (v2, c2) -> value.equal v1 v2 && c1.id = c2.id) r1 r2
  in
  let equal_view a b =
    match (a, b) with
    | Leaf x, Leaf y -> weight.equal x y
    | Node n1, Node n2 ->
        field.equal n1.field n2.field && n1.identity.id = n2.identity.id
        && equal_row n1.defaults n2.defaults
        && List.equal
             (fun (u1, r1) (u2, r2) -> value.equal u1 u2 && equal_row r1 r2)
             n1.branches n2.branches
    | Leaf _, Node _ | Node _, Leaf _ -> false
  in
  let hash_row h r =
    List.fold r ~init:(combine h 17) ~f:(fun h (v, c) -> combine (combine h (value.hash v)) c.id)
  in
  let hash_view = function
    | Leaf w -> combine 1 (weight.hash w)
    | Node n ->
        let h = hash_row (combine (combine 2 (field.hash n.field)) n.identity.id) n.defaults in
        List.fold n.branches ~init:h ~f:(fun h (u, r) -> hash_row (combine h (value.hash u)) r)
  in
  (* A weak table: unreachable nodes can be collected. *)
  let module Table = Stdlib.Weak.Make (struct
    type t = (f, v, w) Types.t

    let equal a b = equal_view a.view b.view
    let hash t = t.hkey
  end) in
  let table = Table.create 4096 in
  let add_cache = Hashtbl.create (module Pair_key) in
  let seq_cache = Hashtbl.create (module Pair_key) in
  let star_cache = Hashtbl.create (module Pair_key) in
  let field_cache = Hashtbl.create (module Int) in
  incr next_uid;
  let uid = !next_uid in
  let rec man =
    {
      uid;
      field;
      value;
      weight;
      intern;
      leaf_zero = lazy (intern (Leaf weight.zero));
      leaf_one = lazy (intern (Leaf weight.one));
      add_cache;
      seq_cache;
      star_cache;
      field_cache;
      optimizations;
    }
  and intern view =
    let probe = { id = -1; hkey = hash_view view; man; view } in
    match Table.find_opt table probe with
    | Some t -> t
    | None ->
        let t = { probe with id = !next_id } in
        incr next_id;
        Table.add table t;
        t
  in
  man

(** Drops all memoization caches. Interned nodes are unaffected, so equality stays valid. *)
let clear_caches man =
  List.iter [ man.add_cache; man.seq_cache; man.star_cache ] ~f:Hashtbl.clear;
  Hashtbl.clear man.field_cache

let optimizations man = man.optimizations

let set_optimizations man optimizations =
  (* Results agree up to canonical form under every setting; clearing the caches keeps
     measurements of an individual setting honest. *)
  clear_caches man;
  man.optimizations <- optimizations
