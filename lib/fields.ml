(** Field analysis behind the untested-field decomposition of Section 6.1.

    A field [g] is input-independent in a wSPP if every node on [g] has the form [wspp(g, ∅, m, 0)]:
    it always overwrites [g] and never reads its input value. *)

open! Core
open Types
open Canonical

(* Field sets are small, so they are sorted lists without duplicates. *)
let union (key : 'f key) a b =
  let rec go acc a b =
    match (a, b) with
    | [], rest | rest, [] -> List.rev_append acc rest
    | x :: a', y :: b' ->
        let c = key.compare x y in
        if c < 0 then go (x :: acc) a' b
        else if c > 0 then go (y :: acc) a b'
        else go (x :: acc) a' b'
  in
  go [] a b

(* For each node: the fields it mentions, and the fields whose input value some node reads
   (through explicit rows or the default identity). Cached per node in the manager. *)
let rec info t =
  match t.view with
  | Leaf _ -> ([], [])
  | Node n ->
      memoize t.man.field_cache t.id (fun () ->
          let key = t.man.field in
          let reads_input = not (List.is_empty n.branches && is_zero n.identity) in
          let visit (mentioned, read) c =
            let mentioned', read' = info c in
            (union key mentioned mentioned', union key read read')
          in
          let acc = visit ([ n.field ], if reads_input then [ n.field ] else []) n.identity in
          let acc = List.fold n.defaults ~init:acc ~f:(fun acc (_, c) -> visit acc c) in
          List.fold n.branches ~init:acc ~f:(fun acc (_, r) ->
              List.fold r ~init:acc ~f:(fun acc (_, c) -> visit acc c)))

(** Fields mentioned by [t], in increasing order. *)
let fields t = fst (info t)

(** The least input-independent field of [t], if any. *)
let input_independent_field t =
  let mentioned, read = info t in
  List.find mentioned ~f:(fun f -> not (List.mem read f ~equal:t.man.field.equal))

(** [split_on g t] is [(keep, write)] where [keep] has the paths of [t] that leave [g] untouched and
    [write] those that assign [g], so [t ≡ keep ⊕ write]. Exact, because the read-back is linear in
    each child. *)
let split_on g t =
  let man = t.man in
  let memo = Hashtbl.create (module Int) in
  let rec go t =
    match t.view with
    | Leaf _ -> (t, zero man)
    | Node n ->
        let c = man.field.compare n.field g in
        if c > 0 then (t, zero man)
        else if c = 0 then (zero man, t)
        else
          memoize memo t.id (fun () ->
              let go_row r =
                let parts = Row.map r ~f:go in
                (Row.map parts ~f:fst, Row.map parts ~f:snd)
              in
              let rows = Row.map n.branches ~f:go_row in
              let keep_m, write_m = go_row n.defaults in
              let keep_d, write_d = go n.identity in
              ( mk man n.field (Row.map rows ~f:fst) keep_m keep_d,
                mk man n.field (Row.map rows ~f:snd) write_m write_d ))
  in
  go t

(** Replaces every node [wspp(g, ∅, m, 0)] by [⊕_v m(v)], forgetting the value written to the
    input-independent field [g]. *)
let erase g t =
  let man = t.man in
  let memo = Hashtbl.create (module Int) in
  let rec go t =
    match t.view with
    | Leaf _ -> t
    | Node n ->
        let c = man.field.compare n.field g in
        if c > 0 then t
        else if c = 0 then
          (* By choice of [g], this node has no explicit rows and a zero identity. *)
          Algebra.sum man (List.map n.defaults ~f:snd)
        else
          memoize memo t.id (fun () ->
              let go_row r = Row.map r ~f:go in
              mk man n.field (Row.map n.branches ~f:go_row) (go_row n.defaults) (go n.identity))
  in
  go t
