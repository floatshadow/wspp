(** Weighting, choice and sequential composition of wSPPs (Section 4.3, Appendices B.3-B.5). *)

open! Core
open Types
open Canonical

(* ------------------------------------------------------------------------------------------ *)
(* Weighting                                                                                  *)
(* ------------------------------------------------------------------------------------------ *)

(** Applies [f] to every leaf weight, keeping the tree shape (up to canonicalization). *)
let map_leaves t ~f =
  let man = t.man in
  let memo = Hashtbl.create (module Int) in
  let rec go t =
    match t.view with
    | Leaf w -> leaf man (f w)
    | Node n ->
        memoize memo t.id (fun () ->
            let go_row r = Row.map r ~f:go in
            mk man n.field (Row.map n.branches ~f:go_row) (go_row n.defaults) (go n.identity))
  in
  go t

(** [scale w t] is [w ⊙ t]: multiplies every leaf from the left. *)
let scale w t =
  let s = t.man.weight in
  if s.equal w s.one then t else if s.equal w s.zero then zero t.man else map_leaves t ~f:(s.mul w)

(** [scale_right t w] is [t ; (w ⊙ skip)]: multiplies every leaf from the right. *)
let scale_right t w =
  let s = t.man.weight in
  if s.equal w s.one then t
  else if s.equal w s.zero then zero t.man
  else map_leaves t ~f:(fun a -> s.mul a w)

(* ------------------------------------------------------------------------------------------ *)
(* Choice                                                                                     *)
(* ------------------------------------------------------------------------------------------ *)

let rec add x y =
  check_same_man "add" x y;
  if is_zero x then y
  else if is_zero y then x
  else
    match (x.view, y.view) with
    | Leaf a, Leaf b -> leaf x.man (x.man.weight.add a b)
    | (Leaf _ | Node _), _ ->
        (* Choice is commutative, so both argument orders share a cache entry. *)
        let key = if x.id <= y.id then (x.id, y.id) else (y.id, x.id) in
        memoize x.man.add_cache key (fun () -> add_nodes x y)

and add_nodes x y =
  let man = x.man in
  let field = top_field x y in
  let cx = components field x and cy = components field y in
  let us =
    Row.union_keys man.value
      [ Row.keys cx.branches; Row.keys cy.branches; Row.keys cx.defaults; Row.keys cy.defaults ]
  in
  let branches =
    List.map3_exn us (branches_at man cx us) (branches_at man cy us) ~f:(fun u r1 r2 ->
        (u, add_row man r1 r2))
  in
  mk man field branches (add_row man cx.defaults cy.defaults) (add cx.identity cy.identity)

and add_row man r1 r2 = Row.merge man.value ~both:add r1 r2

(* ------------------------------------------------------------------------------------------ *)
(* Sequential composition                                                                     *)
(* ------------------------------------------------------------------------------------------ *)

let rec seq x y =
  check_same_man "seq" x y;
  if is_zero x || is_zero y then zero x.man
  else if is_one x then y
  else if is_one y then x
  else
    match (x.view, y.view) with
    | Leaf a, Leaf b -> leaf x.man (x.man.weight.mul a b)
    | Leaf a, Node _ -> scale a y
    | Node _, Leaf b -> scale_right x b
    | Node _, Node _ -> memoize x.man.seq_cache (x.id, y.id) (fun () -> seq_nodes x y)

and seq_nodes x y =
  let man = x.man in
  let field = top_field x y in
  let cx = components field x and cy = components field y in
  (* [compose r] is [r ⊲ y]: route every output value [v] of [r] into the branch of [y] reading
     [v] (the symbolic matrix product), summing entries for equal final values. *)
  let compose r =
    let targets = Row.keys r in
    List.fold2_exn r (branches_at man cy targets) ~init:[] ~f:(fun acc (_, tau) into ->
        add_row man acc (Row.map into ~f:(seq tau)))
  in
  let m_a = compose cx.defaults in
  (* With a zero identity these entries would all be zero; they only shadow a zero identity. *)
  let m_b = if is_zero cx.identity then [] else Row.map cy.defaults ~f:(seq cx.identity) in
  let us =
    Row.union_keys man.value
      [
        Row.keys cx.branches;
        Row.keys cy.branches;
        Row.keys cx.defaults;
        Row.keys cy.defaults;
        Row.keys m_a;
      ]
  in
  let branches = List.map2_exn us (branches_at man cx us) ~f:(fun u r -> (u, compose r)) in
  mk man field branches (add_row man m_a m_b) (seq cx.identity cy.identity)

let sum man ts = List.fold ts ~init:(zero man) ~f:add
let product man ts = List.fold (List.rev ts) ~init:(one man) ~f:(fun acc t -> seq t acc)
