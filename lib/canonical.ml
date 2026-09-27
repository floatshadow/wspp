(** Leaves, the canonicalizing smart constructor [mk] (Appendix B.6), atoms, and the branch maps of
    nodes (Appendix B.1). Every node is built by [mk] and interned, so semantically equivalent wSPPs
    are the same node (Theorem 6.1). *)

open! Core
open Types

let zero man = Lazy.force man.leaf_zero
let one man = Lazy.force man.leaf_one
let leaf man w = man.intern (Leaf w)
let equal a b = a.id = b.id
let is_zero t = equal t (zero t.man)
let is_one t = equal t (one t.man)

let root_field t = match t.view with Leaf _ -> None | Node n -> Some n.field

let check_same_man op x y =
  if x.man.uid <> y.man.uid then
    failwith [%string "Wspp.%{op}: the operands belong to different managers"]

let memoize tbl key compute =
  match Hashtbl.find tbl key with
  | Some v -> v
  | None ->
      let v = compute () in
      Hashtbl.set tbl ~key ~data:v;
      v

(** The branch of a node at an input value [u] that no explicit row mentions. *)
let default_branch man ~defaults ~identity u =
  if is_zero identity || Row.mem man.value defaults u then defaults
  else Row.set man.value defaults u identity

let equal_row man r1 r2 = Row.equal man.value ~equal_data:equal r1 r2

(** [mk man field branches defaults identity] is the canonical node with the read-back semantics of
    the raw node [wspp(field, branches, defaults, identity)]. [branches] and [defaults] must be
    sorted and every child may only mention fields greater than [field]. *)
let mk man field branches defaults identity =
  let nonzero c = not (is_zero c) in
  (* Phase 1: a dead default [v ↦ 0] still shadows the identity at [v]. Before deleting it,
     freeze the behavior at input [v] in an explicit row (unless one exists). *)
  let live_defaults = Row.filter defaults ~f:nonzero in
  let branches =
    if List.length live_defaults = List.length defaults then branches
    else
      List.fold defaults ~init:branches ~f:(fun branches (v, c) ->
          if nonzero c || Row.mem man.value branches v then branches
          else Row.set man.value branches v defaults)
  in
  (* Phase 2 prunes zeros inside rows; phase 3 drops rows the defaults reproduce anyway. *)
  let branches =
    List.filter_map branches ~f:(fun (u, r) ->
        let r = Row.filter r ~f:nonzero in
        if equal_row man r (default_branch man ~defaults:live_defaults ~identity u) then None
        else Some (u, r))
  in
  (* Phase 4: collapse trivial nodes. *)
  if List.is_empty branches && List.is_empty live_defaults then identity
  else man.intern (Node { field; branches; defaults = live_defaults; identity })

(* ------------------------------------------------------------------------------------------ *)
(* Atoms (Section 4.3)                                                                        *)
(* ------------------------------------------------------------------------------------------ *)

let test man f v = mk man f [ (v, [ (v, one man) ]) ] [] (zero man)
let test_neq man f v = mk man f [ (v, []) ] [] (one man)
let assign man f v = mk man f [] [ (v, one man) ] (zero man)

(** The product of the tests [f ≠ x] for all [x] in the sorted list [xs]. *)
let test_neq_all man f xs = mk man f (List.map xs ~f:(fun x -> (x, []))) [] (one man)

(* ------------------------------------------------------------------------------------------ *)
(* Lifting and branch maps                                                                    *)
(* ------------------------------------------------------------------------------------------ *)

type ('f, 'v, 'w) components = {
  branches : ('v * ('f, 'v, 'w) row) list;
  defaults : ('f, 'v, 'w) row;
  identity : ('f, 'v, 'w) Types.t;
}

(** The components of [t] viewed as a node on [field]: a leaf or a node on a greater field is lifted
    to [wspp(field, ∅, ∅, t)], which has the same read-back. *)
let components field t =
  match t.view with
  | Node n when t.man.field.equal n.field field ->
      { branches = n.branches; defaults = n.defaults; identity = n.identity }
  | Leaf _ | Node _ -> { branches = []; defaults = []; identity = t }

(** The branch of the node [c] at input value [u]. *)
let branch man c u =
  match Row.find man.value c.branches u with
  | Some r -> r
  | None -> default_branch man ~defaults:c.defaults ~identity:c.identity u

(** [branches_at man c us] is [List.map us ~f:(branch man c)] for sorted [us], computed in one pass
    over the explicit rows instead of one lookup per value. *)
let branches_at man c us =
  let rec go acc us rows =
    match (us, rows) with
    | [], _ -> List.rev acc
    | u :: us', [] ->
        go (default_branch man ~defaults:c.defaults ~identity:c.identity u :: acc) us' []
    | u :: us', (u', r) :: rows' ->
        let cmp = man.value.compare u u' in
        if cmp > 0 then go acc us rows'
        else if cmp = 0 then go (r :: acc) us' rows'
        else go (default_branch man ~defaults:c.defaults ~identity:c.identity u :: acc) us' rows
  in
  go [] us c.branches

(** The smaller root field of two wSPPs, at least one of which is a node. *)
let top_field x y =
  match (root_field x, root_field y) with
  | Some f, Some g -> if x.man.field.compare f g <= 0 then f else g
  | Some f, None | None, Some f -> f
  | None, None -> failwith "Wspp.top_field: both operands are leaves"
