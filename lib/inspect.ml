(** Reading weights off wSPPs, size statistics, and printing. *)

open! Core
open Types
open Canonical

(** [eval t ~fields ~input ~output] is [⟦t⟧(α)(β)] (Corollary 4.13), where [input f] and [output f]
    are the values of field [f] in [α] and [β]. [fields] must contain every field on which [α] and
    [β] may differ. *)
let eval t ~fields ~input ~output =
  let man = t.man in
  let rec go t visited =
    match t.view with
    | Leaf w ->
        let agree f =
          List.mem visited f ~equal:man.field.equal || man.value.equal (input f) (output f)
        in
        if List.for_all fields ~f:agree then w else man.weight.zero
    | Node n -> (
        let c = { branches = n.branches; defaults = n.defaults; identity = n.identity } in
        match Row.find man.value (branch man c (input n.field)) (output n.field) with
        | None -> man.weight.zero
        | Some child -> go child (n.field :: visited))
  in
  go t []

(** Number of distinct nodes (leaves included) reachable from [t]. *)
let size t =
  let seen = Hash_set.create (module Int) in
  let rec go t =
    if not (Hash_set.mem seen t.id) then (
      Hash_set.add seen t.id;
      match t.view with
      | Leaf _ -> ()
      | Node n ->
          go n.identity;
          List.iter n.defaults ~f:(fun (_, c) -> go c);
          List.iter n.branches ~f:(fun (_, r) -> List.iter r ~f:(fun (_, c) -> go c)))
  in
  go t;
  Hash_set.length seen

let pp_sexp sexp_of x = PPrint.string (Sexp.to_string (sexp_of x))

(** Prints [t] as a tree [wspp(f, {u ↦ {v ↦ ...}}, {z ↦ ...}, d)]. Shared subterms are printed
    repeatedly. *)
let rec pp t =
  let open PPrint in
  let man = t.man in
  let pp_value = pp_sexp man.value.sexp_of in
  let pp_map pp_data r =
    braces
      (separate_map (comma ^^ break 1) (fun (v, x) -> pp_value v ^^ string " ↦ " ^^ pp_data x) r)
  in
  match t.view with
  | Leaf w -> pp_sexp man.weight.sexp_of w
  | Node n ->
      group
        (string "wspp"
        ^^ parens
             (nest 2
                (separate
                   (comma ^^ break 1)
                   [
                     pp_sexp man.field.sexp_of n.field;
                     pp_map (pp_map pp) n.branches;
                     pp_map pp n.defaults;
                     pp n.identity;
                   ])))
