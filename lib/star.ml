(** Kleene star of wSPPs: symbolic state elimination (Section 4.4, Figure 9) together with the
    untested-field decomposition and the trailing-policy optimization of Section 6.1. *)

open! Core
open Types
open Canonical
open Algebra

let rec star t = star_then t (one t.man)

(** [star_then p q = p* ; q]. With the trailing-star optimization, [q] is multiplied into the
    factors of [p*] from the right, so the large product [p*] is never built on its own. *)
and star_then p q =
  check_same_man "star_then" p q;
  let man = p.man in
  if (not man.optimizations.trailing_star) && not (is_one q) then seq (star p) q
  else if is_zero p || is_zero q then q
  else
    match p.view with
    | Leaf w -> scale (man.weight.star w) q
    | Node _ -> memoize man.star_cache (p.id, q.id) (fun () -> star_node p q)

and star_node p q =
  let decompose_on =
    if p.man.optimizations.untested_field_decomposition then Fields.input_independent_field p
    else None
  in
  match decompose_on with
  | Some g ->
      (* With p ≡ keep ⊕ write: p* ; q ≡ keep* ; q ⊕ (keep ⊕ erase write)* ; write ; keep* ; q.
         Inside the middle star every write to [g] is overwritten by the trailing [write] and
         nothing reads [g], so those writes can be erased. Erasing is also what makes this
         terminate: both stars lose the field [g], while [(keep ⊕ write)*] would decompose on
         [g] again forever. *)
      let keep, write = Fields.split_on g p in
      let keep_then_q = star_then keep q in
      add keep_then_q (star_then (add keep (Fields.erase g write)) (seq write keep_then_q))
  | None -> eliminate p q

(* State elimination on the root field of [p], returning [p* ; q]. Each removal emits a factor,
   left ([psi], in reverse) or right ([phi]); [p* = ψ1 ; ... ; ψk ; φl ; ... ; φ1]. *)
and eliminate p q =
  let man = p.man in
  let key = man.value in
  let f, branches, defaults, identity =
    match p.view with
    | Node n -> (n.field, n.branches, n.defaults, n.identity)
    | Leaf _ -> failwith "Wspp.Star.eliminate: expected a node"
  in
  let add_into row v contribution =
    if is_zero contribution then row
    else
      Row.change key row v ~f:(function
        | None -> Some contribution
        | Some old -> Some (add old contribution))
  in
  let factor guard v eta = add (one man) (seq guard (seq (assign man f v) eta)) in
  (* Pass I: remove the default identity. An entry writing a value that no row or default
     mentions can continue through the identity, so it absorbs [identity*]. *)
  let branches, psi =
    if is_zero identity then (branches, [])
    else
      let star_d = star identity in
      let named v = Row.mem key branches v || Row.mem key defaults v in
      let absorb (v, s) = (v, if named v then s else seq s star_d) in
      let branches = Row.map branches ~f:(List.map ~f:absorb) in
      let guard =
        test_neq_all man f (Row.union_keys key [ Row.keys branches; Row.keys defaults ])
      in
      (branches, [ add (one man) (seq guard (seq identity star_d)) ])
  in
  (* Pass II: remove the explicit entries row by row. Emptied rows stay as markers so that the
     defaults never fill them in. An update only adds entries to rows that have an entry into
     the removed value, so an emptied row is never refilled and every row is visited once.

     NOTE: Figure 9 removes one entry at a time, self-loop first, emitting one factor each. We
     remove a whole row [u] at once, which is the same computation with the algebra done
     eagerly: with [S = σ_uu*] the row's factors multiply out to the single factor
     [1 ⊕ (f = u) ; (f ← u ; S ⊕ Σ_v f ← v ; S ; σ_uv)], and the updates of the other rows
     compose to one splice. This keeps the number of factors linear in the number of rows
     rather than in the number of entries, which dominates the cost of the final product. *)
  let clear_row (branches, defaults, psi) u =
    match Row.find key branches u with
    | None | Some [] -> (branches, defaults, psi)
    | Some r ->
        let loop = Option.value_map (Row.find key r u) ~default:(one man) ~f:star in
        (* After looping at [u], leave through each remaining entry. *)
        let exits = Row.map (Row.remove key r u) ~f:(seq loop) in
        let branches = Row.set key branches u [] in
        (* A step into [u] may now loop there and stay, or loop and leave through an exit. *)
        let splice row =
          match Row.find key row u with
          | None -> row
          | Some into_u ->
              List.fold exits
                ~init:(Row.set key row u (seq into_u loop))
                ~f:(fun row (v, exit) -> add_into row v (seq into_u exit))
        in
        let factor = mk man f [ (u, Row.set key exits u loop) ] [] (one man) in
        (Row.map branches ~f:splice, splice defaults, factor :: psi)
  in
  let branches, defaults, psi =
    List.fold (Row.keys branches) ~init:(branches, defaults, psi) ~f:clear_row
  in
  (* Pass III: remove the default assignments column by column; these factors go right. *)
  let guard = test_neq_all man f (Row.keys branches) in
  let rec clear_defaults defaults phi =
    match defaults with
    | [] -> phi
    | (z, sigma) :: rest ->
        if Row.mem key branches z then clear_defaults rest (factor guard z sigma :: phi)
        else
          (* Writing [z] re-enters the default rows, so the column can loop. *)
          let star_sigma = star sigma in
          clear_defaults
            (Row.map rest ~f:(seq star_sigma))
            (factor guard z (seq sigma star_sigma) :: phi)
  in
  let phi = clear_defaults defaults [] in
  (* [ψ1 ; ... ; ψk ; φl ; ... ; φ1 ; q], multiplied from the right. *)
  List.fold (List.rev_append phi psi) ~init:q ~f:(fun acc factor -> seq factor acc)
