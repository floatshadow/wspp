open Core

(* ruleid: ocaml.restriction.poly-equal *)
let direct lhs rhs = Poly.equal lhs rhs

(* ruleid: ocaml.restriction.poly-equal *)
let qualified_core lhs rhs = Core.Poly.equal lhs rhs

(* ruleid: ocaml.restriction.poly-equal *)
let qualified_base lhs rhs = Base.Poly.equal lhs rhs

(* ruleid: ocaml.restriction.poly-equal *)
let equality = Poly.equal

(* ruleid: ocaml.restriction.poly-equal *)
let partial lhs = Poly.equal lhs

(* ruleid: ocaml.restriction.poly-equal *)
let lists lhs rhs = List.equal Poly.equal lhs rhs

(* ok: ocaml.restriction.poly-equal *)
let strings lhs rhs = String.equal lhs rhs

(* ok: ocaml.restriction.poly-equal *)
let integers lhs rhs = Int.equal lhs rhs

(* ok: ocaml.restriction.poly-equal *)
let typed_lists lhs rhs = List.equal String.equal lhs rhs

(* ok: ocaml.restriction.poly-equal *)
let description = "Poly.equal is forbidden"
