open Core

(* ruleid: ocaml.suspicious.partial-hashtbl-find *)
let stdlib_find table key = Stdlib.Hashtbl.find table key

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let core_find table key = Hashtbl.find table key

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let qualified_core_find table key = Core.Hashtbl.find table key

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let base_find table key = Base.Hashtbl.find table key

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let optional_find table key = Stdlib.Hashtbl.find_opt table key

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let handled_find table key = try Stdlib.Hashtbl.find table key with Not_found -> 0

(* ok: ocaml.suspicious.partial-hashtbl-find *)
let explicit_find table key = Hashtbl.find_exn table key

(* ruleid: ocaml.suspicious.partial-list-head-or-tail *)
let stdlib_head xs = Stdlib.List.hd xs

(* ruleid: ocaml.suspicious.partial-list-head-or-tail *)
let stdlib_tail xs = Stdlib.List.tl xs

(* ok: ocaml.suspicious.partial-list-head-or-tail *)
let core_head xs = List.hd xs

(* ok: ocaml.suspicious.partial-list-head-or-tail *)
let core_tail xs = List.tl xs

(* ok: ocaml.suspicious.partial-list-head-or-tail *)
let qualified_core_head xs = Core.List.hd xs

(* ok: ocaml.suspicious.partial-list-head-or-tail *)
let base_tail xs = Base.List.tl xs

(* ruleid: ocaml.suspicious.partial-list-find *)
let stdlib_list_find xs f = Stdlib.List.find f xs

(* ok: ocaml.suspicious.partial-list-find *)
let core_list_find xs f = List.find xs ~f

(* ok: ocaml.suspicious.partial-list-find *)
let base_list_find xs f = Base.List.find xs ~f

(* ok: ocaml.suspicious.partial-list-find *)
let optional_list_find xs f = Stdlib.List.find_opt f xs

(* ok: ocaml.suspicious.partial-list-find *)
let handled_list_find xs f = try Stdlib.List.find f xs with Not_found -> 0

(* ruleid: ocaml.suspicious.partial-list-nth *)
let stdlib_nth xs index = Stdlib.List.nth xs index

(* ok: ocaml.suspicious.partial-list-nth *)
let core_nth xs index = List.nth xs index

(* ok: ocaml.suspicious.partial-list-nth *)
let qualified_core_nth xs index = Core.List.nth xs index

(* ok: ocaml.suspicious.partial-list-nth *)
let base_nth xs index = Base.List.nth xs index

(* ok: ocaml.suspicious.partial-list-nth *)
let optional_nth xs index = Stdlib.List.nth_opt xs index
