(** Finite maps from values to ['a], as association lists sorted by value without duplicate keys.
    Used for rows ([value ↦ continuation]) and for the test-assignment maps of nodes. *)

open! Core
open Types

type ('v, 'a) t = ('v * 'a) list

let find (key : 'v key) (r : ('v, 'a) t) v =
  let rec go = function
    | [] -> None
    | (u, x) :: rest ->
        let c = key.compare u v in
        if c = 0 then Some x else if c > 0 then None else go rest
  in
  go r

let mem key r v = Option.is_some (find key r v)
let keys (r : ('v, 'a) t) = List.map r ~f:fst
let map (r : ('v, 'a) t) ~f = List.map r ~f:(fun (v, x) -> (v, f x))
let filter (r : ('v, 'a) t) ~f = List.filter r ~f:(fun (_, x) -> f x)

(* Sets [v] to [f (find v)], removing the entry when [f] returns [None]. *)
let change (key : 'v key) (r : ('v, 'a) t) v ~f =
  let rec go acc = function
    | [] -> finish acc (f None) []
    | ((u, x) as entry) :: rest ->
        let c = key.compare u v in
        if c < 0 then go (entry :: acc) rest
        else if c = 0 then finish acc (f (Some x)) rest
        else finish acc (f None) (entry :: rest)
  and finish acc result rest =
    match result with
    | None -> List.rev_append acc rest
    | Some x -> List.rev_append acc ((v, x) :: rest)
  in
  go [] r

let set key r v x = change key r v ~f:(fun _ -> Some x)
let remove key r v = change key r v ~f:(fun _ -> None)

(** Union of two maps; values present on both sides are combined with [both]. *)
let merge (key : 'v key) ~both (r1 : ('v, 'a) t) (r2 : ('v, 'a) t) =
  let rec go acc r1 r2 =
    match (r1, r2) with
    | [], rest | rest, [] -> List.rev_append acc rest
    | ((u1, x1) as e1) :: tl1, ((u2, x2) as e2) :: tl2 ->
        let c = key.compare u1 u2 in
        if c < 0 then go (e1 :: acc) tl1 r2
        else if c > 0 then go (e2 :: acc) r1 tl2
        else go ((u1, both x1 x2) :: acc) tl1 tl2
  in
  go [] r1 r2

(** Sorted union of sorted key lists. *)
let union_keys (key : 'v key) (ks : 'v list list) =
  List.fold ks ~init:[] ~f:(fun acc k ->
      merge key ~both:(fun () () -> ()) acc (List.map k ~f:(fun v -> (v, ()))))
  |> keys

let equal (key : 'v key) ~equal_data (r1 : ('v, 'a) t) (r2 : ('v, 'a) t) =
  List.equal (fun (u1, x1) (u2, x2) -> key.equal u1 u2 && equal_data x1 x2) r1 r2
