(** Scalability benchmarks: time to build the wSPP of a looping policy as the network grows, under
    each combination of the Section 6.1 optimizations. *)

open! Core
open Wspp_rational

let settings =
  List.concat_map [ true; false ] ~f:(fun untested_field_decomposition ->
      List.map [ true; false ] ~f:(fun trailing_star ->
          { Wspp.untested_field_decomposition; trailing_star }))

let string_of_setting (o : Wspp.optimizations) =
  (if o.untested_field_decomposition then "decomp" else "------")
  ^ "+"
  ^ if o.trailing_star then "trail" else "-----"

let time f =
  let start = Time_float.now () in
  let result = f () in
  (result, Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) start))

(* A ring of [n] switches: a packet at switch [i] heading to [dst ≠ i] moves to a neighbor,
   clockwise with weight [cw] and counter-clockwise with weight [ccw], and optionally records the
   last hop in the write-only local variable [hop]. The query runs the walk until arrival. *)
let ring man ~n ~cw ~ccw ~local =
  let open Wspp in
  let step i =
    let move j w =
      let arrive = assign man "sw" (j % n) in
      scale w (if local then seq (assign man "hop" i) arrive else arrive)
    in
    product man [ test man "sw" i; test_neq man "dst" i; add (move (i + 1) cw) (move (i - 1) ccw) ]
  in
  let body = sum man (List.init n ~f:step) in
  let arrived = sum man (List.init n ~f:(fun i -> seq (test man "sw" i) (test man "dst" i))) in
  let cleanup = if local then assign man "hop" 0 else one man in
  (body, seq arrived cleanup)

let run (type w) ~name (module W : Wspp.Semiring.S with type t = w) ~(cw : w) ~(ccw : w) ~sizes
    ~local =
  List.iter sizes ~f:(fun n ->
      List.iter settings ~f:(fun o ->
          let man = Wspp.Man.create ~optimizations:o (module String) (module Int) (module W) in
          let body, query = ring man ~n ~cw ~ccw ~local in
          let result, seconds = time (fun () -> Wspp.star_then body query) in
          printf "%-22s n=%-4d %s  %8.3fs  size %d\n%!" name n (string_of_setting o) seconds
            (Wspp.size result)))

let () =
  let sizes = [ 16; 32; 64; 128 ] in
  run ~name:"ring/prob"
    (module Prob)
    ~cw:(Prob.of_ints 1 2) ~ccw:(Prob.of_ints 1 2) ~sizes ~local:false;
  run ~name:"ring/prob+local"
    (module Prob)
    ~cw:(Prob.of_ints 1 2) ~ccw:(Prob.of_ints 1 2) ~sizes ~local:true;
  run ~name:"ring/bool" (module Wspp.Semiring.Bool) ~cw:true ~ccw:false ~sizes ~local:false;
  run ~name:"ring/bool+local" (module Wspp.Semiring.Bool) ~cw:true ~ccw:false ~sizes ~local:true
