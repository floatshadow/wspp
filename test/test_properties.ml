(** Randomized and regression checks of wSPPs against the brute-force semantics, run for several
    semirings. *)

open! Core
open Wspp_rational

(* Two fields, constants {0, 1, 2}, and two fresh values: 25 packets. *)
let small = Reference.{ num_fields = 2; num_constants = 3; num_values = 5 }

(* Two fields, constants {0, ..., 4}, and two fresh values: 49 packets. *)
let regression = Reference.{ num_fields = 2; num_constants = 5; num_values = 7 }

(* Three fields, constants {0, 1}, and two fresh values: 64 packets. *)
let wide = Reference.{ num_fields = 3; num_constants = 2; num_values = 4 }

let run (type w) (module W : Wspp.Semiring.S with type t = w) ~name ~(weights : w list) ~count
    ~canonicity_count =
  let module R = Reference.Make (W) in
  let man = Wspp.Man.create (module Int) (module Int) (module W) in
  let failures =
    R.check_policies man regression (R.regression_policies ~weights)
    + R.check_semantics man small ~weights ~count ~depth:4 ~seed:1
    + R.check_semantics man wide ~weights ~count:(count / 2) ~depth:4 ~seed:2
    + R.check_canonicity man small ~weights ~count:canonicity_count ~depth:3 ~seed:3
  in
  print_endline [%string "%{name}: %{failures#Int} failures"]

let%expect_test "boolean" =
  run
    (module Wspp.Semiring.Bool)
    ~name:"bool" ~weights:[ true; false ] ~count:300 ~canonicity_count:100;
  [%expect {| bool: 0 failures |}]

let%expect_test "probability (exact)" =
  run
    (module Prob)
    ~name:"prob"
    ~weights:Prob.[ of_ints 1 2; of_ints 1 3; of_ints 1 4; one; of_ints 2 1 ]
    ~count:300 ~canonicity_count:100;
  [%expect {| prob: 0 failures |}]

let%expect_test "tropical" =
  let open Wspp.Semiring in
  run
    (module Tropical)
    ~name:"tropical"
    ~weights:(List.map [ 0; 1; 2; 5 ] ~f:Tropical.of_int)
    ~count:300 ~canonicity_count:100;
  [%expect {| tropical: 0 failures |}]

let%expect_test "arctic" =
  let open Wspp.Semiring in
  run
    (module Arctic)
    ~name:"arctic"
    ~weights:Int_ext.[ Fin (-1); Fin 0; Fin 2; Neg_inf ]
    ~count:300 ~canonicity_count:100;
  [%expect {| arctic: 0 failures |}]

let%expect_test "counting" =
  let open Wspp.Semiring in
  run
    (module Counting)
    ~name:"counting"
    ~weights:(List.map [ 0; 1; 2; 3 ] ~f:Counting.of_int)
    ~count:300 ~canonicity_count:100;
  [%expect {| counting: 0 failures |}]

let%expect_test "failure rates" =
  run
    (module Prob_union)
    ~name:"prob-union"
    ~weights:Prob_union.[ of_ints 1 2; of_ints 1 10; one; zero ]
    ~count:300 ~canonicity_count:100;
  [%expect {| prob-union: 0 failures |}]

let%expect_test "product of probability and tropical" =
  let module T = Wspp.Semiring.Tropical in
  run
    (module Wspp.Semiring.Product (Prob) (T))
    ~name:"product"
    ~weights:
      [ (Prob.of_ints 1 2, T.of_int 1); (Prob.of_ints 1 3, T.of_int 0); (Prob.one, T.of_int 4) ]
    ~count:200 ~canonicity_count:60;
  [%expect {| product: 0 failures |}]

(* Trace-carrying frontiers are not commutative, which exercises the multiplication order. *)
module Cost = Wspp.Pareto.Pair (Wspp.Pareto.Latency) (Wspp.Pareto.Bandwidth)
module Trace_frontier = Wspp.Pareto.Frontier (Wspp.Pareto.Trace (Cost) (String))

let traced l b trace = ((Wspp.Pareto.Latency.of_int l, Wspp.Pareto.Bandwidth.of_int b), trace)

let%expect_test "trace-carrying Pareto frontiers" =
  run
    (module Trace_frontier)
    ~name:"trace-frontier"
    ~weights:
      (List.map ~f:Trace_frontier.of_list
         [
           [ traced 1 5 [ "a" ] ];
           [ traced 2 9 [ "b" ] ];
           [ traced 0 3 [ "c" ] ];
           [ traced 3 7 [] ];
           [ traced 1 2 [ "d" ]; traced 4 8 [ "e" ] ];
         ])
    ~count:150 ~canonicity_count:50;
  [%expect {| trace-frontier: 0 failures |}]
