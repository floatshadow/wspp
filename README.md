# wspp

An OCaml implementation of **weighted symbolic packet programs** (wSPPs) from
Lu et al., *A Fast Quantitative Analyzer for NetKAT* ([arXiv:2607.14420](https://arxiv.org/abs/2607.14420)).
wSPPs generalize the SPPs of KATch ([arXiv:2404.04760](https://arxiv.org/abs/2404.04760)) from Boolean to
semiring weights.

A wSPP symbolically represents a weighted relation on *packets*: finite maps from fields to values drawn
from unbounded domains. Compared to ADDs, which branch on Boolean variables, a wSPP node branches on the
*value* of a field and can rewrite it, with a default case standing for "all other values". Operations
are choice (`⊕`, pointwise sum), sequential composition (`;`, matrix product), weighting, and Kleene star,
over any star semiring.

## Usage

The API follows Core's `Map`: create a *manager* once from first-class modules; every wSPP carries its
manager, so operations take no module arguments.

```ocaml
let man = Wspp.Man.create (module String) (module Int) (module Wspp_rational.Prob)

let walk =
  let open Wspp in
  let half = Wspp_rational.Prob.of_ints 1 2 in
  sum man
    [ seq (test man "sw" 0) (scale half (assign man "sw" 1));
      seq (test man "sw" 0) (scale half (assign man "sw" 2)) ]

let reach_2 = Wspp.star_then walk (Wspp.test man "sw" 2)   (* walk* ; sw = 2 *)

let p = Wspp.eval reach_2 ~fields:[ "sw" ] ~input:(fun _ -> 0) ~output:(fun _ -> 2)  (* 1/2 *)
```

- Fields and values: any module with `[@@deriving compare, equal, hash, sexp_of]` (`Int`, `String`, your
  own variants). Field `compare` fixes the order in which wSPPs read fields.
- `Wspp.equal` is semantic equivalence, in constant time (wSPPs are canonical and hash-consed).
- `Wspp.view` exposes the node structure for your own traversals; `Wspp.Policy` is a small
  dup-free weighted NetKAT AST, compiled by `Wspp.of_policy`.

## Semirings

A weight module implements `Wspp.Semiring.S`: `zero`, `one`, `add`, `mul` (not necessarily
commutative), `star`, and `[@@deriving equal, hash, sexp_of]`. `star a` must equal `1 + a + a² + …` in
an ω-continuous semiring the weights embed into (Definition 4.3). Included:

| Module | Semiring | Use |
| --- | --- | --- |
| `Semiring.Bool` | `({0,1}, ∨, ∧)` | reachability (= KATch SPPs) |
| `Semiring.Tropical` | `(N ∪ {∞}, min, +)` | latency |
| `Semiring.Arctic` | `(Z ∪ {±∞}, max, +)` | worst-case cost |
| `Semiring.Bottleneck` | `(Z ∪ {±∞}, max, min)` | bandwidth |
| `Semiring.Counting` | `(N ∪ {∞}, +, ·)` | path counting |
| `Semiring.Float_prob` | `([0, ∞], +, ·)` | fast, approximate probabilities |
| `Semiring.Lattice (L)` | `(L, ∨, ∧)` | security levels, any bounded lattice |
| `Semiring.Product (A) (B)` | componentwise | several analyses at once |
| `Wspp_rational.Prob` | `(Q≥0 ∪ {∞}, +, ·)` | exact probabilities / expectations |
| `Wspp_rational.Viterbi` | `([0,1] ∩ Q, max, ·)` | most reliable path |
| `Wspp_rational.Prob_union` | `(max, a+b−ab)` | failure rates |
| `Pareto.Frontier (T)` | Pareto frontiers (§5.1) | multi-objective trade-offs |
| `Pareto.Frontier (Pareto.Trace (T) (Event))` | trace-carrying frontiers (§5.2) | trade-offs with witnesses |

`Pareto.Latency`, `Pareto.Bandwidth` and `Pareto.Pair` build cost vectors for the frontier semirings.

## Implementation map

| Module | Contents |
| --- | --- |
| `lib/wspp.ml` | public facade (sealed signature) |
| `lib/types.ml` | node and manager representation |
| `lib/man.ml` | managers: weak hash-consing table, memo caches, optimization switches |
| `lib/canonical.ml` | canonicalizing smart constructor `mk` (App. B.6), atoms, branch maps |
| `lib/algebra.ml` | weighting, `⊕`, `;` (App. B.3–B.5) |
| `lib/star.ml` | three-pass star elimination (Fig. 9) + trailing-star and decomposition (§6.1) |
| `lib/fields.ml` | input-independent field analysis, split and erase (§6.1) |
| `lib/inspect.ml`, `lib/policy.ml` | `eval` (Cor. 4.13), printing; policy AST and compiler |

Optimizations: canonical form + hash-consing (so equality is `id` comparison), memoized `⊕`/`;`/star
(`⊕` keyed up to commutativity), zero/one short-circuits, untested-field decomposition, and star with a
trailing policy. The last two can be toggled per manager (`Man.set_optimizations`) for ablation.
Managers are not domain-safe.

## Performance notes

- **Field order matters**, as for BDDs: `compare` on fields decides which field each node reads. Put
  fields that change often (locations) before fields that are mostly tested (destinations). On the ring
  benchmark, reading `sw` before `dst` is 6–10× faster than the reverse (n = 64 / 128).
- Pass II of the star removes one **row** at a time rather than one entry (Figure 9). The algebra is the
  same, but the number of emitted factors is linear in the rows, not the entries: ~100× faster on a
  256-switch random walk.
- Prefer `star_then p q` (or `Policy.Seq (Star p, q)`) over `seq (star p) q` when `q` is selective.
- `bench/bench.exe` (release profile, one core; decomposition on / off, trailing star on):

  | workload | n=64 | n=128 |
  | --- | --- | --- |
  | ring random walk, exact `Prob` | 1.1 s | 17 s |
  | ring + write-only local variable, `Prob` | 1.1 s / 8.7 s | 16 s / 164 s |
  | ring + local variable, `Bool` | 0.7 s / 2.9 s | 12 s / — |

## Building and testing

Requires OCaml ≥ 5.0 with `core`, `ppx_jane`, `pprint`, `zarith` (the `5.4.0` opam switch has them):

```sh
opam exec --switch=5.4.0 -- dune test          # expect tests
opam exec --switch=5.4.0 -- dune exec bench/bench.exe
```

`test/test_paper.ml` reproduces the paper's worked examples (Ex. 2.1, Figs. 1–3, §2.5, Ex. 4.8, Ex. 5.7).
`test/test_properties.ml` checks random and hand-picked policies against a brute-force matrix semantics
(with Lehmann's matrix star) for eight semirings, including a non-commutative one, under every
optimization setting, and checks semiring/Kleene laws as identities of canonical nodes.
