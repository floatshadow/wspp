# OCaml Clippy-style Semgrep pack

The rule files mirror Clippy's broad lint groups:

- `correctness.yml`: high-confidence bugs; these block commits.
- `suspicious.yml`: partial APIs and exception-handling hazards.
- `perf.yml`: needless traversals, allocation, and stack growth.
- `complexity.yml`: redundant or unnecessarily indirect code.
- `pedantic.yml`: this project's Core, PPrint, and error-message conventions.
- `restriction.yml`: unsafe, deprecated, and trust-boundary APIs.

The starting points are Semgrep's
[community OCaml rules](https://github.com/semgrep/semgrep-rules/tree/develop/ocaml/lang)
and the additional OCaml checks in
[Semgrep's own configuration](https://github.com/semgrep/semgrep/blob/develop/semgrep.yml),
adapted for this project's Core and PPrint conventions.

Run every rule with:

```sh
semgrep scan --config semgrep/ .
```

The partial-API rules check explicit `Stdlib.Hashtbl.find` and
`Stdlib.List.{hd,tl,find,nth}` calls. Unqualified `Hashtbl` and `List` follow this
project's Core convention; Core and Base return options from these operations.
The rules do not diagnose unqualified Stdlib calls in files that omit Core.

Run the rules' regression cases with:

```sh
semgrep --test --config semgrep/suspicious.yml semgrep/tests/suspicious.ml
semgrep --test --config semgrep/restriction.yml semgrep/tests/restriction.ml
```

`ocaml.restriction.poly-equal` rejects `Poly.equal`, including `Core.Poly.equal`,
`Base.Poly.equal`, and uses as a function value. Use type-specific equality
(such as `String.equal` or `[@@deriving equal]`) or pattern matching.

The pre-commit hook runs only `ERROR` rules so legacy advisory findings do not
block unrelated commits. Suppress an intentional match with a nearby
`(* nosemgrep: rule.id *)` comment and explain the invariant.
