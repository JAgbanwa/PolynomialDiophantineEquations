# Snapshot

Reproduction information for this formalization.

## Toolchain

| Component | Version / revision |
|---|---|
| Lean 4 | `leanprover/lean4:v4.28.0` (see `lean-toolchain`) |
| Mathlib | tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Build tool | `lake` (bundled with the toolchain) |

The exact revisions of all transitive dependencies (`batteries`, `aesop`, `Qq`,
`proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, `Cli`) are pinned in
`lake-manifest.json`; do not regenerate that file if you want a bit-for-bit reproduction.

## Building

```sh
lake exe cache get     # optional, fetches prebuilt Mathlib olean files
lake build             # builds RequestProject, Challenge and Solution
```

`lake build` builds the three default targets declared in `lakefile.toml`: `RequestProject`
(the development), `Challenge` (self-contained statements of the main results) and `Solution`
(their proofs).

## Verification

```sh
./verify.sh
```

`verify.sh` performs a full build, checks that no `sorry`, `admit`, user-declared `axiom`
or `@[implemented_by]` occurs in the sources, that no `native_decide` is used, that every
file elaborates with no errors and no warnings, and prints the axiom dependencies of every
top-level result listed in `comparator.json`.

## State of the snapshot

* Full build succeeds.
* No `sorry` / `admit` anywhere in the source.
* All three files elaborate with no errors and no warnings.
* No `axiom` declaration and no `@[implemented_by]` attribute is introduced.
* Every main theorem depends only on the standard axioms
  `propext`, `Classical.choice`, `Quot.sound`.

## Layout

```
RequestProject.lean       the development (namespaces PolyQF and PolyQF.Main)
Challenge.lean            self-contained statements of the main results (namespace Challenge)
Solution.lean             proofs of every Challenge statement (namespace Solution)
comparator.json           machine-readable list of the formalized names
formalization.yaml        paper ↔ Lean correspondence, and responses to the referee report
verify.sh                 build and soundness checks
lean-toolchain            leanprover/lean4:v4.28.0
lake-manifest.json        pinned revisions of Mathlib and its dependencies
```
