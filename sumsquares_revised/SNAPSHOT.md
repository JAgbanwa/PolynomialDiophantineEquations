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
lake build             # builds the single module RequestProject
```

`lake build` builds the only default target declared in `lakefile.toml`, namely
`RequestProject`, which consists of the single file `RequestProject.lean`.

## Verification

```sh
./verify.sh
```

`verify.sh` performs a full build, checks that no `sorry`, `admit`, user-declared `axiom`
or `@[implemented_by]` occurs in the source, that the file elaborates with no errors and
no warnings, and prints the axiom dependencies of every
top-level result listed in `comparator.json`.

## State of the snapshot

* Full build succeeds.
* No `sorry` / `admit` anywhere in the source.
* The file elaborates with no errors and no warnings.
* No `axiom` declaration and no `@[implemented_by]` attribute is introduced.
* Every main theorem depends only on the standard axioms
  `propext`, `Classical.choice`, `Quot.sound`.

## Layout

```
RequestProject.lean       the complete formalization (namespaces PolyQF, PolyQF.Main,
                          Challenge, Solution)
comparator.json           machine-readable list of the formalized names
formalization.yaml        paper ↔ Lean correspondence
verify.sh                 build and soundness checks
```
