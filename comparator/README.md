# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs" — certify that this repository proves the paper's **Section 3 main result**
(`section3_main`), independently of the repository's own build and using only the permitted axioms.

## What is checked

- [`Challenge.lean`](Challenge.lean) imports **only Mathlib**. It reproduces from the library the
  three non-Mathlib definitions the statement mentions — `iteratedPoly`, `GaloisGroup`,
  `WreathPower`, under their library names in the `QuadraticIterates` namespace — and states the
  result with a `sorry` proof. Because it depends on nothing in this repository, it is a
  self-contained specification of the claim.
- [`Solution.lean`](Solution.lean) imports `QuadraticIterates` and proves that statement via the
  library theorem `QuadraticIterates.section3_main`.

Comparator builds both modules (the solution in a sandbox), exports them with `lean4export`, and
checks that `challenge_section3_main` in the solution:

1. proves the **same statement** as in the challenge — comparing the full bodies (not just the
   types) of every definition the statement transitively refers to, so a solution that redefines
   `iteratedPoly`, `GaloisGroup` or `WreathPower` is rejected;
2. uses no axioms beyond `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`);
3. is accepted by the Lean kernel.

`WreathPower` is a thin wrapper around Mathlib's `IteratedWreathProduct`, and `GaloisGroup` around
Mathlib's `Polynomial.Gal`, so reproducing the three definitions pulls in only Mathlib.

## Config

[`section3_main.json`](section3_main.json) — theorem `challenge_section3_main`.

## Running

Prerequisites (see the Comparator README): a built `comparator` binary, plus `landrun` and
`lean4export` on `PATH` (or pointed to by `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT`).

Run from the **repository root** (Comparator uses the current directory as the project and invokes
`lake build Challenge` / `lake build Solution` there):

```bash
lake exe cache get           # trusted Mathlib oleans, optional
lake build QuadraticIterates # so the Solution build reuses the library oleans
# For the strongest sandbox guarantee, run under systemd-run as in the Comparator README:
lake env /path/to/comparator comparator/section3_main.json
```

Exit code `0` means the check passed.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry` in
`Challenge.lean` never enters the library build.
