# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs" — certify that this repository proves the paper's **Section 3 main result** (`section3_main`, one
challenge per case), the **theorems of Li** extending it (`li2021_theorem_3_9`,
`li2020_theorem_3_5`, and Theorem 3.3 of 2021 in its strengthened form
`nonempty_mulEquiv_of_eq_neg_mul`, for `a = -(4k+2)(4k+3)` rather than Li's `a = -(8k+2)(8k+3)`)
and the **rational-parameter theorems R⁺ and R⁻** (`QuadraticIterates/Rational/Main.lean`, with
the 2-adic classes and the squarefree-level certificates spelled out as disjunctions),
independently of the repository's own build and using only the permitted axioms.

## What is checked

- [`Challenge.lean`](Challenge.lean) imports **only Mathlib**. It reproduces from the library the
  three non-Mathlib definitions the statement mentions — `iteratedPoly`, `GaloisGroup`,
  `WreathPower`, under their library names in the `QuadraticIterates` namespace — and states the
  results with `sorry` proofs. Because it depends on nothing in this repository, it is a
  self-contained specification of the claims.
- [`Solution.lean`](Solution.lean) imports `QuadraticIterates` and proves each statement via the
  corresponding library theorem.

Comparator builds both modules (the solution in a sandbox), exports them with `lean4export`, and
checks that each challenge theorem in the solution:

1. proves the **same statement** as in the challenge — comparing the full bodies (not just the
   types) of every definition the statement transitively refers to, so a solution that redefines
   `iteratedPoly`, `GaloisGroup` or `WreathPower` is rejected;
2. uses no axioms beyond `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`);
3. is accepted by the Lean kernel.

`WreathPower` is a thin wrapper around Mathlib's `IteratedWreathProduct`, and `GaloisGroup` around
Mathlib's `Polynomial.Gal`, so reproducing the three definitions pulls in only Mathlib.

## Config

[`challenges.json`](challenges.json) — the eight challenge theorems: the three cases of the
Section 3 main result (`a > 0`, `a ≡ 1 mod 4`; `a > 0`, `a ≡ 2 mod 4`; `a < 0`, `a ≡ 0 mod 4`,
`-a` not a square), Li's Theorems 3.9 (2021) and 3.5 (2020), Theorem 3.3 (2021) strengthened to
`a = -(4k+2)(4k+3)`, and Theorems R⁺ (`a = r/s > -1`) and R⁻ (`a = -R/s ≤ -2`) for rational
parameters.

## Running

Prerequisites (see the Comparator README): a built `comparator` binary, plus `landrun` and
`lean4export` on `PATH` (or pointed to by `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT`).

Run from the **repository root** (Comparator uses the current directory as the project and invokes
`lake build Challenge` / `lake build Solution` there):

```bash
lake exe cache get           # trusted Mathlib oleans, optional
lake build QuadraticIterates # so the Solution build reuses the library oleans
# For the strongest sandbox guarantee, run under systemd-run as in the Comparator README:
lake env /path/to/comparator comparator/challenges.json
```

Exit code `0` and the line `Your solution is okay!` mean the check passed.
[`scripts/run-comparator.sh`](../scripts/run-comparator.sh) wraps the last two steps: it locates
the three binaries (override with `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN`;
`lean4export` must be built at this project's Lean version), builds the library, and runs the
check on `comparator/challenges.json` or on the config given as its argument.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry`s in
`Challenge.lean` never enter the library build.
