# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` since Lean v4.35.0 — certify that this
repository proves the paper's **Section 3 main result** (`section3_main`, one challenge per case),
the **theorems of Li** extending it (`li2021_theorem_3_9`, `li2020_theorem_3_5`, and Theorem 3.3 of
2021 in its strengthened form `nonempty_mulEquiv_of_eq_neg_mul`, for `a = -(4k+2)(4k+3)` rather than
Li's `a = -(8k+2)(8k+3)`) and the **main theorem for rational parameters**
(`nonempty_mulEquiv_of_twoAdicClass_of_criteria`, with its `2`-adic classes and three lists of
criteria reproduced as definitions) with its two corollaries — **level two decides** outside the
interval `α < a ≤ a_*` (`forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`) and shorter
lists of criteria on the interval `α < a < -1` (`nonempty_mulEquiv_of_lt_neg_one_of_criteria`) —
independently of the repository's own build and using only the permitted axioms.

## What is checked

- [`Challenge.lean`](Challenge.lean) imports **only Mathlib**. It reproduces from the library the
  non-Mathlib definitions the statements mention — `iteratedPoly`, `GaloisGroup`, `WreathPower`,
  for the main theorem `NegAllCriterion`, `NegFirstCriterion`, `NegTailCriterion` and
  `TwoAdicClass`, and for the second corollary `NegFirstCriterion'` and `NegTailCriterion'`, under
  their library names in the `QuadraticIterates` namespace — and states the
  results with `sorry` proofs. Because it depends on nothing in this repository, it is a
  self-contained specification of the claims.
- [`Solution.lean`](Solution.lean) imports `QuadraticIterates` and proves each statement via the
  corresponding library theorem.

`lake comparator` builds and exports both modules inside a `bubblewrap` sandbox (it never loads
the project's `.olean`s into its own process) and checks that each challenge theorem in the
solution:

1. proves the **same statement** as in the challenge — comparing the full bodies (not just the
   types) of every definition the statement transitively refers to, so a solution that redefines
   `iteratedPoly`, `GaloisGroup` or `WreathPower` is rejected;
2. uses no axioms beyond `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`);
3. is accepted by the Lean kernel.

`WreathPower` is a thin wrapper around Mathlib's `IteratedWreathProduct`, and `GaloisGroup` around
Mathlib's `Polynomial.Gal`, so reproducing the three definitions pulls in only Mathlib.

## Config

[`challenges.json`](challenges.json) — the nine challenge theorems: the three cases of the
Section 3 main result (`a > 0`, `a ≡ 1 mod 4`; `a > 0`, `a ≡ 2 mod 4`; `a < 0`, `a ≡ 0 mod 4`,
`-a` not a square), Li's Theorems 3.9 (2021) and 3.5 (2020), Theorem 3.3 (2021) strengthened to
`a = -(4k+2)(4k+3)`, the main theorem for rational parameters `a = r/s`, and its two corollaries,
where the 2-independence of `c₁ = -a` and `c₂ = a² + a` is spelled out as three non-squares.

## Running

Run from the **repository root**; the only prerequisite besides Lean is `bubblewrap` (`bwrap`)
with unprivileged user namespaces (or installed setuid root):

```bash
scripts/run-comparator.sh               # = lake build QuadraticIterates && lake comparator --config comparator/challenges.json
scripts/run-comparator.sh --paranoid    # also run all external checkers bundled with Lean
```

Exit code `0` (and `Your solution is okay!`) means the check passed, `1` that it was rejected, `2`
that it could not start (no `bwrap`, no `lake-manifest.json`, a malformed configuration). The
wrapper builds the library first: the sandbox cannot write to the project directory, and with a
current build the sandboxed builds only replay it. A different configuration file can be given as
the first argument.

Until 2026-10-15 the check ran on the external tools — a separately built `comparator` binary,
`landrun`, and a `lean4export` built at the project's Lean version — through an earlier version of
the wrapper (see the history of `scripts/run-comparator.sh`); `lake comparator` replaces all three.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry`s in
`Challenge.lean` never enter the library build.
