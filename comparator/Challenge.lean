module

public import Mathlib

/-!
# Comparator challenge statement (Section 3 main result)

A self-contained restatement of the paper's Section 3 main result (`section3_main` in
`QuadraticIterates/ArchMath1992/`), with a `sorry` proof, for verification with
[leanprover/comparator](https://github.com/leanprover/comparator).

This file imports **only Mathlib**: the three non-Mathlib definitions the statement refers to
(`QuadraticIterates.iteratedPoly`, `.GaloisGroup`, `.WreathPower`) are reproduced here from the
library — under their library names, and with the library's local notation `fℚ[a, n]` spelled out —
so the challenge does not depend on the repository being formalized. Comparator compares the full
definition bodies (not just types) between challenge and solution, so a solution that alters any of
these definitions is rejected. The companion `Solution.lean` discharges the `sorry` with the
library theorem.
-/

@[expose] public section

namespace QuadraticIterates

/-- The iterates `f_n` of `f = X² + a` over a commutative (semi)ring `R`: `f_0 = X`,
`f_{n+1} = f_n² + a`. Over `ℤ` (`R := ℤ`) this is the sequence of the paper. -/
noncomputable def iteratedPoly {R : Type*} [CommSemiring R] (a : R) : ℕ → Polynomial R
  | 0 => Polynomial.X
  | n + 1 => (iteratedPoly a n) ^ 2 + Polynomial.C a

/-- The Galois group `Ω_n = Gal(f_n/ℚ)` of the `n`-th iterate, via Mathlib's `Polynomial.Gal`. -/
noncomputable abbrev GaloisGroup (a : ℤ) (n : ℕ) : Type :=
  (iteratedPoly (a : ℚ) n).Gal

/-- The `n`-fold iterated regular wreath product `[C_2]^n` of `C_2 = Multiplicative (ZMod 2)`, via
Mathlib's `IteratedWreathProduct`. -/
abbrev WreathPower (n : ℕ) : Type :=
  IteratedWreathProduct (Multiplicative (ZMod 2)) n

end QuadraticIterates

open QuadraticIterates in
/-- Section 3 main result (`section3_main`): if `a > 0` with `a ≡ 1, 2 mod 4`, or `a < 0`,
`a ≡ 0 mod 4` and `-a` is not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main (a : ℤ)
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  sorry
