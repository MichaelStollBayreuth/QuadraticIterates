module

public import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements, with `sorry` proofs, of the main results for verification with
[leanprover/comparator](https://github.com/leanprover/comparator): the three cases of the paper's
Section 3 main result (`section3_main` in `QuadraticIterates/ArchMath1992/`), one challenge per
case, and the theorems of Li extending it (`li2021_theorem_3_9`, `li2020_theorem_3_5` and, in its
strengthened form `nonempty_mulEquiv_of_eq_neg_mul`, Theorem 3.3 of 2021; all in
`QuadraticIterates/Li/`).

This file imports **only Mathlib**: the three non-Mathlib definitions the statement refers to
(`QuadraticIterates.iteratedPoly`, `.GaloisGroup`, `.WreathPower`) are reproduced here from the
library — under their library names, and with the library's local notation `fℚ[a, n]` spelled out —
so the challenge does not depend on the repository being formalized. Comparator compares the full
definition bodies (not just types) between challenge and solution, so a solution that alters any of
these definitions is rejected. The companion `Solution.lean` discharges the `sorry`s with the
library theorems.
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

open QuadraticIterates

/-- Section 3 main result (`section3_main`), case a): if `a > 0` and `a ≡ 1 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_one (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 1) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case b): if `a > 0` and `a ≡ 2 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_two (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 2) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case c): if `a < 0`, `a ≡ 0 mod 4` and `-a` is not a
square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_neg_emod_four_eq_zero (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  sorry

/-- For `a = -(4k+2)(4k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` (`nonempty_mulEquiv_of_eq_neg_mul`);
Theorem 3.3 of H.-C. Li, Arch. Math. 117 (2021), is the case of even `k`, `a = -(8k+2)(8k+3)`. -/
theorem challenge_nonempty_mulEquiv_of_eq_neg_mul (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-((4 * k + 2) * (4 * k + 3))) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.9 of H.-C. Li, Arch. Math. 117 (2021) (`li2021_theorem_3_9`): for
`a = -((4k+1)(4k+2)+1)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_li2021_theorem_3_9 (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-((4 * k + 1) * (4 * k + 2) + 1)) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.5 of H.-C. Li, Arch. Math. 114 (2020) (`li2020_theorem_3_5`): for `a < 0` with
`a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` if and only if `-a - 1` is not
a square. -/
theorem challenge_li2020_theorem_3_5 (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  sorry
