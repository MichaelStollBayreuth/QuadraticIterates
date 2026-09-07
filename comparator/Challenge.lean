module

public import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements, with `sorry` proofs, of the main results for verification with
[leanprover/comparator](https://github.com/leanprover/comparator): the three cases of the paper's
Section 3 main result (`section3_main` in `QuadraticIterates/ArchMath1992/`), one challenge per
case, the theorems of Li extending it (`li2021_theorem_3_9`, `li2020_theorem_3_5` and, in its
strengthened form `nonempty_mulEquiv_of_eq_neg_mul`, Theorem 3.3 of 2021; all in
`QuadraticIterates/Li/`), and the two theorems extending it to rational parameters `a = r/s`
(Theorems R⁺ and R⁻ of `QuadraticIterates/Rational/Main.lean`, with the 2-adic classes and the
squarefree-level certificates spelled out).

This file imports **only Mathlib**: the three non-Mathlib definitions the statement refers to
(`QuadraticIterates.iteratedPoly`, `.GaloisGroup`, `.WreathPower`) are reproduced here from the
library — under their library names, and with the library's local notation `fℚ[a, n]` spelled out —
so the challenge does not depend on the repository being formalized. The Galois group is defined
for a rational parameter, as in the library (which also treats rational `a = r/s`); the integer
parameters of the challenges are cast to `ℚ`. Comparator compares the full definition bodies (not
just types) between challenge and solution, so a solution that alters any of these definitions is
rejected. The companion `Solution.lean` discharges the `sorry`s with the library theorems.
-/

@[expose] public section

namespace QuadraticIterates

/-- The iterates `f_n` of `f = X² + a` over a commutative (semi)ring `R`: `f_0 = X`,
`f_{n+1} = f_n² + a`. Over `ℤ` (`R := ℤ`) this is the sequence of the paper. -/
noncomputable def iteratedPoly {R : Type*} [CommSemiring R] (a : R) : ℕ → Polynomial R
  | 0 => Polynomial.X
  | n + 1 => (iteratedPoly a n) ^ 2 + Polynomial.C a

/-- The Galois group `Ω_n = Gal(f_n/ℚ)` of the `n`-th iterate of `X² + a`, `a ∈ ℚ`, via Mathlib's
`Polynomial.Gal`. -/
noncomputable abbrev GaloisGroup (a : ℚ) (n : ℕ) : Type :=
  (iteratedPoly a n).Gal

/-- The `n`-fold iterated regular wreath product `[C_2]^n` of `C_2 = Multiplicative (ZMod 2)`, via
Mathlib's `IteratedWreathProduct`. -/
abbrev WreathPower (n : ℕ) : Type :=
  IteratedWreathProduct (Multiplicative (ZMod 2)) n

end QuadraticIterates

open QuadraticIterates

/-- Section 3 main result (`section3_main`), case a): if `a > 0` and `a ≡ 1 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_one (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 1) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case b): if `a > 0` and `a ≡ 2 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_two (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 2) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case c): if `a < 0`, `a ≡ 0 mod 4` and `-a` is not a
square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_neg_emod_four_eq_zero (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) : ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- For `a = -(4k+2)(4k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` (`nonempty_mulEquiv_of_eq_neg_mul`);
Theorem 3.3 of H.-C. Li, Arch. Math. 117 (2021), is the case of even `k`, `a = -(8k+2)(8k+3)`. -/
theorem challenge_nonempty_mulEquiv_of_eq_neg_mul (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup ((-((4 * k + 2) * (4 * k + 3)) : ℤ) : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.9 of H.-C. Li, Arch. Math. 117 (2021) (`li2021_theorem_3_9`): for
`a = -((4k+1)(4k+2)+1)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_li2021_theorem_3_9 (k : ℕ) :
    ∀ n ≥ 1,
      Nonempty (GaloisGroup ((-((4 * k + 1) * (4 * k + 2) + 1) : ℤ) : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.5 of H.-C. Li, Arch. Math. 114 (2020) (`li2020_theorem_3_5`): for `a < 0` with
`a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` if and only if `-a - 1` is not
a square. -/
theorem challenge_li2020_theorem_3_5 (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  sorry

/-- **Theorem R⁺** (`nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCert`), the
extension of the Section 3 main result to a rational parameter `a = r/s > -1` (`s > 0`, `r` and
`s` coprime): if `-rs` is not a square, `(r, s)` lies in one of the 2-adic classes (`s` odd with
`r ≡ 1 mod 4` or `r + s ≡ 3 mod 4`, or `s` even with `r ≡ 3 mod 4`), and one of the four
squarefree-level certificates holds — a divisor `M` of `s` modulo which `r` is not a square; a
divisor `M` of `r + 2s` modulo which `-s` is not a square; `s` even with `r ≡ 3 mod 4` and
`r + s ≢ 1 mod 8`; or `r + s` not a square with a divisor `M` of `r + s` modulo which `s` is not
a square — then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCert (r s : ℤ)
    (hs : 0 < s) (hrs : IsCoprime r s) (hr : -s < r) (hsq : ¬IsSquare (-(r * s)))
    (hc : (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + 2 * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + s) % 8 ≠ 1) ∨
          (¬IsSquare (r + s) ∧
            ∃ M : ℕ, (M : ℤ) ∣ r + s ∧ ¬IsSquare (s : ZMod M))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  sorry

/-- **Theorem R⁻** (`nonempty_mulEquiv_of_two_mul_le_neg_of_twoAdicClass_of_squarefreeCert`), the
extension of the Section 3 main result to a rational parameter `a = -R/s ≤ -2` (`R, s > 0`
coprime): if `Rs` is not a square, `(R, s)` lies in one of the 2-adic classes (`s` odd with
`R ≡ 1 mod 4` or `R - s ≡ 3 mod 4`, or `s` even with `R ≡ 3 mod 4`), and one of the four
squarefree-level certificates holds — a divisor `M` of `s` modulo which `R` is not a square; a
divisor `M` of `R` modulo which `-s` is not a square; `s` even with `R ≡ 3 mod 4` and
`R - s ≢ 1 mod 8`; or `R - s` not a square with a divisor `M` of `R - s` modulo which `-s` is not
a square — then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_nonempty_mulEquiv_of_two_mul_le_neg_of_twoAdicClass_of_squarefreeCert (R s : ℤ)
    (hs : 0 < s) (hRs : IsCoprime R s) (hR : 2 * s ≤ R) (hsq : ¬IsSquare (R * s))
    (hc : (s % 2 = 1 ∧ (R % 4 = 1 ∨ (R - s) % 4 = 3)) ∨ (s % 2 = 0 ∧ R % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧
            ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-R / s : ℚ) n ≃* WreathPower n) :=
  sorry
