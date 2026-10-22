/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.TwoIndependent
public import QuadraticIterates.Main.TwoAdic

import QuadraticIterates.Galois.Criterion
import QuadraticIterates.Main.Theorem
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Algebra.Ring.Parity
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Sequence.SquareClasses

/-!
# Level two decides

For `a = r/s` in one of the `2`-adic classes (C1)–(C3) of `QuadraticIterates.TwoAdicClass`, with
`a ≤ -2`, or `a > -1`, or `a < -1` in the window `c_3 < 0 < c_4`, the hypotheses of the main
theorem `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria` hold as soon as
`c_1, c_2` are 2-independent. Modulo squares `c_1 ∼ -rs`, `c_2 ∼ r(r + s)` and
`c_1 c_2 ∼ -s(r + s)`; as a product of two squares is a square, for `r < 0` at most one of `-r`,
`s`, `-(r + s)` is a square, and the other two give two of (Z1), (O3)/(O4) and the criterion (T1),
(T3) or (T4) for `τ`, while for `a > 0` (O1) holds and `r`, `r + s` are not both squares. In the
classes `(r, s) ≡ (1, 1)` with `a > 0` and `(3, 3)` with `a ≤ -2` modulo `4`, (O2) holds, and (Z2)
takes the place of (Z1) when `|r|` is a square. Hence the arboreal representation of `X² + a` is
surjective if and only if `Ω_2 ≅ [C₂]²`.

## Main statements

* `QuadraticIterates.twoIndependent_fin_two_cSeq_iff`: `c_1, c_2` are 2-independent if and only if
  none of `-rs`, `r(r + s)`, `-s(r + s)` is a square.
* `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_not_isSquare`: if none of `-rs`,
  `r(r + s)`, `-s(r + s)` is a square, `Ω_n ≅ [C₂]ⁿ` for every `n`.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass` and
  `QuadraticIterates.forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass`: level two
  decides.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_of_le_neg_two`: Theorem 3.5 of [Li 2020] for
  rational parameters.

## References

* H.-C. Li, *Arboreal Galois representation for a certain type of quadratic polynomials*,
  Arch. Math. **114** (2020), 265-269.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- **Level two in terms of `r` and `s`**: `c_1, c_2` are 2-independent if and only if none of
`-rs`, `r(r + s)` and `-s(r + s)`, the square classes of `c_1`, `c_2` and `c_1 c_2`, is a square.
For `r = 0` or `s = 0` both sides fail, as `c_1 = 0`. -/
theorem twoIndependent_fin_two_cSeq_iff :
    (TwoIndependent fun i : Fin 2 ↦ cSeq ((r : ℚ) / s) ((i : ℕ) + 1)) ↔
      ¬IsSquare (-(r * s)) ∧ ¬IsSquare (r * (r + s)) ∧ ¬IsSquare (-(s * (r + s))) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [twoIndependent_fin_two_iff]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [twoIndependent_fin_two_iff]
  rw [twoIndependent_fin_two_iff]
  exact and_congr (isSquare_cSeq_one_iff hs).not <| and_congr (isSquare_cSeq_two_iff hs).not
    (isSquare_cSeq_one_mul_cSeq_two_iff hr hs).not

/-- (Z2) for `r + 2s ≡ ±3 (mod 8)`. -/
private lemma negAllCriterion_of_emod_eight (h : (r + 2 * s) % 8 = 3 ∨ (r + 2 * s) % 8 = 5) :
    NegAllCriterion r s :=
  let ⟨p, hp, hp8, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_three_or_five h
  .dvd_add_two_mul p hp hp8 hpd

/-- With `r < 0`, two of `-r`, `s`, `-(r + s)` are not squares; they give two of (Z1), (O3)/(O4)
and the criterion for `τ` supplied by `hT`. -/
private lemma criteria_of_not_isSquare (hr : r < 0) (hs : 0 ≤ s)
    (hT : ¬IsSquare (-(r + s)) → NegTailCriterion r s) (h₁ : ¬IsSquare (-(r * s)))
    (h₂ : ¬IsSquare (r * (r + s))) (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hZ (h : ¬IsSquare (-r)) : NegAllCriterion r s := .not_isSquare (not_isSquare_of_neg hr) h
  have hO := negFirstCriterion_of_not_isSquare_right (r := r) hs
  by_cases hr' : IsSquare (-r)
  · exact .inr (.inr ⟨hO fun h ↦ h₁ (neg_mul r s ▸ hr'.mul h),
      hT fun h ↦ h₂ (neg_mul_neg r (r + s) ▸ hr'.mul h)⟩)
  by_cases hs' : IsSquare s
  · exact .inr (.inl ⟨hZ hr', hT fun h ↦ h₁₂ (mul_neg s (r + s) ▸ hs'.mul h)⟩)
  · exact .inl ⟨hZ hr', hO hs'⟩

/-- For `a ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`): (O2), and (Z1), or (Z2) if `|r|` is a square:
`r = t²` gives `r ≡ 1` and `r + 2s ≡ 3 (mod 8)`, `r = -t²` gives `r ≡ 7` and `r + 2s ≡ 5`. -/
private lemma criteria_of_modEq_four (hs : s % 2 = 1) (h4 : r % 4 = s % 4) :
    NegAllCriterion r s ∧ NegFirstCriterion r s := by
  refine ⟨?_, .modEq_four (Int.odd_iff.mpr hs) (by rw [Int.ModEq]; lia)⟩
  by_cases hsq : IsSquare r ∨ IsSquare (-r)
  · refine negAllCriterion_of_emod_eight ?_
    obtain ⟨t, ht⟩ | ⟨t, ht⟩ := hsq <;>
    lia [Int.sq_emod_eight_eq_one_of_odd (x := t) (Int.odd_iff.mpr (by lia [Int.sq_emod_four t]))]
  · push Not at hsq
    exact .not_isSquare hsq.1 hsq.2

/-- For `a > 0`: (O1), and (Z1) if `r ≠ □`; for `r = t²`, (T3) in the classes `(1, 3)` and
`(0, 3)`; the class `(1, 1)` is `QuadraticIterates.criteria_of_modEq_four`. -/
private lemma criteria_of_pos (hs : 0 < s) (hr : 0 < r) (hc : TwoAdicClass r s 1)
    (h₂ : ¬IsSquare (r * (r + s))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  by_cases h11 : r % 4 = 1 ∧ s % 4 = 1
  · exact .inl (criteria_of_modEq_four (by lia) (by lia))
  by_cases hsq : IsSquare r
  swap
  · exact .inl ⟨.not_isSquare hsq (not_isSquare_of_neg (by lia)), .pos hr⟩
  have hns : ¬IsSquare (r + s) := fun h ↦ h₂ (hsq.mul h)
  obtain ⟨t, ht⟩ := hsq
  exact .inr (.inr ⟨.pos hr, negTailCriterion_of_emod_four hns (not_isSquare_of_neg (by lia))
    (by lia [Int.sq_emod_four t, twoAdicClass_one_iff.mp hc])⟩)

/-- For `a ≤ -2`: the classes `(3, 3)` (`QuadraticIterates.criteria_of_modEq_four`) and `(1, 2)`
directly, the others by `QuadraticIterates.criteria_of_not_isSquare` with (T3), as `r + s ≡ 0` or
`1 (mod 4)`. -/
private lemma criteria_of_le_neg_two (hs : 0 < s) (ha : r ≤ -2 * s) (hc : TwoAdicClass r s (-1))
    (h₁ : ¬IsSquare (-(r * s))) (h₂ : ¬IsSquare (r * (r + s)))
    (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hr : r < 0 := by lia
  by_cases h33 : r % 4 = 3 ∧ s % 4 = 3
  · exact .inl (criteria_of_modEq_four (by lia) (by lia))
  by_cases h12 : r % 4 = 1 ∧ s % 4 = 2
  · exact .inl ⟨.not_isSquare (not_isSquare_of_neg hr)
      (Int.not_isSquare_of_two_le_emod_four (by lia)),
      negFirstCriterion_of_not_isSquare_right hs.le (Int.not_isSquare_of_two_le_emod_four (by lia))⟩
  exact criteria_of_not_isSquare hr hs.le (fun h ↦ negTailCriterion_of_emod_four
    (not_isSquare_of_neg (by lia)) h (by lia [twoAdicClass_neg_one_iff.mp hc])) h₁ h₂ h₁₂

/-- For `a > -1`, or `a < -1` in the window `c_3 < 0 < c_4`. -/
private lemma criteria_of_twoAdicClass_one (hs : 0 < s)
    (ha : -s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7)
    (hc : TwoAdicClass r s 1) (h₁ : ¬IsSquare (-(r * s))) (h₂ : ¬IsSquare (r * (r + s)))
    (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  rcases ha with ha | ⟨hr, h₃, h₄⟩
  · rcases lt_trichotomy r 0 with hr | rfl | hr
    · exact criteria_of_not_isSquare hr hs.le (fun _ ↦ .neg_one_lt ha hr) h₁ h₂ h₁₂
    · simp at h₁
    · exact criteria_of_pos hs hr hc h₂
  · exact criteria_of_not_isSquare (by lia) hs.le
      (.window hr h₃ h₄ (not_isSquare_of_neg (by lia))) h₁ h₂ h₁₂

/-- The window `c_3 < 0 < c_4` lies above `α`: with `X = r² + rs = s² c_2` and
`Y = X² + rs³ = s⁴ c_3`, `Y < -s⁴`, then `X < s²`, and `r (r³ + 2r²s + 2rs² + 2s³) = X s² + Y`. -/
private lemma cubic_pos_of_window (hs : 0 < s) (hr : r < -s)
    (h₃ : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0)
    (h₄ : 0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) :
    0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 := by
  have hY : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < -s ^ 4 := by
    nlinarith [pow_pos hs 4, mul_neg_of_neg_of_pos (by lia : r + s < 0) (pow_pos hs 7)]
  have hX : r ^ 2 + r * s < s ^ 2 := by
    nlinarith [pow_pos hs 2, mul_nonneg (sq_nonneg s) (sq_nonneg (r + s))]
  nlinarith [pow_pos hs 2]

/-- For `a = r/s` in a `2`-adic class with `a ≤ -2`, or `a > -1`, or `a < -1` in the window
`c_3 < 0 < c_4`, if none of `-rs`, `r(r + s)`, `-s(r + s)` is a square, then `Ω_n ≅ [C₂]ⁿ`: the
non-squares among `|r|`, `s`, `|r + s|` give two of the lists of criteria of
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`. -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_not_isSquare (hrs : IsCoprime r s) (hs : 0 < s)
    {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) (h₁ : ¬IsSquare (-(r * s))) (h₂ : ¬IsSquare (r * (r + s)))
    (h₁₂ : ¬IsSquare (-(s * (r + s)))) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  rcases hε with ⟨ha, rfl⟩ | ⟨ha, rfl⟩
  · exact nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs (.inl ⟨ha, rfl⟩) hc
      (criteria_of_le_neg_two hs ha hc h₁ h₂ h₁₂) n
  refine nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs (.inr ⟨?_, rfl⟩) hc
    (criteria_of_twoAdicClass_one hs ha hc h₁ h₂ h₁₂) n
  rcases ha with ha | ⟨hr, h₃, h₄⟩
  exacts [cubic_pos_of_neg_lt hs ha, cubic_pos_of_window hs hr h₃ h₄]

/-- **Level two decides**, in terms of `r` and `s`: for `a = r/s` in a `2`-adic class with
`a ≤ -2`, or `a > -1`, or `a < -1` in the window `c_3 < 0 < c_4`, the arboreal representation of
`X² + a` is surjective if and only if none of `-rs`, `r(r + s)`, `-s(r + s)` is a square. -/
theorem forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass (hrs : IsCoprime r s)
    (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      ¬IsSquare (-(r * s)) ∧ ¬IsSquare (r * (r + s)) ∧ ¬IsSquare (-(s * (r + s))) :=
  ⟨fun h ↦ twoIndependent_fin_two_cSeq_iff.mp ((nonempty_mulEquiv_iff_twoIndependent _ 2).mp (h 2)),
    fun ⟨h₁, h₂, h₁₂⟩ ↦ nonempty_mulEquiv_of_twoAdicClass_of_not_isSquare hrs hs hε hc h₁ h₂ h₁₂⟩

/-- **Level two decides**: for `a = r/s` in a `2`-adic class with `a ≤ -2`, or `a > -1`, or
`a < -1` in the window `c_3 < 0 < c_4`, the arboreal representation of `X² + a` is surjective if and
only if `c_1, c_2` are 2-independent, that is, `Ω_2 ≅ [C₂]²`. -/
theorem forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass (hrs : IsCoprime r s)
    (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      TwoIndependent fun i : Fin 2 ↦ cSeq ((r : ℚ) / s) ((i : ℕ) + 1) :=
  (forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass hrs hs hε hc).trans
    twoIndependent_fin_two_cSeq_iff.symm

/-- **Theorem 3.5 of [Li 2020] for rational parameters**: for `a = r/s ≤ -2` with `r ≡ 3` and
`s ≡ 1 (mod 4)` and `φ₀` (for instance `|r| ≠ □`), the arboreal representation of `X² + a` is
surjective if and only if `-(a + 1)` is not a square. The class is (C1), and `φ₀` makes
`c_1 ∼ -rs` and `c_2 ∼ r(r + s)` non-squares, which leaves `-s(r + s) = s² · (-(a + 1))` in
`QuadraticIterates.forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass`. -/
theorem forall_nonempty_mulEquiv_iff_of_le_neg_two (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r ≤ -2 * s) (hs4 : s % 4 = 1) (hr4 : r % 4 = 3)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      ¬IsSquare (-((r : ℚ) / s + 1)) := by
  obtain ⟨χ, hχ⟩ := h₀
  have hsq (n : ℕ) (hn : 1 ≤ n) : ¬IsSquare (cSeq ((r : ℚ) / s) n) :=
    fun h ↦ χ.apply_ne_neg_one_of_isSquare h (hχ n hn)
  rw [forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass hrs hs (.inl ⟨ha, rfl⟩)
      (twoAdicClass_neg_one_iff.mpr (by lia)), ← isSquare_cSeq_one_iff hs.ne',
    ← isSquare_cSeq_two_iff hs.ne', and_iff_right (hsq 1 le_rfl),
    and_iff_right (hsq 2 one_le_two), ← Rat.isSquare_intCast_iff,
    ← isSquare_mul_sq_iff₀ (a := -((r : ℚ) / s + 1)) (Int.cast_ne_zero.mpr hs.ne')]
  congr! 2
  push_cast
  field

end QuadraticIterates
