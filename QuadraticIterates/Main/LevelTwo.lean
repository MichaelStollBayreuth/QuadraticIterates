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
`a ≤ -2`, or `a > -1`, or `a < -1` in the window `c₃ < 0 < c₄`, the hypotheses of the main theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria` hold as soon as `c₁, c₂` are
2-independent. Modulo squares `c₁ ∼ -rs`, `c₂ ∼ r(r + s)` and `c₁ c₂ ∼ -s(r + s)`, with `r`, `s`,
`r + s` pairwise coprime, and the non-squares among `|r|`, `s`, `|r + s|` give (Z1), (O3)/(O4) and
(T3) or (T4); in the classes `(r, s) ≡ (1, 1)` with `a > 0` and `(3, 3)` with `a ≤ -2` modulo `4`,
(Z2) takes the place of (Z1) when `|r|` is a square. Hence the arboreal representation of `X² + a`
is surjective if and only if `Ω₂ ≅ [C₂]²`.

## Main statements

* `QuadraticIterates.twoIndependent_fin_two_cSeq_iff`: `c₁, c₂` are 2-independent if and only if
  none of `-rs`, `r(r + s)`, `-s(r + s)` is a square.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass` and
  `QuadraticIterates.forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass`: level two
  decides.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_of_le_neg_two`: Li's theorem of 2020 for
  rational parameters.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- **Level two in terms of `r` and `s`**: `c₁, c₂` are 2-independent if and only if none of
`-rs`, `r(r + s)` and `-s(r + s)`, the square classes of `c₁`, `c₂` and `c₁ c₂`, is a square. For
`r = 0` or `s = 0` both sides fail, as `c₁ = 0`. -/
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

/-- The classes of `(r, s) mod 4` of `TwoAdicClass r s (-1)`. -/
private lemma emod_four_of_twoAdicClass_neg_one (hc : TwoAdicClass r s (-1)) :
    r % 4 = 3 ∧ s % 4 = 1 ∨ r % 4 = 3 ∧ s % 4 = 3 ∨ r % 4 = 0 ∧ s % 4 = 1 ∨
      r % 4 = 2 ∧ s % 4 = 3 ∨ r % 4 = 1 ∧ s % 4 = 0 ∨ r % 4 = 1 ∧ s % 4 = 2 := by
  rcases hc with ⟨⟨k, rfl⟩, h⟩ | ⟨⟨k, rfl⟩, h⟩ | ⟨⟨k, rfl⟩, h⟩ <;> rw [Int.ModEq] at h <;> lia

/-- The classes of `(r, s) mod 4` of `TwoAdicClass r s 1`. -/
private lemma emod_four_of_twoAdicClass_one (hc : TwoAdicClass r s 1) :
    r % 4 = 1 ∧ s % 4 = 1 ∨ r % 4 = 1 ∧ s % 4 = 3 ∨ r % 4 = 2 ∧ s % 4 = 1 ∨
      r % 4 = 0 ∧ s % 4 = 3 ∨ r % 4 = 3 ∧ s % 4 = 0 ∨ r % 4 = 3 ∧ s % 4 = 2 := by
  rcases hc with ⟨⟨k, rfl⟩, h⟩ | ⟨⟨k, rfl⟩, h⟩ | ⟨⟨k, rfl⟩, h⟩ <;> rw [Int.ModEq] at h <;> lia

/-- (Z2) for `r + 2s ≡ ±3 (mod 8)`. -/
private lemma negAllCriterion_of_emod_eight
    (h : (r + 2 * s) % 8 = 3 ∨ (r + 2 * s) % 8 = 5) : NegAllCriterion r s := by
  obtain ⟨p, hp, hp8, hpd⟩ : ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ (p : ℤ) ∣ r + 2 * s := by
    rcases lt_or_gt_of_ne (show r + 2 * s ≠ 0 by lia) with hx | hx
    · obtain ⟨p, hp, hp8, hpd⟩ :=
        Int.exists_prime_dvd_of_emod_eight_eq_three_or_five (x := -(r + 2 * s)) (by lia) (by lia)
      exact ⟨p, hp, hp8, dvd_neg.mp hpd⟩
    · exact Int.exists_prime_dvd_of_emod_eight_eq_three_or_five hx h
  exact .dvd_add_two_mul p hp hp8 hpd

/-- With `r < 0`, two of `-r`, `s`, `-(r + s)` are not squares; they give two of (Z1), (O3)/(O4)
and the criterion for `τ` supplied by `hT`. -/
private lemma criteria_of_not_isSquare (hr : r < 0) (hs : 0 ≤ s)
    (hT : ¬IsSquare (-(r + s)) → NegTailCriterion r s) (h₁ : ¬IsSquare (-(r * s)))
    (h₂ : ¬IsSquare (r * (r + s))) (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hZ (h : ¬IsSquare (-r)) : NegAllCriterion r s := .not_isSquare (fun h ↦ hr.not_ge h.nonneg) h
  have hO := negFirstCriterion_of_not_isSquare_right (r := r) hs
  by_cases hr' : IsSquare (-r)
  · exact .inr (.inr ⟨hO fun h ↦ h₁ (neg_mul r s ▸ hr'.mul h),
      hT fun h ↦ h₂ (neg_mul_neg r (r + s) ▸ hr'.mul h)⟩)
  by_cases hs' : IsSquare s
  · exact .inr (.inl ⟨hZ hr', hT fun h ↦ h₁₂ (mul_neg s (r + s) ▸ hs'.mul h)⟩)
  · exact .inl ⟨hZ hr', hO hs'⟩

/-- For `-1 < a < 0`: (T1), and (Z1) or (O3)/(O4). -/
private lemma criteria_of_neg_one_lt (hs : 0 < s) (h₁ : -s < r) (h₀ : r < 0)
    (hc : ¬IsSquare (-(r * s))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  by_cases hr : IsSquare (-r)
  · exact .inr (.inr ⟨negFirstCriterion_of_not_isSquare_right hs.le
      fun h ↦ hc (neg_mul r s ▸ hr.mul h), .neg_one_lt h₁ h₀⟩)
  · exact .inr (.inl ⟨.not_isSquare (fun h ↦ h₀.not_ge h.nonneg) hr, .neg_one_lt h₁ h₀⟩)

/-- For `a > 0`: (O1), and (Z1) if `r ≠ □`; for `r = t²`, (Z2) in the class `(1, 1)` and (T3) in
the classes `(1, 3)` and `(0, 3)`. -/
private lemma criteria_of_pos (hs : 0 < s) (hr : 0 < r) (hc : TwoAdicClass r s 1)
    (h₂ : ¬IsSquare (r * (r + s))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  by_cases hsq : IsSquare r
  swap
  · exact .inl ⟨.not_isSquare hsq fun h ↦ (neg_neg_of_pos hr).not_ge h.nonneg, .pos hr⟩
  have hns : ¬IsSquare (r + s) := fun h ↦ h₂ (hsq.mul h)
  obtain ⟨t, ht⟩ := hsq
  by_cases h11 : r % 4 = 1 ∧ s % 4 = 1
  · refine .inl ⟨negAllCriterion_of_emod_eight ?_, .pos hr⟩
    lia [sq t, Int.sq_emod_eight_eq_one_of_odd (x := t)
      (Int.odd_iff.mpr (by lia [sq t, Int.sq_emod_four t]))]
  · exact .inr (.inr ⟨.pos hr, negTailCriterion_of_emod_four hns
      (fun h ↦ (by lia : -(r + s) < 0).not_ge h.nonneg)
      (by lia [sq t, Int.sq_emod_four t, emod_four_of_twoAdicClass_one hc])⟩)

/-- In the class `(3, 3)` with `r < 0`: (O2), and (Z1), or (Z2) if `r = -t²`, as then `r ≡ 7` and
`r + 2s ≡ 5 (mod 8)`. -/
private lemma criteria_of_emod_four_eq_three (hr : r < 0) (hr4 : r % 4 = 3) (hs4 : s % 4 = 3) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hO : NegFirstCriterion r s :=
    .modEq_four (Int.odd_iff.mpr (by lia)) (by rw [Int.ModEq]; lia)
  by_cases hsq : IsSquare (-r)
  · obtain ⟨t, ht⟩ := hsq
    refine .inl ⟨negAllCriterion_of_emod_eight ?_, hO⟩
    lia [sq t, Int.sq_emod_eight_eq_one_of_odd (x := t)
      (Int.odd_iff.mpr (by lia [sq t, Int.sq_emod_four t]))]
  · exact .inl ⟨.not_isSquare (fun h ↦ hr.not_ge h.nonneg) hsq, hO⟩

/-- For `a ≤ -2`: the classes `(3, 3)` and `(1, 2)` directly, the others by
`QuadraticIterates.criteria_of_not_isSquare` with (T3), as `r + s ≡ 0` or `1 (mod 4)`. -/
private lemma criteria_of_le_neg_two (hs : 0 < s) (ha : r ≤ -2 * s) (hc : TwoAdicClass r s (-1))
    (h₁ : ¬IsSquare (-(r * s))) (h₂ : ¬IsSquare (r * (r + s)))
    (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hr : r < 0 := by lia
  by_cases h33 : r % 4 = 3 ∧ s % 4 = 3
  · exact criteria_of_emod_four_eq_three hr h33.1 h33.2
  by_cases h12 : r % 4 = 1 ∧ s % 4 = 2
  · exact .inl ⟨.not_isSquare (fun h ↦ hr.not_ge h.nonneg)
      (Int.not_isSquare_of_two_le_emod_four (by lia)),
      negFirstCriterion_of_not_isSquare_right hs.le (Int.not_isSquare_of_two_le_emod_four (by lia))⟩
  exact criteria_of_not_isSquare hr hs.le (fun h ↦ negTailCriterion_of_emod_four
    (fun h ↦ (by lia : r + s < 0).not_ge h.nonneg) h
    (by lia [emod_four_of_twoAdicClass_neg_one hc])) h₁ h₂ h₁₂

/-- For `a > -1`, or `a < -1` in the window `c₃ < 0 < c₄`. -/
private lemma criteria_of_twoAdicClass_one (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : -s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7)
    (hc : TwoAdicClass r s 1) (h₁ : ¬IsSquare (-(r * s))) (h₂ : ¬IsSquare (r * (r + s)))
    (h₁₂ : ¬IsSquare (-(s * (r + s)))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  rcases ha with ha | ⟨hr, h₃, h₄⟩
  · rcases lt_trichotomy r 0 with hr | rfl | hr
    · exact criteria_of_neg_one_lt hs ha hr h₁
    · obtain rfl | rfl := Int.isUnit_iff.mp (isCoprime_zero_left.mp hrs)
      all_goals lia [emod_four_of_twoAdicClass_one hc]
    · exact criteria_of_pos hs hr hc h₂
  · exact criteria_of_not_isSquare (by lia) hs.le
      (.window hr h₃ h₄ fun h ↦ (by lia : r + s < 0).not_ge h.nonneg) h₁ h₂ h₁₂

private lemma cubic_pos_of_neg_lt (hs : 0 < s) (h : -s < r) :
    0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 := by
  nlinarith [mul_pos (by lia : 0 < r + s)
    (by nlinarith [sq_nonneg (2 * r + s)] : 0 < r ^ 2 + r * s + s ^ 2), pow_pos hs 3]

/-- The window `c₃ < 0 < c₄` lies above `α`: with `X = r² + rs = s² c₂` and
`Y = X² + rs³ = s⁴ c₃`, `Y < -s⁴`, then `X < s²`, and `r (r³ + 2r²s + 2rs² + 2s³) = X s² + Y`. -/
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
`c₃ < 0 < c₄`, if none of `-rs`, `r(r + s)`, `-s(r + s)` is a square, then `Ω_n ≅ [C₂]ⁿ`: the
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
    (criteria_of_twoAdicClass_one hrs hs ha hc h₁ h₂ h₁₂) n
  rcases ha with ha | ⟨hr, h₃, h₄⟩
  exacts [cubic_pos_of_neg_lt hs ha, cubic_pos_of_window hs hr h₃ h₄]

/-- **Level two decides**, in terms of `r` and `s`: for `a = r/s` in a `2`-adic class with
`a ≤ -2`, or `a > -1`, or `a < -1` in the window `c₃ < 0 < c₄`, the arboreal representation of
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
`a < -1` in the window `c₃ < 0 < c₄`, the arboreal representation of `X² + a` is surjective if and
only if `c₁, c₂` are 2-independent, that is, `Ω₂ ≅ [C₂]²`. -/
theorem forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass (hrs : IsCoprime r s)
    (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      TwoIndependent fun i : Fin 2 ↦ cSeq ((r : ℚ) / s) ((i : ℕ) + 1) :=
  (forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass hrs hs hε hc).trans
    twoIndependent_fin_two_cSeq_iff.symm

/-- **Li 2020 for rational parameters**: for `a = r/s ≤ -2` with `r ≡ 3` and `s ≡ 1 (mod 4)` and
`φ₀` (for instance `|r| ≠ □`), the arboreal representation of `X² + a` is surjective if and only
if `-(a + 1)` is not a square. The class is (C1), and `φ₀` makes `c₁ ∼ -rs` and `c₂ ∼ r(r + s)`
non-squares, which leaves `-s(r + s) = s² · (-(a + 1))` in
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
      (.inl ⟨Int.odd_iff.mpr (by lia), by rw [Int.ModEq]; lia⟩), ← isSquare_cSeq_one_iff hs.ne',
    ← isSquare_cSeq_two_iff hs.ne', and_iff_right (hsq 1 le_rfl),
    and_iff_right (hsq 2 one_le_two), ← Rat.isSquare_intCast_iff,
    ← isSquare_mul_sq_iff₀ (a := -((r : ℚ) / s + 1)) (Int.cast_ne_zero.mpr hs.ne')]
  congr! 2
  push_cast
  field

end QuadraticIterates
