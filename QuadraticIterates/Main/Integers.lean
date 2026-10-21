/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Main.Families

import QuadraticIterates.Galois.Criterion
import QuadraticIterates.Main.LevelTwo
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.RingTheory.Multiplicity

/-!
# Integer parameters

The known results for `a ∈ ℤ` are the case `s = 1` of the rational statements: the main result of
Section 3 of the paper, Theorem 3.5 of [Li 2020] and Theorems 3.3 and 3.9 of [Li 2021].

## Main statements

* `QuadraticIterates.section3_main`, with the three cases
  `QuadraticIterates.nonempty_mulEquiv_of_pos_of_emod_four_eq_one`,
  `QuadraticIterates.nonempty_mulEquiv_of_pos_of_emod_four_eq_two` and
  `QuadraticIterates.nonempty_mulEquiv_of_neg_of_emod_four_eq_zero`.
* `QuadraticIterates.li2020_theorem_3_5`.
* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul` (Theorem A) and
  `QuadraticIterates.li2021_theorem_3_3`, its case of even `k`.
* `QuadraticIterates.li2021_theorem_3_9`.

## References

* [M. Stoll, *Galois groups over ℚ of some iterated polynomials*, Arch. Math. 59 (1992)]
* [H.-C. Li, Arch. Math. 114 (2020), 265-269]
* [H.-C. Li, Arch. Math. 117 (2021), 133-140]
-/

@[expose] public section

namespace QuadraticIterates

private lemma nonempty_mulEquiv_zero (a : ℚ) : Nonempty (GaloisGroup a 0 ≃* WreathPower 0) :=
  (nonempty_mulEquiv_iff_twoIndependent a 0).mpr fun S hS ↦
    (hS.ne_empty S.eq_empty_of_isEmpty).elim

variable {a : ℤ}

/-- The main theorem `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria` at
`s = 1`. -/
private lemma nonempty_mulEquiv_of_criteria_of_integer {ε : ℤ}
    (hε : (a ≤ -2 ∧ ε = -1) ∨ (0 < a ^ 3 + 2 * a ^ 2 + 2 * a + 2 ∧ ε = 1))
    (hc : TwoAdicClass a 1 ε)
    (h : NegAllCriterion a 1 ∧ NegFirstCriterion a 1 ∨ NegAllCriterion a 1 ∧ NegTailCriterion a 1 ∨
      NegFirstCriterion a 1 ∧ NegTailCriterion a 1) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := by
  have := nonempty_mulEquiv_of_twoAdicClass_of_criteria isCoprime_one_right one_pos
    (by simpa using hε) hc h n
  rwa [Int.cast_one, div_one] at this

/-- Section 3 of the paper, case a): `a > 0` and `a ≡ 1 mod 4`, by (O1), (C1) and (Z1), or (Z2)
when `a` is a square: then `a ≡ 1 (mod 8)`, and `a + 2 ≡ 3 (mod 8)`. -/
theorem nonempty_mulEquiv_of_pos_of_emod_four_eq_one (ha : 0 < a) (ha4 : a % 4 = 1) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := by
  refine nonempty_mulEquiv_of_criteria_of_integer (.inr ⟨by positivity, rfl⟩)
    (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩) (.inl ⟨?_, .pos ha⟩) n
  by_cases hsq : IsSquare a
  · obtain ⟨t, rfl⟩ := hsq
    have ht : Odd t := Int.odd_iff.mpr (by lia [Int.sq_emod_four t, sq t])
    obtain ⟨p, hp, hp8, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_three_or_five
      (x := t * t + 2) (by positivity) (.inl (by lia [Int.eight_dvd_sq_sub_one_of_odd ht, sq t]))
    exact .dvd_add_two_mul p hp hp8 (by simpa using hpd)
  · exact .not_isSquare hsq fun ⟨t, ht⟩ ↦ by lia [mul_self_nonneg t]

/-- Section 3 of the paper, case b): `a > 0` and `a ≡ 2 mod 4`, by (O1), (C2) and (Z1). -/
theorem nonempty_mulEquiv_of_pos_of_emod_four_eq_two (ha : 0 < a) (ha4 : a % 4 = 2) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_criteria_of_integer (.inr ⟨by positivity, rfl⟩)
    (.inr (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩))
    (.inl ⟨.not_isSquare (Int.not_isSquare_of_two_le_emod_four (by lia))
      (Int.not_isSquare_of_two_le_emod_four (by lia)), .pos ha⟩) n

/-- Section 3 of the paper, case c): `a < 0`, `a ≡ 0 mod 4` and `-a ≠ □`, by (C2), (Z1), and (O5)
or (T2) for the odd part `m` of `a = 2^k m`, `k ≥ 2`. -/
theorem nonempty_mulEquiv_of_neg_of_emod_four_eq_zero (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := by
  have h₀ : NegAllCriterion a 1 := .not_isSquare (fun ⟨t, ht⟩ ↦ by lia [mul_self_nonneg t]) hsq
  obtain ⟨k, m, hk, hrm, hm⟩ := Int.exists_pow_mul_of_dvd Nat.prime_two ha.ne
    (by push_cast; lia)
  push_cast at hrm hm
  have hk2 : 2 ≤ k := by
    by_contra hk2
    obtain rfl : k = 1 := by lia
    lia
  refine nonempty_mulEquiv_of_criteria_of_integer (.inl ⟨by lia, rfl⟩)
    (.inr (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩)) ?_ n
  rcases (by lia : m % 4 = 1 ∨ m % 4 = 3) with h | h
  · exact .inl ⟨h₀, .dvd_left_two k m hk2 hrm (by simpa using h)⟩
  · exact .inr (.inl ⟨h₀, .dvd_left_two k m hk2 hrm (by simpa using h)⟩)

/-- **Section 3, main result** of the paper: if `a > 0` and `a ≡ 1, 2 mod 4`, or `a < 0`,
`a ≡ 0 mod 4` and `-a` is not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem section3_main
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := fun n _ ↦ by
  rcases hcase with ⟨ha, h4⟩ | ⟨ha, h4⟩ | ⟨ha, h4, hsq⟩
  exacts [nonempty_mulEquiv_of_pos_of_emod_four_eq_one ha h4 n,
    nonempty_mulEquiv_of_pos_of_emod_four_eq_two ha h4 n,
    nonempty_mulEquiv_of_neg_of_emod_four_eq_zero ha h4 hsq n]

/-- Theorem 3.5 of [Li 2020]: for `a < 0` with `a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ`
for all `n ≥ 1` if and only if `-a - 1` is not a square; the case `s = 1` of
`QuadraticIterates.forall_nonempty_mulEquiv_iff_of_le_neg_two`. -/
theorem li2020_theorem_3_5 (ha : a < 0) (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) := by
  have ha5 : a ≤ -2 * 1 := by
    by_contra h
    obtain rfl : a = -1 := by lia
    exact hsq ⟨1, by norm_num⟩
  have h := forall_nonempty_mulEquiv_iff_of_le_neg_two isCoprime_one_right one_pos ha5 rfl ha4
    (hasCharPattern_neg_one_of_negAllCriterion isCoprime_one_right one_ne_zero
      (.not_isSquare (fun ⟨t, ht⟩ ↦ by lia [mul_self_nonneg t]) hsq))
  rw [Int.cast_one, div_one, show -((a : ℚ) + 1) = ((-a - 1 : ℤ) : ℚ) by push_cast; ring,
    Rat.isSquare_intCast_iff] at h
  rw [← h]
  exact ⟨fun h n ↦ n.eq_zero_or_pos.elim (fun h0 ↦ h0 ▸ nonempty_mulEquiv_zero _) (h n),
    fun h n _ ↦ h n⟩

/-- For `a = -(4k+2)(4k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`: the case `j = 4k + 2` of
`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`. Theorem 3.3 of [Li 2021]
(`QuadraticIterates.li2021_theorem_3_3`) is the case of even `k`. -/
theorem nonempty_mulEquiv_of_eq_neg_mul {k : ℕ} (ha : a = -((4 * k + 2) * (4 * k + 3))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := fun n _ ↦ by
  rw [show (a : ℚ) = -(((4 * k + 2 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) *
      (((4 * k + 2 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) + 1)) by rw [ha]; push_cast; ring]
  exact nonempty_mulEquiv_of_eq_neg_mul_add_one isCoprime_one_right one_pos (by lia)
    (.inl ⟨by lia, rfl⟩) n

/-- Theorem 3.3 of [Li 2021]: for `a = -(8k+2)(8k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`; the case of
even `k` of `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul`. -/
theorem li2021_theorem_3_3 {k : ℕ} (ha : a = -((8 * k + 2) * (8 * k + 3))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_eq_neg_mul (k := 2 * k) (by rw [ha]; push_cast; ring)

/-- Theorem 3.9 of [Li 2021]: for `a = -((4k+1)(4k+2)+1)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`; the
case `ℓ = 4k + 1` of `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`. -/
theorem li2021_theorem_3_9 {k : ℕ} (ha : a = -((4 * k + 1) * (4 * k + 2) + 1)) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) := fun n _ ↦ by
  rw [show (a : ℚ) = -((((4 * k + 1 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ 2 +
      ((4 * k + 1 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) + 1) by rw [ha]; push_cast; ring]
  exact nonempty_mulEquiv_of_eq_neg_sq_add_add_one isCoprime_one_right (by lia) one_pos
    (by lia [sq_nonneg (k : ℤ)]) (.inl ⟨by lia, rfl⟩) n

end QuadraticIterates
