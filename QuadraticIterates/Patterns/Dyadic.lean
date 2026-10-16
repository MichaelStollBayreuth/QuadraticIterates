/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat

import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Patterns.Primes
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.SquareClasses

/-!
# The dyadic patterns for `a ≡ 1 mod 4`

For `a = r/s` with `s` odd and `r ≡ s (mod 4)`, modulo `8` the parameter is `rs ∈ {1, 5}` and the
sequence is `(-rs, rs + 1, rs + 4, rs + 1, …)`, so `χ₄(c_n)` is `-1`, `χ₈(rs)`, `1`, `χ₈(rs)`, `1`,
…, while `val₂(c_n)` alternates, `v₂(r + s)` being `1`. Hence `a` has `φ₁`.

## Main statements

* `QuadraticIterates.hasCharPattern_mulSingle_one_of_modEq_four`: `a ≡ 1 mod 4` has `φ₁`.
* `QuadraticIterates.valChar_two_cSeq_succ_of_modEq_four`: `val₂` alternates along `(c_n)`.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

/-! ### `χ₄` from residues modulo `8` -/

private lemma unitPartChar_two_χ₄_of_emod_four_eq_one {x : ℤ} (h : x % 4 = 1) :
    unitPartChar 2 ZMod.χ₄ x = 1 := by
  rw [unitPartChar_intCast (by norm_num : 4 = 2 ^ 2) (by lia), ZMod.χ₄_int_one_mod_four h]

private lemma unitPartChar_two_χ₄_two_mul {m : ℤ} (hm : ¬(2 : ℤ) ∣ m) :
    unitPartChar 2 ZMod.χ₄ ((2 * m : ℤ) : ℚ) = ZMod.χ₄ m := by
  rw [Int.cast_mul, map_mul, Int.cast_ofNat, ← Nat.cast_ofNat (R := ℚ),
    unitPartChar_natCast_self (by norm_num : 4 = 2 ^ 2), one_mul,
    unitPartChar_intCast (by norm_num : 4 = 2 ^ 2) (mod_cast hm)]

private lemma unitPartChar_two_χ₄_of_emod_eight_eq_two {x : ℤ} (h : x % 8 = 2) :
    unitPartChar 2 ZMod.χ₄ x = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m := ⟨x / 2, by lia⟩
  rw [unitPartChar_two_χ₄_two_mul (by lia), ZMod.χ₄_int_one_mod_four (by lia)]

private lemma unitPartChar_two_χ₄_of_emod_eight_eq_six {x : ℤ} (h : x % 8 = 6) :
    unitPartChar 2 ZMod.χ₄ x = -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m := ⟨x / 2, by lia⟩
  rw [unitPartChar_two_χ₄_two_mul (by lia), ZMod.χ₄_int_three_mod_four (by lia)]

private lemma emod_eight_eq {x : ℤ} {y : ℕ} (h : (x : ZMod 8) = y) (hy : y < 8) : x % 8 = y := by
  have := (ZMod.intCast_eq_intCast_iff' x y 8).mp (mod_cast h)
  lia

variable {r s : ℤ}

/-- For odd `s` and `r ≡ s (mod 4)`, the parameter `r s` modulo `8` is `1` or `5`. -/
lemma intCast_mul_zmod_eight_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) :
    (r : ZMod 8) * s = 1 ∨ (r : ZMod 8) * s = 5 := by
  obtain ⟨t, ht⟩ := h4.symm.dvd
  have hr : (r : ZMod 8) = s + 4 * t := by
    rw [show r = s + 4 * t by lia]
    push_cast
    ring
  rw [hr, add_mul, ← sq, ZMod.intCast_sq_eight_eq_one_of_odd hs, mul_assoc]
  generalize (t : ZMod 8) * s = x
  revert x
  decide

private lemma odd_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) : Odd r := by
  obtain ⟨t, ht⟩ := h4.symm.dvd
  rw [show r = s + 2 * (2 * t) by lia]
  exact hs.add_even (even_two_mul _)

private lemma not_two_dvd_of_odd {x : ℤ} (hx : Odd x) : ¬((2 : ℕ) : ℤ) ∣ x := by
  simpa [← even_iff_two_dvd] using hx

/-- For odd `s` and `r ≡ s (mod 4)`, `χ₄(c_1) = -1`: `c_1 ∼ -rs` and `rs ≡ 1 (mod 4)`. -/
theorem unitPartChar_two_χ₄_cSeq_one_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) :
    unitPartChar 2 ZMod.χ₄ (cSeq ((r : ℚ) / s) 1) = -1 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hrs : (r : ZMod 4) = s := (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (mod_cast h4)
  have h1 : ZMod.χ₄ (s : ZMod 4) ^ 2 = 1 := by
    rw [← map_pow]
    exact ZMod.χ₄.apply_sq_of_isUnit (ZMod.isUnit_intCast_of_not_dvd (p := 2)
      (by norm_num : 4 = 2 ^ 2) (not_two_dvd_of_odd hs))
  rw [mulChar_cSeq_one_eq_mul _ hs0, unitPartChar_neg_one (by norm_num : 4 = 2 ^ 2),
    unitPartChar_intCast (by norm_num : 4 = 2 ^ 2) (not_two_dvd_of_odd (odd_of_modEq_four hs h4)),
    unitPartChar_intCast (by norm_num : 4 = 2 ^ 2) (not_two_dvd_of_odd hs), hrs,
    show ZMod.χ₄ (-1) = -1 by decide]
  linear_combination -h1

/-- For odd `s` and `r ≡ s (mod 4)`, `χ₄(c_n) = 1` for odd `n ≥ 3`: `r w_n ≡ rs + 4 (mod 8)`. -/
theorem unitPartChar_two_χ₄_cSeq_two_mul_add_one_of_modEq_four (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) {j : ℕ} (hj : 1 ≤ j) :
    unitPartChar 2 ZMod.χ₄ (cSeq ((r : ℚ) / s) (2 * j + 1)) = 1 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h := intCast_mul_wSeq_zmod_eight r hs (n := 2 * j + 1) (by lia)
  rw [cSeq_two_mul_add_one_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) hj] at h
  rw [mulChar_cSeq_of_two_le _ hs0 (by lia), ← Int.cast_mul]
  refine unitPartChar_two_χ₄_of_emod_four_eq_one ?_
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with ha | ha
  · rw [ha, show (1 : ZMod 8) + 4 = ((5 : ℕ) : ZMod 8) by decide] at h
    have := emod_eight_eq h (by norm_num)
    lia
  · rw [ha, show (5 : ZMod 8) + 4 = ((1 : ℕ) : ZMod 8) by decide] at h
    have := emod_eight_eq h (by norm_num)
    lia

/-- For odd `s` and `r ≡ s (mod 4)`, `χ₄(c_{2j}) = χ₈(rs)` for `j ≥ 1`: `r w_{2j} ≡ rs + 1
(mod 8)`, which is `2` or `6`. -/
theorem unitPartChar_two_χ₄_cSeq_two_mul_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4])
    {j : ℕ} (hj : 1 ≤ j) :
    unitPartChar 2 ZMod.χ₄ (cSeq ((r : ℚ) / s) (2 * j)) = ZMod.χ₈ ((r : ZMod 8) * s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h := intCast_mul_wSeq_zmod_eight r hs (n := 2 * j) (by lia)
  rw [cSeq_two_mul_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) hj] at h
  rw [mulChar_cSeq_of_two_le _ hs0 (by lia), ← Int.cast_mul]
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with ha | ha
  · rw [ha, show (1 : ZMod 8) + 1 = ((2 : ℕ) : ZMod 8) by decide] at h
    rw [ha, unitPartChar_two_χ₄_of_emod_eight_eq_two (emod_eight_eq h (by norm_num))]
    decide
  · rw [ha, show (5 : ZMod 8) + 1 = ((6 : ℕ) : ZMod 8) by decide] at h
    rw [ha, unitPartChar_two_χ₄_of_emod_eight_eq_six (emod_eight_eq h (by norm_num))]
    decide

private lemma two_dvd_add_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) :
    ((2 : ℕ) : ℤ) ∣ r + s := by
  obtain ⟨t, ht⟩ := h4.symm.dvd
  obtain ⟨u, rfl⟩ := hs
  exact ⟨2 * t + 2 * u + 1, by lia⟩

private lemma valChar_two_add_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) :
    valChar 2 ((r + s : ℤ) : ℚ) = -1 := by
  obtain ⟨t, ht⟩ := h4.symm.dvd
  obtain ⟨u, rfl⟩ := hs
  rw [show r + (2 * u + 1) = 2 * (2 * t + 2 * u + 1) by lia, Int.cast_mul, map_mul,
    Int.cast_ofNat, ← Nat.cast_ofNat (R := ℚ), valChar_natCast_self,
    valChar_intCast_of_not_dvd (not_two_dvd_of_odd ⟨t + u, by ring⟩), mul_one]

/-- For `a = r/s ≡ 1 mod 4`, `val₂` alternates along `(c_n)`: `(+, -, +, -, …)`, as
`v₂(r + s) = 1`. -/
theorem valChar_two_cSeq_succ_of_modEq_four (hrs : IsCoprime r s) (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) {m : ℕ} (hm : 1 ≤ m) :
    valChar 2 (cSeq ((r : ℚ) / s) (m + 1)) = -valChar 2 (cSeq ((r : ℚ) / s) m) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h2 := two_dvd_add_of_modEq_four hs h4
  have hv := valChar_two_add_of_modEq_four hs h4
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs0 h2,
      valChar_cSeq_two_mul_of_dvd_add hrs hs0 h2 (by lia), hv, neg_neg]
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, valChar_cSeq_two_mul_of_dvd_add hrs hs0 h2
      (by lia), valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs0 h2, hv]

private lemma hasCharPattern_mulSingle_one_of_parity {M : Type*} [CommMonoid M] {v : ℕ → M}
    (χ : MulChar M ℤ) (h₁ : χ (v 1) = -1) (hodd : ∀ j ≥ 1, χ (v (2 * j + 1)) = 1)
    (heven : ∀ j ≥ 1, χ (v (2 * j)) = 1) : HasCharPattern v 1 (Pi.mulSingle 1 (-1)) := by
  refine ⟨χ, fun m hm ↦ ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [heven j (by lia), Pi.mulSingle_eq_of_ne (by lia)]
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using h₁
    · rw [hodd j hj, Pi.mulSingle_eq_of_ne (by lia)]

/-- For `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s mod 4`), `a` has `φ₁`: `χ₄` has the pattern
`(-1, χ₈(rs), 1, χ₈(rs), 1, …)`, and `val₂` the pattern `(1, -1, 1, -1, …)`, so `χ₄` (if
`rs ≡ 1 mod 8`) or `χ₄ val₂` (if `rs ≡ 5 mod 8`) realizes `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_modEq_four (hrs : IsCoprime r s) (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h2 := two_dvd_add_of_modEq_four hs h4
  have hodd (j : ℕ) := valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs0 h2 j
  have heven (j : ℕ) (hj : 1 ≤ j) := (valChar_cSeq_two_mul_of_dvd_add hrs hs0 h2 hj).trans
    (valChar_two_add_of_modEq_four hs h4)
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with ha | ha
  · refine hasCharPattern_mulSingle_one_of_parity _
      (unitPartChar_two_χ₄_cSeq_one_of_modEq_four hs h4)
      (fun j hj ↦ unitPartChar_two_χ₄_cSeq_two_mul_add_one_of_modEq_four hs h4 hj) fun j hj ↦ ?_
    rw [unitPartChar_two_χ₄_cSeq_two_mul_of_modEq_four hs h4 hj, ha]
    decide
  · refine hasCharPattern_mulSingle_one_of_parity (unitPartChar 2 ZMod.χ₄ * valChar 2) ?_
      (fun j hj ↦ ?_) fun j hj ↦ ?_
    · have h₁ : valChar 2 (cSeq ((r : ℚ) / s) 1) = 1 := hodd 0
      rw [MulChar.coeToFun_mul, Pi.mul_apply, unitPartChar_two_χ₄_cSeq_one_of_modEq_four hs h4, h₁,
        mul_one]
    · simp [unitPartChar_two_χ₄_cSeq_two_mul_add_one_of_modEq_four hs h4 hj, hodd j]
    · simp [unitPartChar_two_χ₄_cSeq_two_mul_of_modEq_four hs h4 hj, heven j hj, ha,
        show ZMod.χ₈ 5 = -1 by decide]

end QuadraticIterates
