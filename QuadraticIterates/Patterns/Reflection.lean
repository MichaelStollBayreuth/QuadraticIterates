/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat
public import QuadraticIterates.Sequence.WSeq

import Mathlib.Data.ZMod.Units
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.SquareClasses

/-!
# Reflection and period two

Let `ψ` be a character modulo a power `N = p^k` (`k ≥ 1`) of a prime with `ψ(-1) = -1`, and
`χ_ψ = Rat.unitPartChar p ψ`. If `N` divides `v_n` (and `p ∤ r`), then modulo `N` the term
`c̄_{n+1} = -c̄_n` is a fixed point, so `χ_ψ` changes sign after `n` (reflection); if `N` divides
`u_n` (and `p ∤ r + s`), then `c̄_{n+2} = -c̄_n` and `χ_ψ` has the pattern `(x, y, -x, y, -x, …)`
from `n` on (period two). Together with `φ₀`, and for period two a character alternating from `n`
on, both give `φ_n`.

## Main statements

* `QuadraticIterates.unitPartChar_cSeq_of_dvd_vSeq`: the values after reflection, for any `ψ`.
* `QuadraticIterates.hasCharPattern_mulSingle_of_dvd_vSeq`: reflection.
* `QuadraticIterates.hasCharPattern_mulSingle_of_dvd_uSeq`: period two.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

variable {r s : ℤ} {p : ℕ} [Fact p.Prime]

/-- Modulo a power `N = p^k` dividing `v_n`, with `p ∤ r`: `s` has an inverse `σ`, as `v_n` is
prime to `s`, and for the sequence `c̄` of `r σ`, `c̄_n + c̄_{n+1} = 0` and `c̄_n` is a unit, as
`c̄_n (-(1 + c̄_n)) = r σ`. -/
private lemma exists_inv_of_dvd_vSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k) {n : ℕ}
    (hn : 1 ≤ n) (hdvd : (N : ℤ) ∣ vSeq r s n) (hpr : ¬(p : ℤ) ∣ r) :
    ∃ σ : ZMod N, (s : ZMod N) * σ = 1 ∧
      cSeq ((r : ZMod N) * σ) n + cSeq ((r : ZMod N) * σ) (n + 1) = 0 ∧
      IsUnit (cSeq ((r : ZMod N) * σ) n) := by
  obtain ⟨σ, hσ⟩ := ((ZMod.coe_int_isUnit_iff_isCoprime s N).mpr
    ((isCoprime_vSeq_right hrs n).of_isCoprime_of_dvd_left hdvd)).exists_right_inv
  have hsum := cSeq_add_cSeq_succ_eq_zero_of_vSeq hσ hn
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd)
  have ha : cSeq ((r : ZMod N) * σ) n * (-(1 + cSeq ((r : ZMod N) * σ) n)) = (r : ZMod N) * σ := by
    linear_combination cSeq_succ ((r : ZMod N) * σ) hn - hsum
  exact ⟨σ, hσ, hsum, isUnit_of_mul_isUnit_left (ha ▸ (ZMod.isUnit_intCast_of_not_dvd hN hpr).mul
    (.of_mul_eq_one_right _ hσ))⟩

/-- **Reflection values**: let `ψ` be a character modulo a power `N = p^k` (`k ≥ 1`). If
`N ∣ v_n` and `p ∤ r`, then `χ_ψ(c_m) = ψ(-1) χ_ψ(c_n)` for all `m > n`: modulo `N`,
`c̄_n + c̄_{n+1} = 0`, so `c̄_m = -c̄_n` is a fixed point. -/
theorem unitPartChar_cSeq_of_dvd_vSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k)
    (hk : k ≠ 0) (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 1 ≤ n) (hdvd : (N : ℤ) ∣ vSeq r s n)
    (hpr : ¬(p : ℤ) ∣ r) {m : ℕ} (hm : n < m) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) m) = ψ (-1) * unitPartChar p ψ (cSeq ((r : ℚ) / s) n) := by
  obtain ⟨σ, hσ, hsum, hu⟩ := exists_inv_of_dvd_vSeq hrs hN hn hdvd hpr
  have hcm := cSeq_eq_of_add_succ_eq_zero hn hsum hm
  rw [eq_neg_of_add_eq_zero_right hsum] at hcm
  rw [unitPartChar_cSeq hN hk ψ hσ (by lia) (hcm ▸ hu.neg), hcm,
    unitPartChar_cSeq hN hk ψ hσ hn hu, neg_eq_neg_one_mul, map_mul]

/-- If `N = p^k ∣ v_n` (`k ≥ 1`) and `p ∤ r`, then the term `c̄_n` of the sequence of `r/s` modulo
`N` is a unit, so `χ_ψ(c_n) = ψ(c̄_n) ≠ 0` (`QuadraticIterates.unitPartChar_cSeq`). -/
theorem unitPartChar_cSeq_ne_zero_of_dvd_vSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k)
    (hk : k ≠ 0) (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 1 ≤ n) (hdvd : (N : ℤ) ∣ vSeq r s n)
    (hpr : ¬(p : ℤ) ∣ r) : unitPartChar p ψ (cSeq ((r : ℚ) / s) n) ≠ 0 := by
  obtain ⟨σ, hσ, -, hu⟩ := exists_inv_of_dvd_vSeq hrs hN hn hdvd hpr
  exact unitPartChar_cSeq hN hk ψ hσ hn hu ▸ (hu.map ψ).ne_zero

/-- **Reflection**: let `ψ` be a character modulo a power `N = p^k` (`k ≥ 1`) with `ψ(-1) = -1`.
If `N ∣ v_n` and `p ∤ r`, then `χ_ψ(c_m) = -χ_ψ(c_n) ≠ 0` for all `m > n`
(`QuadraticIterates.unitPartChar_cSeq_of_dvd_vSeq`). With `φ₀` this gives `φ_n`. -/
theorem hasCharPattern_mulSingle_of_dvd_vSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k)
    (hk : k ≠ 0) {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) {n : ℕ} (hn : 1 ≤ n)
    (hdvd : (N : ℤ) ∣ vSeq r s n) (hpr : ¬(p : ℤ) ∣ r)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) n (-1)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) :=
  hasCharPattern_mulSingle_of_neg_of_forall_lt h₀
    (unitPartChar_cSeq_ne_zero_of_dvd_vSeq hrs hN hk ψ hn hdvd hpr) fun m hm ↦ by
      rw [unitPartChar_cSeq_of_dvd_vSeq hrs hN hk ψ hn hdvd hpr hm, hψ, neg_one_mul]

/-- Modulo a power `N = p^k` dividing `u_n`, with `p ∤ r + s`: `s` has an inverse `σ`, as `u_n` is
prime to `s`, and for the sequence `c̄` of `a = r σ`, `c̄_{n+2} = -c̄_n`, and `c̄_n`,
`c̄_{n+1} = c̄_n - 1` are units, as `c̄_n (c̄_n - 1) = -(a + 1)` is. -/
private lemma exists_inv_of_dvd_uSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k) {n : ℕ}
    (hn : 1 ≤ n) (hdvd : (N : ℤ) ∣ uSeq r s n) (hprs : ¬(p : ℤ) ∣ r + s) :
    ∃ σ : ZMod N, (s : ZMod N) * σ = 1 ∧
      cSeq ((r : ZMod N) * σ) (n + 2) = -cSeq ((r : ZMod N) * σ) n ∧
      IsUnit (cSeq ((r : ZMod N) * σ) n) ∧ IsUnit (cSeq ((r : ZMod N) * σ) (n + 1)) := by
  obtain ⟨σ, hσ⟩ := ((ZMod.coe_int_isUnit_iff_isCoprime s N).mpr
    ((isCoprime_uSeq_right hrs hn).of_isCoprime_of_dvd_left hdvd)).exists_right_inv
  refine ⟨σ, hσ, ?_⟩
  set c := cSeq ((r : ZMod N) * σ)
  have hq := cSeq_sq_sub_cSeq_add_eq_zero_of_uSeq hσ hn
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd)
  have h₁ : c (n + 1) = c n - 1 := by linear_combination cSeq_succ ((r : ZMod N) * σ) hn + hq
  have hu : IsUnit (c n * (c n - 1)) := by
    have : c n * (c n - 1) = -((r + s : ℤ) : ZMod N) * σ := by push_cast; linear_combination hq + hσ
    exact this ▸ ((ZMod.isUnit_intCast_of_not_dvd hN hprs).neg.mul (.of_mul_eq_one_right _ hσ))
  refine ⟨?_, isUnit_of_mul_isUnit_left hu, h₁ ▸ isUnit_of_mul_isUnit_right hu⟩
  have h₃ := cSeq_add_cSeq_add_two (a := (r : ZMod N) * σ) hn
  rw [hq, mul_zero] at h₃
  linear_combination h₃

/-- A sequence with units at `n + 1` and `n + 2` that is `2`-periodic from `n + 1` on has units
at all `m ≥ n + 1`. -/
private lemma isUnit_of_add_two_eq {M : Type*} [Monoid M] {c : ℕ → M} {n : ℕ}
    (h₁ : IsUnit (c (n + 1))) (h₂ : IsUnit (c (n + 2))) (hp : ∀ m ≥ n + 1, c (m + 2) = c m)
    (m : ℕ) (hm : n + 1 ≤ m) : IsUnit (c m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k using Nat.twoStepInduction with
  | zero => exact h₁
  | one => exact h₂
  | more k ih _ => simpa [hp (n + 1 + k) (by lia), ← add_assoc] using ih (by lia)

/-- **Period two**: let `ψ` be a character modulo a power `N = p^k` (`k ≥ 1`) with `ψ(-1) = -1`.
If `N ∣ u_n` and `p ∤ r + s`, then `χ_ψ` has the pattern `(x, y, -x, y, -x, …)` from `n` on
(modulo `N`, `c̄_{n+2} = -c̄_n`); with `φ₀` and a character alternating from `n` on, this gives
`φ_n`. -/
theorem hasCharPattern_mulSingle_of_dvd_uSeq (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k)
    (hk : k ≠ 0) {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) {n : ℕ} (hn : 1 ≤ n)
    (hdvd : (N : ℤ) ∣ uSeq r s n) (hprs : ¬(p : ℤ) ∣ r + s)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) n (-1)) {χ : MulChar ℚ ℤ}
    (hχ₀ : χ (cSeq ((r : ℚ) / s) n) ≠ 0)
    (hχ : ∀ m ≥ n, χ (cSeq ((r : ℚ) / s) (m + 1)) = -χ (cSeq ((r : ℚ) / s) m)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  obtain ⟨σ, hσ, h₂, hu₀, hu₁⟩ := exists_inv_of_dvd_uSeq hrs hN hn hdvd hprs
  have hper (m : ℕ) (hm : n + 1 ≤ m) := cSeq_add_two_eq_of_add_two_eq_neg hn h₂ hm
  have hu (m : ℕ) (hm : n + 1 ≤ m) := isUnit_of_add_two_eq hu₁ (h₂ ▸ hu₀.neg) hper m hm
  refine hasCharPattern_mulSingle_of_neg_of_alternating h₀ hχ₀ hχ (χ := unitPartChar p ψ)
    (unitPartChar_cSeq hN hk ψ hσ hn hu₀ ▸ (hu₀.map ψ).ne_zero)
    (unitPartChar_cSeq hN hk ψ hσ (by lia) hu₁ ▸ (hu₁.map ψ).ne_zero) ?_ fun m hm ↦ ?_
  · rw [unitPartChar_cSeq hN hk ψ hσ (by lia) (hu _ (by lia)), unitPartChar_cSeq hN hk ψ hσ hn hu₀,
      h₂, neg_eq_neg_one_mul, map_mul, hψ, neg_one_mul]
  · rw [unitPartChar_cSeq hN hk ψ hσ (by lia) (hu _ (by lia)),
      unitPartChar_cSeq hN hk ψ hσ (by lia) (hu m hm), hper m hm]

end QuadraticIterates
