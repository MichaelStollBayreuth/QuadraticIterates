/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Sequence.WSeq

import Mathlib.Data.ZMod.Units
import QuadraticIterates.Mathlib.Data.ZMod

/-!
# Orbits of `x ↦ x² + a` and two-periodicity modulo `(r + s)²`

For a parameter `a` in a commutative ring, `x ↦ x² + a` is even, so once `c_{n+1} = -c_n` the
sequence is constant from `n + 1` on, and once `c_{n+2} = -c_n` it is `2`-periodic from `n + 1` on;
moreover `c_n + c_{n+2} = (c_n + c_{n+1})(c_n² - c_n + a + 1)`. If `(a + 1)² = 0`, the sequence is
`1 - t, -t, t - 1, -t, t - 1, …` with `t = a + 1`; modulo `(r + s)²` this applies to `a = r/s` and
gives the congruences of `w_{2k}` modulo `(r + s)²` and of `w_{2k+1}` modulo `r + s`.

## Main statements

* `QuadraticIterates.cSeq_eq_of_add_succ_eq_zero`,
  `QuadraticIterates.cSeq_add_two_eq_of_add_two_eq_neg`, `QuadraticIterates.cSeq_add_cSeq_add_two`:
  fixed points, two-cycles, and the factorization of `c_n + c_{n+2}`.
* `QuadraticIterates.wSeq_two_mul_modEq`: `w_{2k} ≡ (r + s) s^{2^{2k-1} - 2} (mod (r + s)²)`.
* `QuadraticIterates.wSeq_two_mul_add_one_modEq`: `w_{2k+1} ≡ s^{2^{2k} - 1} (mod r + s)`.
* `QuadraticIterates.cSeq_neg_two`, `QuadraticIterates.cSeq_two_mul_add_one_of_sq_eq_neg_one`,
  `QuadraticIterates.cSeq_two_mul_of_sq_eq_neg_one`: the sequences of `a = -2` and of `a` with
  `a² = -1`.
-/

@[expose] public section

namespace QuadraticIterates

section Orbit

variable {R : Type*} [CommRing R] {a : R}

/-- Periodicity propagates along the recursion: if `c_{n₀+k} = c_{n₀}` with `n₀ ≥ 1`, then
`c_{m+k} = c_m` for all `m ≥ n₀`. -/
theorem cSeq_add_eq_of_add_eq {n₀ k : ℕ} (hn₀ : 1 ≤ n₀) (h : cSeq a (n₀ + k) = cSeq a n₀) {m : ℕ}
    (hm : n₀ ≤ m) : cSeq a (m + k) = cSeq a m := by
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m hm ih => rw [Nat.add_right_comm, cSeq_succ a (by lia), cSeq_succ a (by lia), ih]

/-- If `c_{n+1} = -c_n` (`n ≥ 1`), then `c_{n+1}` is a fixed point: `c_m = c_{n+1}` for all
`m > n`, since `x ↦ x² + a` is even. -/
theorem cSeq_eq_of_add_succ_eq_zero {n : ℕ} (hn : 1 ≤ n) (h : cSeq a n + cSeq a (n + 1) = 0)
    {m : ℕ} (hm : n < m) : cSeq a m = cSeq a (n + 1) := by
  have h₁ : cSeq a (n + 1 + 1) = cSeq a (n + 1) :=
    calc cSeq a (n + 1 + 1) = cSeq a (n + 1) ^ 2 + a := cSeq_succ a (by lia)
      _ = cSeq a n ^ 2 + a := by rw [eq_neg_of_add_eq_zero_right h, neg_sq]
      _ = cSeq a (n + 1) := (cSeq_succ a hn).symm
  induction m, (hm : n + 1 ≤ m) using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [cSeq_add_eq_of_add_eq (by lia) h₁ hm, ih]

/-- If `c_{n+2} = -c_n` (`n ≥ 1`), the sequence is `2`-periodic from `n + 1` on. -/
theorem cSeq_add_two_eq_of_add_two_eq_neg {n : ℕ} (hn : 1 ≤ n) (h : cSeq a (n + 2) = -cSeq a n)
    {m : ℕ} (hm : n + 1 ≤ m) : cSeq a (m + 2) = cSeq a m :=
  cSeq_add_eq_of_add_eq (by lia) (by
    rw [show n + 1 + 2 = n + 2 + 1 by lia, cSeq_succ a (by lia), h, neg_sq, ← cSeq_succ a hn]) hm

/-- `c_n + c_{n+2} = (c_n + c_{n+1}) (c_n² - c_n + a + 1)`: the identity
`f(f(x)) + x = (x² + x + a)(x² - x + a + 1)` for `f(x) = x² + a`. -/
theorem cSeq_add_cSeq_add_two {n : ℕ} (hn : 1 ≤ n) :
    cSeq a n + cSeq a (n + 2) =
      (cSeq a n + cSeq a (n + 1)) * (cSeq a n ^ 2 - cSeq a n + a + 1) := by
  rw [cSeq_succ a (by lia : 1 ≤ n + 1), cSeq_succ a hn]
  ring

/-- If `(a + 1)² = 0`, the sequence `1 - t, -t, t - 1, -t, t - 1, …` (`t = a + 1`) has
`c_{2k} = -(a + 1)` for `k ≥ 1`. -/
theorem cSeq_two_mul_of_sq_eq_zero (ht : (a + 1) ^ 2 = 0) {k : ℕ} (hk : 1 ≤ k) :
    cSeq a (2 * k) = -(a + 1) := by
  have h₂ : cSeq a 2 = -(a + 1) := by rw [cSeq_two]; linear_combination ht
  have h₄ : cSeq a (2 + 2) = cSeq a 2 := by
    rw [cSeq_succ a (by norm_num), cSeq_succ a (by norm_num), h₂]
    linear_combination ((a + 1) ^ 2 + 2 * a + 1) * ht
  induction k, hk using Nat.le_induction with
  | base => exact h₂
  | succ k hk ih =>
    rw [mul_add, mul_one, cSeq_add_eq_of_add_eq (by norm_num) h₄ (by lia : 2 ≤ 2 * k), ih]

/-- If `(a + 1)² = 0`, then `c_{2k+1} = a` for `k ≥ 1`. -/
theorem cSeq_two_mul_add_one_of_sq_eq_zero (ht : (a + 1) ^ 2 = 0) {k : ℕ} (hk : 1 ≤ k) :
    cSeq a (2 * k + 1) = a := by
  rw [cSeq_succ a (by lia), cSeq_two_mul_of_sq_eq_zero ht hk, neg_sq, ht, zero_add]

/-- For `a = -2`, `2` is a fixed point: `c_n = 2` for `n ≥ 1`. -/
theorem cSeq_neg_two {n : ℕ} (hn : 1 ≤ n) : cSeq (-2 : R) n = 2 := by
  have h₂ : cSeq (-2 : R) (1 + 1) = cSeq (-2 : R) 1 := by
    rw [cSeq_succ _ le_rfl]
    norm_num
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [cSeq_add_eq_of_add_eq le_rfl h₂ hn, ih]

variable {a : R}

/-- If `a² = -1`, the sequence `-a, a - 1, -a, a - 1, …` has period two: `c_{2j+1} = -a`. -/
theorem cSeq_two_mul_add_one_of_sq_eq_neg_one (ha : a ^ 2 = -1) (j : ℕ) :
    cSeq a (2 * j + 1) = -a := by
  have h₃ : cSeq a (1 + 2) = cSeq a 1 := by
    rw [cSeq_succ a (by norm_num), cSeq_two]
    simp only [cSeq_one]
    linear_combination (a ^ 2 + 2 * a) * ha
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, cSeq_add_eq_of_add_eq le_rfl h₃ (by lia), ih]

/-- If `a² = -1`, then `c_{2j} = a - 1` for `j ≥ 1`. -/
theorem cSeq_two_mul_of_sq_eq_neg_one (ha : a ^ 2 = -1) {j : ℕ} (hj : 1 ≤ j) :
    cSeq a (2 * j) = a - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by lia⟩
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, cSeq_succ a (by lia),
    cSeq_two_mul_add_one_of_sq_eq_neg_one ha, neg_sq]
  linear_combination ha

end Orbit

section ZModEight

variable {a : ZMod 8} (ha : a = 1 ∨ a = 5)
include ha

private lemma cSeq_four_eq_two_zmod_eight : cSeq a (2 + 2) = cSeq a 2 := by
  rw [cSeq_succ a (by norm_num), cSeq_succ a (by norm_num), cSeq_two]
  rcases ha with rfl | rfl <;> decide

/-- For `a ≡ 1 mod 4` in `ZMod 8`, the even terms are `a + 1`:
`(c_n) = (-a, a + 1, a + 4, a + 1, …)`. -/
theorem cSeq_two_mul_zmod_eight {j : ℕ} (hj : 1 ≤ j) : cSeq a (2 * j) = a + 1 := by
  induction j, hj using Nat.le_induction with
  | base => rw [mul_one, cSeq_two]; rcases ha with rfl | rfl <;> decide
  | succ j hj ih =>
    rw [mul_add, mul_one, cSeq_add_eq_of_add_eq (by norm_num) (cSeq_four_eq_two_zmod_eight ha)
      (by lia : 2 ≤ 2 * j), ih]

/-- For `a ≡ 1 mod 4` in `ZMod 8`, the odd terms from `n = 3` on are `a + 4`. -/
theorem cSeq_two_mul_add_one_zmod_eight {j : ℕ} (hj : 1 ≤ j) : cSeq a (2 * j + 1) = a + 4 := by
  rw [cSeq_succ a (by lia), cSeq_two_mul_zmod_eight ha hj]
  rcases ha with rfl | rfl <;> decide

end ZModEight

section StrongCong

variable {r s : ℤ}

private lemma isUnit_intCast_zmod_natAbs {m x : ℤ} (h : IsCoprime m x) :
    IsUnit (x : ZMod m.natAbs) :=
  (ZMod.coe_int_isUnit_iff_isCoprime x _).mpr (by rwa [Int.natCast_natAbs, IsCoprime.abs_left_iff])

/-- **Two-periodicity modulo `(r + s)²`**: for `k ≥ 1`,
`w_{2k} ≡ (r + s) s^{2^{2k-1} - 2} (mod (r + s)²)`. Modulo `(r + s)²` the parameter
`a = r/s` satisfies `(a + 1)² = 0`, so `c̄_{2k} = -(a + 1)`
(`QuadraticIterates.cSeq_two_mul_of_sq_eq_zero`), and the reduction
`QuadraticIterates.intCast_mul_wSeq` gives `r w_{2k} = -s^{2^{2k-1} - 1} (r + s)`. -/
theorem wSeq_two_mul_modEq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    wSeq r s (2 * k) ≡ (r + s) * s ^ (2 ^ (2 * k - 1) - 2) [ZMOD (r + s) ^ 2] := by
  have hs := isUnit_intCast_zmod_natAbs (m := (r + s) ^ 2)
    (by simpa using (hrs.add_mul_left_left 1).pow_left)
  have hr := isUnit_intCast_zmod_natAbs (m := (r + s) ^ 2)
    (by simpa [add_comm] using (hrs.symm.add_mul_left_left 1).pow_left)
  set σ := ↑hs.unit⁻¹
  have hσ : (s : ZMod ((r + s) ^ 2).natAbs) * σ = 1 := hs.mul_val_inv
  obtain ⟨ρ, hρ⟩ := hr.exists_right_inv
  have h0 := ZMod.intCast_self_natAbs ((r + s) ^ 2)
  have hred := intCast_mul_wSeq r hσ (n := 2 * k) (by lia)
  rw [cSeq_two_mul_of_sq_eq_zero (by push_cast at h0; grobner) hk] at hred
  have hpow : (s : ZMod ((r + s) ^ 2).natAbs) ^ 2 ^ (2 * k - 1) =
      s ^ (2 ^ (2 * k - 1) - 2) * s ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel]
    exact Nat.le_self_pow (by lia) 2
  refine ZMod.intCast_eq_intCast_iff_modEq.mp ?_
  push_cast at h0 ⊢
  grobner

/-- For `k ≥ 1`, `w_{2k+1} ≡ s^{2^{2k} - 1} (mod r + s)`: modulo `r + s`, `a = -1` and
`c̄_{2k+1} = -1`. -/
theorem wSeq_two_mul_add_one_modEq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    wSeq r s (2 * k + 1) ≡ s ^ (2 ^ (2 * k) - 1) [ZMOD r + s] := by
  have hs := isUnit_intCast_zmod_natAbs (m := r + s) (by simpa using hrs.add_mul_left_left 1)
  have hr := isUnit_intCast_zmod_natAbs (m := r + s)
    (by simpa [add_comm] using hrs.symm.add_mul_left_left 1)
  set σ := ↑hs.unit⁻¹
  have hσ : (s : ZMod (r + s).natAbs) * σ = 1 := hs.mul_val_inv
  obtain ⟨ρ, hρ⟩ := hr.exists_right_inv
  have h0 := ZMod.intCast_self_natAbs (r + s)
  have hred := intCast_mul_wSeq r hσ (n := 2 * k + 1) (by lia)
  rw [cSeq_two_mul_add_one_of_sq_eq_zero (by push_cast at h0; grobner) hk,
    Nat.add_sub_cancel] at hred
  have hpow : (s : ZMod (r + s).natAbs) ^ 2 ^ (2 * k) = s ^ (2 ^ (2 * k) - 1) * s := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  refine ZMod.intCast_eq_intCast_iff_modEq.mp ?_
  push_cast at h0 ⊢
  grobner

/-- `r w_{2k+1} ≡ -(s^{2^{2k-1}})² (mod r + s)` for `k ≥ 1`: `r ≡ -s` and
`w_{2k+1} ≡ s^{2^{2k} - 1}`. -/
theorem mul_wSeq_two_mul_add_one_modEq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    r * wSeq r s (2 * k + 1) ≡ -1 * (s ^ 2 ^ (2 * k - 1)) ^ 2 [ZMOD r + s] := by
  have hr : r ≡ -1 * s [ZMOD r + s] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  have he : 2 ^ (2 * k) - 1 + 1 = 2 ^ (2 * k - 1) * 2 := by
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_succ, Nat.sub_add_cancel (by lia)]
  refine (hr.mul (wSeq_two_mul_add_one_modEq hrs hk)).trans ?_
  rw [mul_assoc, ← pow_succ', he, pow_mul]

/-- Modulo `r + s`, `u_{2k+1} ≡ 2 s^{2^{2k+1}}` (`k ≥ 1`): there `a ≡ -1` and
`r w_{2k+1} ≡ -s^{2^{2k}}`. -/
theorem uSeq_two_mul_add_one_modEq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    uSeq r s (2 * k + 1) ≡ 2 * s ^ 2 ^ (2 * k + 1) [ZMOD r + s] := by
  have hX := mul_wSeq_two_mul_add_one_modEq hrs hk
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by lia)] at hX
  have h0 : (r + s) * s ^ (2 ^ (2 * k + 1) - 1) ≡ 0 [ZMOD r + s] :=
    Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
  calc uSeq r s (2 * k + 1)
      = (r * wSeq r s (2 * k + 1)) ^ 2 - r * wSeq r s (2 * k + 1) * s ^ 2 ^ (2 * k) +
          (r + s) * s ^ (2 ^ (2 * k + 1) - 1) := by rw [uSeq, Nat.add_sub_cancel]; ring
    _ ≡ (-1 * s ^ 2 ^ (2 * k)) ^ 2 - -1 * s ^ 2 ^ (2 * k) * s ^ 2 ^ (2 * k) + 0 [ZMOD r + s] :=
      ((hX.pow 2).sub (hX.mul_right _)).add h0
    _ = 2 * s ^ 2 ^ (2 * k + 1) := by rw [pow_succ 2 (2 * k), pow_mul]; ring

/-- `w_{2k} = (r + s) T` with `T ≡ s^{2^{2k-1} - 2} (mod r + s)`, for `k ≥ 1`. -/
theorem exists_wSeq_two_mul_eq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    ∃ T, wSeq r s (2 * k) = (r + s) * T ∧ T ≡ s ^ (2 ^ (2 * k - 1) - 2) [ZMOD r + s] := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp (wSeq_two_mul_modEq hrs hk)
  exact ⟨s ^ (2 ^ (2 * k - 1) - 2) - (r + s) * t, by linear_combination -ht,
    Int.modEq_iff_dvd.mpr ⟨t, by ring⟩⟩

end StrongCong

end QuadraticIterates
