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
# Orbits of `x ↦ x² + a`, rigid divisibility, and periodicity modulo `w_m²`

For a parameter `a` in a commutative ring, `x ↦ x² + a` is even, so once `c_{n+1} = -c_n` the
sequence is constant from `n + 1` on, and once `c_{n+2} = -c_n` it is `2`-periodic from `n + 1` on;
moreover `c_n + c_{n+2} = (c_n + c_{n+1})(c_n² - c_n + a + 1)`. If `c_m² = 0`, the sequence is
`m`-periodic from `n = 2` on, so `c_{mk} = c_m`; in a quotient ring this is the rigid divisibility
`c_{mk} ≡ c_m (mod c_m²)`. Modulo `w_m²` it applies to `a = r/s` and gives the congruence of
`w_{mk}` modulo `w_m²`. If `(a + 1)² = 0`, the sequence is `1 - t, -t, t - 1, -t, t - 1, …` with
`t = a + 1`; modulo `(r + s)²` this applies to `a = r/s` and gives the congruence of `w_{2k+1}`
modulo `r + s`.

## Main statements

* `QuadraticIterates.cSeq_eq_of_add_succ_eq_zero`,
  `QuadraticIterates.cSeq_add_two_eq_of_add_two_eq_neg`, `QuadraticIterates.cSeq_add_cSeq_add_two`:
  fixed points, two-cycles, and the factorization of `c_n + c_{n+2}`.
* `QuadraticIterates.cSeq_add_eq_of_sq_eq_zero`, `QuadraticIterates.cSeq_mul_of_sq_eq_zero`: if
  `c_m² = 0`, the sequence is `m`-periodic from `n = 2` on and `c_{mk} = c_m`.
* `QuadraticIterates.cSeq_eq_zero_iff_dvd`: if `m` is the first index with `c_m = 0` and `a ≠ 0`,
  then `c_n = 0 ↔ m ∣ n`.
* `QuadraticIterates.cSeq_sq_dvd_cSeq_mul_sub`, `QuadraticIterates.sq_dvd_cSeq_sub`: rigid
  divisibility, `c_{mk} ≡ c_m (mod c_m²)` for `m ≥ 2` and `c_k ≡ a (mod c_1²)`.
* `QuadraticIterates.wSeq_mul_modEq`: `w_{mk} ≡ w_m s^{2^{mk-1} - 2^{m-1}} (mod w_m²)`, with the
  case `QuadraticIterates.wSeq_two_mul_modEq`, `w_{2k} ≡ (r + s) s^{2^{2k-1} - 2} (mod (r + s)²)`.
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

/-- If `c_m² = 0` (`m ≥ 1`), the sequence is `m`-periodic from `n = 2` on: `c_{m+1} = c_m² + a = a`,
so `c_{m+2} = a² + a = c_2`. -/
theorem cSeq_add_eq_of_sq_eq_zero {m : ℕ} (hm : 1 ≤ m) (h : cSeq a m ^ 2 = 0) {n : ℕ}
    (hn : 2 ≤ n) : cSeq a (n + m) = cSeq a n :=
  cSeq_add_eq_of_add_eq (by norm_num) (by
    rw [show 2 + m = m + 1 + 1 by lia, cSeq_succ a (by lia), cSeq_succ a hm, h, zero_add,
      cSeq_two]) hn

theorem cSeq_add_mul_eq_of_sq_eq_zero {m : ℕ} (hm : 1 ≤ m) (h : cSeq a m ^ 2 = 0) {n : ℕ}
    (hn : 2 ≤ n) (k : ℕ) : cSeq a (n + m * k) = cSeq a n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, cSeq_add_eq_of_sq_eq_zero hm h (by lia), ih]

/-- If `c_m² = 0` for some `m ≥ 2`, then `c_{mk} = c_m` for `k ≥ 1`. -/
theorem cSeq_mul_of_sq_eq_zero {m : ℕ} (hm : 2 ≤ m) (h : cSeq a m ^ 2 = 0) {k : ℕ} (hk : 1 ≤ k) :
    cSeq a (m * k) = cSeq a m := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  rw [mul_add, mul_one, add_comm, cSeq_add_mul_eq_of_sq_eq_zero (by lia) h hm]

/-- If `a² = 0`, then `c_k = a` for `k ≥ 2`: the sequence is `1`-periodic from `n = 2` on, and
`c_2 = a² + a`. -/
theorem cSeq_eq_self_of_sq_eq_zero (h : a ^ 2 = 0) {k : ℕ} (hk : 2 ≤ k) : cSeq a k = a := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by lia⟩
  rw [← one_mul j, cSeq_add_mul_eq_of_sq_eq_zero le_rfl (by rwa [cSeq_one, neg_sq]) le_rfl,
    cSeq_two, h, zero_add]

/-- If `m ≥ 1` is the first index with `c_m = 0`, and `a ≠ 0`, then `c_n = 0 ↔ m ∣ n` for `n ≥ 1`:
the sequence is `m`-periodic from `n = 2` on, with `c_{m+1} = c_m² + a = a`. -/
theorem cSeq_eq_zero_iff_dvd {m : ℕ} (hm : 1 ≤ m) (h : cSeq a m = 0) (ha : a ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < m → cSeq a j ≠ 0) {n : ℕ} (hn : 1 ≤ n) : cSeq a n = 0 ↔ m ∣ n := by
  have hc : cSeq a m ^ 2 = 0 := by rw [h, zero_pow two_ne_zero]
  have hm2 : 2 ≤ m := by
    by_contra! h'
    exact ha (neg_eq_zero.mp (by rwa [show m = 1 by lia, cSeq_one] at h))
  refine ⟨fun h' ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · by_contra hmn
    have hn' := Nat.mod_add_div n m
    rcases Nat.eq_zero_or_pos (n / m) with hq | hq
    · exact hmin n hn (by rw [hq] at hn'; lia [Nat.mod_lt n (by lia : 0 < m)]) h'
    rcases (by lia [show n % m ≠ 0 from fun h ↦ hmn (Nat.dvd_of_mod_eq_zero h)] :
      n % m = 1 ∨ 2 ≤ n % m) with h1 | h2
    · rw [show n = m + 1 + m * (n / m - 1) by lia [Nat.mul_sub_one m (n / m),
        Nat.le_mul_of_pos_right m hq], cSeq_add_mul_eq_of_sq_eq_zero hm hc (by lia),
        cSeq_succ _ hm, hc, zero_add] at h'
      exact ha h'
    · rw [← hn', cSeq_add_mul_eq_of_sq_eq_zero hm hc h2] at h'
      exact hmin _ (by lia) (Nat.mod_lt n (by lia)) h'
  · rw [hk, cSeq_mul_of_sq_eq_zero hm2 hc (Nat.pos_of_ne_zero (by rintro rfl; simp_all)), h]

variable (a) in
/-- **Rigid divisibility**: `c_{mk} ≡ c_m (mod c_m²)` for `m ≥ 2` and `k ≥ 1`. In the quotient by
`c_m²` the image of `c_m` has square zero (`QuadraticIterates.cSeq_mul_of_sq_eq_zero`). -/
theorem cSeq_sq_dvd_cSeq_mul_sub {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) :
    cSeq a m ^ 2 ∣ cSeq a (m * k) - cSeq a m := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_cSeq, map_cSeq]
  refine cSeq_mul_of_sq_eq_zero hm ?_ hk
  rw [← map_cSeq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

variable (a) in
/-- **Rigid divisibility** at `m = 1`, where the sign of `c_1 = -a` is changed:
`c_k ≡ a (mod c_1²)` for `k ≥ 2`. -/
theorem sq_dvd_cSeq_sub {k : ℕ} (hk : 2 ≤ k) : a ^ 2 ∣ cSeq a k - a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_cSeq]
  refine cSeq_eq_self_of_sq_eq_zero ?_ hk
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- If `c_3² = 0`, then `c_{3k+1} = a` for `k ≥ 1`. -/
theorem cSeq_three_mul_add_one_of_sq_eq_zero (h : cSeq a 3 ^ 2 = 0) {k : ℕ} (hk : 1 ≤ k) :
    cSeq a (3 * k + 1) = a := by
  rw [cSeq_succ a (by lia), cSeq_mul_of_sq_eq_zero (by norm_num) h hk, h, zero_add]

/-- If `c_3² = 0`, then `c_{3k+2} = c_2` for all `k`. -/
theorem cSeq_three_mul_add_two_of_sq_eq_zero (h : cSeq a 3 ^ 2 = 0) (k : ℕ) :
    cSeq a (3 * k + 2) = cSeq a 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  rw [show 3 * k + 2 = 3 * k + 1 + 1 from rfl, cSeq_succ a (by lia),
    cSeq_three_mul_add_one_of_sq_eq_zero h hk, cSeq_two]

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

/-- **`m`-periodicity modulo `w_m²`**: for `m ≥ 2` and `k ≥ 1`,
`w_{mk} ≡ w_m s^{2^{mk-1} - 2^{m-1}} (mod w_m²)`. Modulo `w_m²` the term `c̄_m = r w_m σ^{2^{m-1}}`
has square zero, so `c̄_{mk} = c̄_m` (`QuadraticIterates.cSeq_mul_of_sq_eq_zero`), and the
reduction `QuadraticIterates.intCast_mul_wSeq` gives `r w_{mk} = s^{2^{mk-1}} c̄_m`. -/
theorem wSeq_mul_modEq (hrs : IsCoprime r s) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) :
    wSeq r s (m * k) ≡ wSeq r s m * s ^ (2 ^ (m * k - 1) - 2 ^ (m - 1)) [ZMOD wSeq r s m ^ 2] := by
  have hs := isUnit_intCast_zmod_natAbs (m := wSeq r s m ^ 2)
    (isCoprime_wSeq_right hrs (by lia)).pow_left
  have hr := isUnit_intCast_zmod_natAbs (m := wSeq r s m ^ 2)
    (isCoprime_wSeq_left hrs (by lia)).pow_left
  obtain ⟨σ, hσ⟩ := hs.exists_right_inv
  obtain ⟨ρ, hρ⟩ := hr.exists_right_inv
  have h0 : (wSeq r s m : ZMod (wSeq r s m ^ 2).natAbs) ^ 2 = 0 :=
    mod_cast ZMod.intCast_self_natAbs _
  have hσE : (s : ZMod (wSeq r s m ^ 2).natAbs) ^ 2 ^ (m - 1) * σ ^ 2 ^ (m - 1) = 1 := by
    rw [← mul_pow, hσ, one_pow]
  have hcm := intCast_mul_wSeq r hσ (n := m) (by lia)
  have hc : cSeq ((r : ZMod (wSeq r s m ^ 2).natAbs) * σ) m ^ 2 = 0 := by grobner
  have hred := intCast_mul_wSeq r hσ (n := m * k) (Nat.mul_pos (by lia) hk)
  rw [cSeq_mul_of_sq_eq_zero hm hc hk] at hred
  have hpow : (s : ZMod (wSeq r s m ^ 2).natAbs) ^ 2 ^ (m * k - 1) =
      s ^ (2 ^ (m * k - 1) - 2 ^ (m - 1)) * s ^ 2 ^ (m - 1) := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.pow_le_pow_right two_pos
      (Nat.sub_le_sub_right (Nat.le_mul_of_pos_right m hk) 1))]
  exact ZMod.intCast_eq_intCast_iff_modEq.mp (by push_cast; grobner)

/-- `w_{mk} = w_m T` with `T ≡ s^{2^{mk-1} - 2^{m-1}} (mod w_m)`, for `m ≥ 2` and `k ≥ 1`. -/
theorem exists_wSeq_mul_eq (hrs : IsCoprime r s) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) :
    ∃ T, wSeq r s (m * k) = wSeq r s m * T ∧
      T ≡ s ^ (2 ^ (m * k - 1) - 2 ^ (m - 1)) [ZMOD wSeq r s m] := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp (wSeq_mul_modEq hrs hm hk)
  exact ⟨s ^ (2 ^ (m * k - 1) - 2 ^ (m - 1)) - wSeq r s m * t, by linear_combination -ht,
    Int.modEq_iff_dvd.mpr ⟨t, by ring⟩⟩

/-- **Two-periodicity modulo `(r + s)²`**: for `k ≥ 1`,
`w_{2k} ≡ (r + s) s^{2^{2k-1} - 2} (mod (r + s)²)`, the case `m = 2` of
`QuadraticIterates.wSeq_mul_modEq`, as `w_2 = r + s`. -/
theorem wSeq_two_mul_modEq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    wSeq r s (2 * k) ≡ (r + s) * s ^ (2 ^ (2 * k - 1) - 2) [ZMOD (r + s) ^ 2] := by
  simpa using wSeq_mul_modEq hrs le_rfl hk

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

/-- `w_{3k} = w_3 T` with `T ≡ s^{2^{3k-1} - 4} (mod w_3)`, for `k ≥ 1`. -/
theorem exists_wSeq_three_mul_eq (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    ∃ T, wSeq r s (3 * k) = wSeq r s 3 * T ∧ T ≡ s ^ (2 ^ (3 * k - 1) - 4) [ZMOD wSeq r s 3] := by
  simpa using exists_wSeq_mul_eq hrs (m := 3) (by norm_num) hk

end StrongCong

end QuadraticIterates
