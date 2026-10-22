/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Galois.Iterates

import QuadraticIterates.Mathlib.Algebra.QuadraticDiscriminant

/-!
# Signs and sizes of the terms `c_n`

For a parameter `a` in a linearly ordered commutative ring: the signs of `c_n` for `a > 0`, for
`-1 < a < 0` and for `a ≤ -2`; the window `a < -1`, `c_3 < 0 < c_4`, in which the odd terms lie
in `[a, c_3]` with `c_3 < -1` and the even terms in `[c_4, c_2]` with `c_4 > 0`; the negativity
of `c_n + c_{n+1}` for `α < a < 0`, `α` the real root of `x³ + 2x² + 2x + 2`; and the positivity
of `c_n² - c_n + a + 1` for `a ≤ -2`, for `a > -1`, and at the odd `n ≥ 3` in the window.

## Main statements

* `QuadraticIterates.cSeq_pos_of_pos`, `QuadraticIterates.cSeq_neg_of_neg_one_lt`,
  `QuadraticIterates.neg_le_cSeq_of_le_neg_two`: the signs.
* `QuadraticIterates.cSeq_mem_Icc_of_even`, `QuadraticIterates.cSeq_mem_Icc_of_odd`: the window.
* `QuadraticIterates.cSeq_add_cSeq_succ_neg`: `c_n + c_{n+1} < 0` for `α < a < 0` and `n ≥ 2`.
* `QuadraticIterates.cSeq_sq_sub_cSeq_add_pos_of_le_neg_two`,
  `QuadraticIterates.cSeq_sq_sub_cSeq_add_pos_of_neg_one_lt`,
  `QuadraticIterates.cSeq_sq_sub_cSeq_add_pos_of_odd`: `c_n² - c_n + a + 1 > 0`.
-/

@[expose] public section

namespace QuadraticIterates

section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a : R)

theorem le_cSeq {n : ℕ} (hn : 2 ≤ n) : a ≤ cSeq a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [cSeq_succ a (by lia)]
  exact le_add_of_nonneg_left (sq_nonneg _)

variable {a}

/-- For `-2 ≤ a ≤ 0` the second iterate `c_2 = a² + a` bounds the sequence from above: the
interval `[a, a² + a]`, contained in `[a, -a]`, is mapped into itself by `x ↦ x² + a`. -/
theorem cSeq_le_sq_add (h₂ : -2 ≤ a) (h₀ : a ≤ 0) {n : ℕ} (hn : 2 ≤ n) : cSeq a n ≤ a ^ 2 + a := by
  induction n, hn using Nat.le_induction with
  | base => exact (cSeq_two a).le
  | succ k hk ih =>
    have hle : a ^ 2 + a ≤ -a := by
      linear_combination mul_nonpos_of_nonpos_of_nonneg h₀ (by linarith : 0 ≤ a + 2)
    rw [cSeq_succ a (by lia), ← neg_sq a]
    exact add_le_add (sq_le_sq' (by linarith [le_cSeq a hk]) (ih.trans hle)) le_rfl

-- the real root of `x³ + 2x² + 2x + 2` is larger than `-2`
private lemma neg_two_lt_of_pos (h : 0 < a ^ 3 + 2 * a ^ 2 + 2 * a + 2) : -2 < a := by
  by_contra! h'
  linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith : a + 2 ≤ 0)]

/-- The first iterate `a = -c_1` and the second, `c_2 = a² + a`, have negative sum for
`-2 < a < 0`. -/
theorem add_cSeq_two_neg (h₂ : -2 < a) (ha : a < 0) : a + cSeq a 2 < 0 := by
  rw [cSeq_two]
  linear_combination mul_neg_of_neg_of_pos ha (by linarith : 0 < a + 2)

/-- **Sums of successive iterates are negative** for `α < a < 0`, where `α ≈ -1.5437` is the real
root of `x³ + 2x² + 2x + 2`: `c_n + c_{n+1} < 0` for all `n ≥ 2` (the first pair is
`QuadraticIterates.add_cSeq_two_neg`). The hypothesis `0 < a³ + 2a² + 2a + 2` says `α < a`, the
cubic being increasing; `QuadraticIterates.cSeq_add_cSeq_succ_neg_of_lt` has the root in the
statement. Proof: `c_n + c_{n+1} = q(c_n)` for `q(x) = x² + x + a`, `c_n` lies in `[a, a² + a]`,
and the convex `q` is negative at both endpoints, `q(a) = a (a + 2)` and
`q(a² + a) = a (a³ + 2a² + 2a + 2)`. -/
theorem cSeq_add_cSeq_succ_neg (ha : a < 0) (hα : 0 < a ^ 3 + 2 * a ^ 2 + 2 * a + 2) {n : ℕ}
    (hn : 2 ≤ n) :
    cSeq a n + cSeq a (n + 1) < 0 := by
  have h₂ := neg_two_lt_of_pos hα
  have hl : 1 * (a * a) + 1 * a + a < 0 := by
    linear_combination mul_neg_of_neg_of_pos ha (by linarith : 0 < a + 2)
  have hu : 1 * ((a ^ 2 + a) * (a ^ 2 + a)) + 1 * (a ^ 2 + a) + a < 0 := by
    linear_combination mul_neg_of_neg_of_pos ha hα
  have := (quadratic_le_max_of_nonneg_of_mem_Icc zero_le_one 1 a
    ⟨le_cSeq a hn, cSeq_le_sq_add h₂.le ha.le hn⟩).trans_lt (max_lt hl hu)
  rw [cSeq_succ a (by lia)]
  linear_combination this

/-- `QuadraticIterates.cSeq_add_cSeq_succ_neg` with the root in the statement: for a root `α` of
`x³ + 2x² + 2x + 2` (over `ℝ`, its only real root, `α ≈ -1.5437`) and `α < a < 0`, the sums
`c_n + c_{n+1}`, `n ≥ 2`, are negative. -/
theorem cSeq_add_cSeq_succ_neg_of_lt {α : R} (hα : α ^ 3 + 2 * α ^ 2 + 2 * α + 2 = 0) (h : α < a)
    (ha : a < 0) {n : ℕ} (hn : 2 ≤ n) :
    cSeq a n + cSeq a (n + 1) < 0 := by
  refine cSeq_add_cSeq_succ_neg ha ?_ hn
  have hpos : 0 < a ^ 2 + a * α + α ^ 2 + 2 * a + 2 * α + 2 := by
    linarith [sq_nonneg (2 * a + α + 2), sq_nonneg (3 * α + 2)]
  linear_combination mul_pos (sub_pos.2 h) hpos - hα

theorem cSeq_pos_of_pos (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) : 0 < cSeq a n :=
  ha.trans_le (le_cSeq a hn)

theorem cSeq_neg_of_neg_one_lt (h₁ : -1 < a) (h₀ : a < 0) {n : ℕ} (hn : 2 ≤ n) : cSeq a n < 0 :=
  (cSeq_le_sq_add (by linarith) h₀.le hn).trans_lt (by nlinarith)

theorem neg_le_cSeq_of_le_neg_two (ha : a ≤ -2) {n : ℕ} (hn : 1 ≤ n) : -a ≤ cSeq a n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [cSeq_succ a hk]
    nlinarith

/-- In the window `a < -1`, `c_3 < 0 < c_4`, the third term is below `-1`: `c_3² = c_4 - a > 1`. -/
theorem cSeq_three_lt_neg_one (ha : a < -1) (h₃ : cSeq a 3 < 0) (h₄ : 0 < cSeq a 4) :
    cSeq a 3 < -1 := by
  rw [cSeq_succ a (by norm_num : 1 ≤ 3)] at h₄
  nlinarith

/-- The window `a < -1`, `c_3 < 0 < c_4`: from `k = 1` on, `c_{2k} ∈ [c_4, c_2]` and
`c_{2k+1} ∈ [a, c_3]`. The map `x ↦ x² + a` is decreasing on `[a, c_3] ⊆ (-∞, 0)` with image
`[c_4, c_2]`, and increasing on `[c_4, c_2] ⊆ (0, ∞)` with image `[c_5, c_3] ⊆ [a, c_3]`. -/
private theorem cSeq_mem_Icc_and_mem_Icc (ha : a < -1) (h₃ : cSeq a 3 < 0) (h₄ : 0 < cSeq a 4)
    {k : ℕ} (hk : 1 ≤ k) :
    cSeq a (2 * k) ∈ Set.Icc (cSeq a 4) (cSeq a 2) ∧
      cSeq a (2 * k + 1) ∈ Set.Icc a (cSeq a 3) := by
  have h31 := cSeq_three_lt_neg_one ha h₃ h₄
  have hc3 : cSeq a 3 = cSeq a 2 ^ 2 + a := cSeq_succ a (by norm_num)
  have hc4 : cSeq a 4 = cSeq a 3 ^ 2 + a := cSeq_succ a (by norm_num)
  have hc2 : cSeq a 2 = a ^ 2 + a := cSeq_two a
  induction k, hk using Nat.le_induction with
  | base => exact ⟨⟨by nlinarith, le_rfl⟩, le_cSeq a (by norm_num), le_rfl⟩
  | succ k hk ih =>
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih
    have he : cSeq a (2 * (k + 1)) = cSeq a (2 * k + 1) ^ 2 + a := cSeq_succ a (by lia)
    have ho : cSeq a (2 * (k + 1) + 1) = cSeq a (2 * (k + 1)) ^ 2 + a := cSeq_succ a (by lia)
    have he₁ : cSeq a 4 ≤ cSeq a (2 * (k + 1)) := by nlinarith
    have he₂ : cSeq a (2 * (k + 1)) ≤ cSeq a 2 := by nlinarith
    exact ⟨⟨he₁, he₂⟩, le_cSeq a (by lia), by nlinarith [h₄.trans_le he₁]⟩

theorem cSeq_mem_Icc_of_even (ha : a < -1) (h₃ : cSeq a 3 < 0) (h₄ : 0 < cSeq a 4) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    cSeq a n ∈ Set.Icc (cSeq a 4) (cSeq a 2) := by
  obtain ⟨k, rfl⟩ := he
  simpa [two_mul] using (cSeq_mem_Icc_and_mem_Icc ha h₃ h₄ (k := k) (by lia)).1

theorem cSeq_mem_Icc_of_odd (ha : a < -1) (h₃ : cSeq a 3 < 0) (h₄ : 0 < cSeq a 4) {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) :
    cSeq a n ∈ Set.Icc a (cSeq a 3) := by
  obtain ⟨k, rfl⟩ := ho
  exact (cSeq_mem_Icc_and_mem_Icc ha h₃ h₄ (by lia)).2

/-- For `a ≤ -2`, `c_n² - c_n + a + 1 ≥ (a + 1)² > 0` (`n ≥ 1`), as `c_n ≥ -a ≥ 2`. -/
theorem cSeq_sq_sub_cSeq_add_pos_of_le_neg_two (ha : a ≤ -2) {n : ℕ} (hn : 1 ≤ n) :
    0 < cSeq a n ^ 2 - cSeq a n + a + 1 := by
  have h := neg_le_cSeq_of_le_neg_two ha hn
  linear_combination mul_nonneg (by linarith : 0 ≤ cSeq a n + a)
    (by linarith : 0 ≤ cSeq a n - a - 1) + pow_pos (by linarith : 0 < -(a + 1)) 2

/-- For `a > -1`, `c_n² - c_n + a + 1 > 0` (`n ≥ 2`): for `a ≥ 0` as `x² - x + 1 > 0`, and for
`a < 0` as `c_n < 0`. -/
theorem cSeq_sq_sub_cSeq_add_pos_of_neg_one_lt (ha : -1 < a) {n : ℕ} (hn : 2 ≤ n) :
    0 < cSeq a n ^ 2 - cSeq a n + a + 1 := by
  rcases le_or_gt 0 a with h | h
  · linarith [sq_nonneg (cSeq a n), sq_nonneg (cSeq a n - 1)]
  · linarith [cSeq_neg_of_neg_one_lt ha h hn, sq_nonneg (cSeq a n)]

/-- In the window `a < -1`, `c_3 < 0 < c_4`, `c_n² - c_n + a + 1 > 0` for odd `n ≥ 3`: there
`c_n ≤ c_3 < -1`, and `a > -2`. -/
theorem cSeq_sq_sub_cSeq_add_pos_of_odd (ha : a < -1) (h₃ : cSeq a 3 < 0) (h₄ : 0 < cSeq a 4)
    {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    0 < cSeq a n ^ 2 - cSeq a n + a + 1 := by
  have hc := (cSeq_mem_Icc_of_odd ha h₃ h₄ hn ho).2.trans_lt (cSeq_three_lt_neg_one ha h₃ h₄)
  have ha₂ : -2 < a := lt_of_not_ge fun h ↦
    h₃.not_ge ((neg_nonneg.mpr (by linarith)).trans (neg_le_cSeq_of_le_neg_two h (by norm_num)))
  linarith [sq_nonneg (cSeq a n)]

end

end QuadraticIterates
