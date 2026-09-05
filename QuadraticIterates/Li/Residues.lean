/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Main

import QuadraticIterates.Mathlib.Data.Int.Order.Units

/-!
# Residues of the rescaled sequence for negative `a`

For `a < 0`, the rescaled polynomial is `normPoly a = -a X² - 1`, and its `γ`-sequence starts
`γ_1 = 1`, `γ_2 = -a - 1`. The residues of `γ_n` modulo `8` and `4` follow from the `2`-periodicity
lemmas of `QuadraticIterates.ArchMath1992.Sequences`:

* `gammaSeq_normPoly_zmod_eight_of_even`: for even `a`, `γ_n ≡ -a - 1 mod 8` for all `n ≥ 2`;
* `gammaSeq_normPoly_zmod_eight_of_emod_four_eq_one`: for `a ≡ 1 mod 4`, `γ_n mod 8` alternates
  between `-a - 1` (even `n`) and `3` (odd `n`) from `n = 2` on;
* `gammaSeq_normPoly_zmod_four_of_emod_four_eq_three`: for `a ≡ 3 mod 4`, `γ_n mod 4` alternates
  between `0` (even `n`) and `3` (odd `n`) from `n = 2` on.

These are the residue computations behind the results of H.-C. Li extending the Section 3 theorem
of the paper to further values of `a`; see `QuadraticIterates.Li`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

variable {a : ℤ}

/-- `g(0) = sgn a` is a unit for the rescaled polynomial `g = normPoly a`, `a ≠ 0`. -/
lemma isUnit_eval_zero_normPoly (ha : a ≠ 0) : IsUnit ((normPoly a).eval 0) := by
  simpa using IsUnit.of_pow_eq_one (Int.sign_sq_of_ne_zero ha) two_ne_zero

/-- For `a < 0`, the rescaled polynomial is `normPoly a = -a X² - 1`. -/
lemma normPoly_of_neg (ha : a < 0) : normPoly a = C (-a) * X ^ 2 - 1 := by
  rw [normPoly, abs_of_neg ha, Int.sign_eq_neg_one_of_neg ha, C_neg, C_neg, C_1, sub_eq_add_neg]

lemma eval_normPoly_of_neg (ha : a < 0) (x : ℤ) : (normPoly a).eval x = -a * x ^ 2 - 1 := by
  simp [normPoly_of_neg ha]

/-- The image of `normPoly a`, `a < 0`, in a commutative ring `S`, evaluated at `x`:
`-a x² - 1`. -/
lemma eval_map_normPoly_of_neg (ha : a < 0) {S : Type*} [CommRing S] (x : S) :
    ((normPoly a).map (Int.castRingHom S)).eval x = -(a : S) * x ^ 2 - 1 := by
  simp [normPoly_of_neg ha]

lemma gammaSeq_normPoly_two (ha : a < 0) : gammaSeq (normPoly a) a.sign 2 = -a - 1 := by
  rw [gammaSeq_succ _ _ le_rfl, gammaSeq_normPoly_one ha.ne, eval_normPoly, abs_of_neg ha,
    Int.sign_eq_neg_one_of_neg ha]
  ring

/-- For `a < 0`, the `γ`-sequence of `normPoly a` in `ZMod m` is the `γ`-sequence of
`-a X² - 1` with `ε = -1`. -/
lemma intCast_gammaSeq_normPoly (ha : a < 0) (m : ℕ) (n : ℕ) :
    ((gammaSeq (normPoly a) a.sign n : ℤ) : ZMod m)
      = gammaSeq ((normPoly a).map (Int.castRingHom (ZMod m))) (-1) n := by
  rw [intCast_gammaSeq, Int.sign_eq_neg_one_of_neg ha, Int.cast_neg, Int.cast_one]

section

variable (ha : a < 0)
include ha

lemma eval_zero_map_normPoly_sq (S : Type*) [CommRing S] :
    ((normPoly a).map (Int.castRingHom S)).eval 0 ^ 2 = 1 := by
  rw [eval_map_normPoly_of_neg ha]
  ring

lemma gammaSeq_map_normPoly_one (S : Type*) [CommRing S] :
    gammaSeq ((normPoly a).map (Int.castRingHom S)) (-1) 1 = 1 := by
  rw [gammaSeq_one, eval_map_normPoly_of_neg ha]
  ring

end

/-- **Lemma 2.2 of [Li 2021], residues:** for even `a < 0`, `γ_n ≡ -a - 1 mod 8` for all `n ≥ 2`
(the residue `-a - 1` is odd, so its square is `1 mod 8`, and `g(-a - 1) ≡ -a - 1`). -/
theorem gammaSeq_normPoly_zmod_eight_of_even (ha : a < 0) (ha2 : Even a) :
    ∀ n ≥ 2, ((gammaSeq (normPoly a) a.sign n : ℤ) : ZMod 8) = ((-a - 1 : ℤ) : ZMod 8) := by
  intro n hn
  obtain ⟨b, rfl⟩ := ha2
  have h1 : (((normPoly (b + b)).map (Int.castRingHom (ZMod 8))).eval 1) ^ 2 = 1 := by
    rw [eval_map_normPoly_of_neg ha]
    push_cast
    generalize (b : ZMod 8) = y
    decide +revert
  rw [intCast_gammaSeq_normPoly ha, gammaSeq_eq_eval_one ((evenPoly_normPoly _).map _) (by ring)
    (eval_zero_map_normPoly_sq ha _) h1 n hn, eval_map_normPoly_of_neg ha]
  push_cast
  ring

/-- **Lemma 2.2 of [Li 2021], residues:** for `a < 0` with `a ≡ 1 mod 4`, the sequence
`γ_n mod 8` alternates from `n = 2` on between `-a - 1` (even `n`) and `3` (odd `n`). -/
theorem gammaSeq_normPoly_zmod_eight_of_emod_four_eq_one (ha : a < 0) (ha4 : a % 4 = 1) :
    ∀ n ≥ 2, ((gammaSeq (normPoly a) a.sign n : ℤ) : ZMod 8)
      = if Even n then ((-a - 1 : ℤ) : ZMod 8) else 3 := by
  intro n hn
  set g' := (normPoly a).map (Int.castRingHom (ZMod 8))
  have hα : (a : ZMod 8) = 5 ∨ (a : ZMod 8) = 1 := by
    rcases (show a % 8 = 5 ∨ a % 8 = 1 by omega) with h | h
    · exact .inl ((ZMod.intCast_eq_intCast_iff' a 5 8).mpr h)
    · exact .inr ((ZMod.intCast_eq_intCast_iff' a 1 8).mpr h)
  have h2 : gammaSeq g' (-1) 2 = -(a : ZMod 8) - 1 := by
    rw [gammaSeq_succ _ _ le_rfl, gammaSeq_map_normPoly_one ha, eval_map_normPoly_of_neg ha]
    ring
  have h3 : gammaSeq g' (-1) 3 = 3 := by
    rw [gammaSeq_succ _ _ one_le_two, h2, eval_map_normPoly_of_neg ha]
    rcases hα with h | h <;> rw [h] <;> decide
  have h4 : gammaSeq g' (-1) (2 + 2) = gammaSeq g' (-1) 2 := by
    rw [gammaSeq_succ _ _ (by lia), h3, h2, eval_map_normPoly_of_neg ha]
    rcases hα with h | h <;> rw [h] <;> decide
  rw [intCast_gammaSeq_normPoly ha, gammaSeq_eq_ite_even_of_add_two_eq g' one_le_two h4 n hn, h2,
    h3]
  push_cast
  simp [Nat.even_add]

/-- **Lemma 3.1 of [Li 2020], residues:** for `a < 0` with `a ≡ 3 mod 4`, the sequence
`γ_n mod 4` alternates from `n = 2` on between `0` (even `n`) and `3` (odd `n`). -/
theorem gammaSeq_normPoly_zmod_four_of_emod_four_eq_three (ha : a < 0) (ha4 : a % 4 = 3) :
    ∀ n ≥ 2, ((gammaSeq (normPoly a) a.sign n : ℤ) : ZMod 4) = if Even n then 0 else 3 := by
  intro n hn
  have hα : (a : ZMod 4) = 3 := (ZMod.intCast_eq_intCast_iff' a 3 4).mpr ha4
  rw [intCast_gammaSeq_normPoly ha, gammaSeq_eq_ite_even_of_eval_one_eq_zero
    ((evenPoly_normPoly _).map _) (eval_zero_map_normPoly_sq ha _) (gammaSeq_map_normPoly_one ha _)
    (by rw [eval_map_normPoly_of_neg ha, hα]; decide) n hn, eval_map_normPoly_of_neg ha,
    zero_pow two_ne_zero, mul_zero, zero_sub]
  split_ifs <;> decide

/-- For `a < 0` with `a ≡ 1 mod 4` and odd `k ≥ 3`, `γ_k + γ_{k+2} ≡ 6 mod 8`. -/
theorem gammaSeq_normPoly_add_two_emod_eight (ha : a < 0) (ha4 : a % 4 = 1) {k : ℕ} (hko : Odd k)
    (hk : 3 ≤ k) :
    (gammaSeq (normPoly a) a.sign k + gammaSeq (normPoly a) a.sign (k + 2)) % 8 = 6 := by
  have h := gammaSeq_normPoly_zmod_eight_of_emod_four_eq_one ha ha4
  have hk1 := h k (by lia)
  have hk2 := h (k + 2) (by lia)
  rw [if_neg (Nat.not_even_iff_odd.mpr hko)] at hk1
  rw [if_neg (Nat.not_even_iff_odd.mpr (by grind))] at hk2
  have := (ZMod.intCast_eq_intCast_iff' _ 3 8).mp hk1
  have := (ZMod.intCast_eq_intCast_iff' _ 3 8).mp hk2
  omega

/-- For `a < 0` with `a ≡ 1 mod 4` and even `k ≥ 2`, `γ_k ≡ 2 mod 4`. -/
theorem gammaSeq_normPoly_emod_four_of_even (ha : a < 0) (ha4 : a % 4 = 1) {k : ℕ} (hke : Even k)
    (hk : 2 ≤ k) : gammaSeq (normPoly a) a.sign k % 4 = 2 := by
  have h := gammaSeq_normPoly_zmod_eight_of_emod_four_eq_one ha ha4 k hk
  rw [if_pos hke] at h
  have := (ZMod.intCast_eq_intCast_iff' _ _ 8).mp h
  omega

/-- For `a < 0` with `a ≡ 3 mod 4` and `k ≥ 2`, `γ_k + γ_{k+1} ≡ 3 mod 4`. -/
theorem gammaSeq_normPoly_add_succ_emod_four (ha : a < 0) (ha4 : a % 4 = 3) {k : ℕ} (hk : 2 ≤ k) :
    (gammaSeq (normPoly a) a.sign k + gammaSeq (normPoly a) a.sign (k + 1)) % 4 = 3 := by
  have h := gammaSeq_normPoly_zmod_four_of_emod_four_eq_three ha ha4
  have hk1 := h k hk
  have hk2 := h (k + 1) (by lia)
  simp only [Nat.even_add_one] at hk2
  rcases Nat.even_or_odd k with he | ho
  · rw [if_pos he] at hk1
    rw [if_neg (not_not.mpr he)] at hk2
    have := (ZMod.intCast_eq_intCast_iff' _ 0 4).mp hk1
    have := (ZMod.intCast_eq_intCast_iff' _ 3 4).mp hk2
    omega
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho)] at hk1
    rw [if_pos (Nat.not_even_iff_odd.mpr ho)] at hk2
    have := (ZMod.intCast_eq_intCast_iff' _ 3 4).mp hk1
    have := (ZMod.intCast_eq_intCast_iff' _ 0 4).mp hk2
    omega

end QuadraticIterates
