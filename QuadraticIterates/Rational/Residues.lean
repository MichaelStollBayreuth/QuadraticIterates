/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.Reflection

import Mathlib.Data.Fintype.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# The 2-adic classes: residues of the reflection numerators

For a rational parameter `a = r/s` with sign `ε`, the numerator `N_k = w_k s^(2^(k-1)) + w_{k+1}`
of `γ_k + γ_{k+1}` (`QuadraticIterates.reflNum`) is, for every `k ≥ 2`, `≡ 6 mod 8` or
`≡ 3 mod 4` in the *2-adic classes* `QuadraticIterates.TwoAdicClass`: `s` odd with `r ≡ 1` or
`r + εs ≡ 3 mod 4`, or `s` even with `r ≡ 3 mod 4`. For odd `s` everything is decided modulo `8`,
where the `γ`-sequence of `a X² + ε` is `2`-periodic from index `2` on for every `a`
(`QuadraticIterates.reflNum_emod_of_odd`); for even `s`, `w_n ≡ r mod 8` for `n ≥ 3`
(`QuadraticIterates.intCast_wSeq_zmod_eight_of_even`,
`QuadraticIterates.reflNum_emod_four_of_even`). Hence `-1` is not a square modulo `N_k`
(`QuadraticIterates.not_isSquare_neg_one_zmod_reflNum`), and the reflection lemma with the modulus
`N_k` makes `β_n` a non-square for every `n ≥ 2` with `n / rad n ≥ 2`
(`QuadraticIterates.not_isSquare_betaInt_of_two_le`).

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

variable {r s ε : ℤ}

/-! ### Residues modulo 8 -/

/-- The square of an odd integer is `1` in `ZMod 8`. -/
lemma intCast_sq_zmod_eight_of_odd {x : ℤ} (hx : x % 2 = 1) : (x : ZMod 8) ^ 2 = 1 := by
  rcases (show x % 8 = 1 % 8 ∨ x % 8 = 3 % 8 ∨ x % 8 = 5 % 8 ∨ x % 8 = 7 % 8 by lia)
    with h | h | h | h <;> rw [(ZMod.intCast_eq_intCast_iff' x _ 8).mpr h] <;> decide

lemma isUnit_intCast_zmod_eight_of_odd {x : ℤ} (hx : x % 2 = 1) : IsUnit (x : ZMod 8) :=
  .of_mul_eq_one _ (sq (x : ZMod 8) ▸ intCast_sq_zmod_eight_of_odd hx)

/-- A power `≥ 3` of an even integer is `0` in `ZMod 8`. -/
lemma intCast_pow_zmod_eight_of_even {x : ℤ} (hx : x % 2 = 0) {m : ℕ} (hm : 3 ≤ m) :
    (x : ZMod 8) ^ m = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, x = 2 * t := ⟨x / 2, by lia⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  push_cast
  rw [mul_pow, show (2 : ZMod 8) ^ 3 = 0 by decide, zero_mul, zero_mul]

/-- For odd `s`, `s^(2^k - 1) = s` in `ZMod 8` (`k ≥ 1`): the exponent is odd and `s² = 1`. -/
lemma intCast_pow_two_pow_sub_one_zmod_eight_of_odd (hs : s % 2 = 1) {k : ℕ} (hk : 1 ≤ k) :
    (s : ZMod 8) ^ (2 ^ k - 1) = s := by
  rw [two_pow_sub_one_eq hk, pow_succ, pow_mul, intCast_sq_zmod_eight_of_odd hs, one_pow, one_mul]

section zmod8

variable {u : ZMod 8}

local notation "g8" => (C ((r : ZMod 8) * u) * X ^ 2 + C (ε : ZMod 8) : (ZMod 8)[X])
local notation "γ8" => gammaSeq g8 (ε : ZMod 8)

private lemma gammaSeq_zmod_eight_one (hε : ε ^ 2 = 1) : γ8 1 = 1 := by
  have he : (ε : ZMod 8) ^ 2 = 1 := by rw [← Int.cast_pow, hε, Int.cast_one]
  rw [gammaSeq_one, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_C]
  linear_combination he

private lemma gammaSeq_zmod_eight_two (hε : ε ^ 2 = 1) : γ8 2 = (r : ZMod 8) * u + ε := by
  rw [gammaSeq_succ _ _ le_rfl, gammaSeq_zmod_eight_one hε]
  simp

private lemma gammaSeq_zmod_eight_three (hε : ε ^ 2 = 1) :
    γ8 3 = (r : ZMod 8) * u * ((r : ZMod 8) * u + ε) ^ 2 + ε := by
  rw [gammaSeq_succ _ _ one_le_two, gammaSeq_zmod_eight_two hε]
  simp

/-- In `ZMod 8`, `γ_4 = γ_2` for every `a` and every `ε` with `ε² = 1`: the sequence is
`2`-periodic from index `2` on. -/
private lemma gammaSeq_zmod_eight_add_two_eq (hε : ε ^ 2 = 1) : γ8 (2 + 2) = γ8 2 := by
  have he : (ε : ZMod 8) ^ 2 = 1 := by rw [← Int.cast_pow, hε, Int.cast_one]
  rw [gammaSeq_succ _ _ (by lia), gammaSeq_zmod_eight_three hε, gammaSeq_zmod_eight_two hε]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  generalize (r : ZMod 8) * u = x
  generalize (ε : ZMod 8) = e at he ⊢
  revert x e
  decide

/-- For odd `s` and `k ≥ 2`, `N_k ≡ s (γ_2 + γ_3) mod 8`, with `γ` the sequence of `a X² + ε`
over `ZMod 8`, `a = r s⁻¹`. -/
private lemma intCast_reflNum_zmod_eight (hs : s % 2 = 1) (hu : (s : ZMod 8) * u = 1)
    (hε : ε ^ 2 = 1) {k : ℕ} (hk : 2 ≤ k) : (reflNum r s ε k : ZMod 8) = s * (γ8 2 + γ8 3) := by
  have hp := gammaSeq_eq_ite_even_of_add_two_eq g8 one_le_two (gammaSeq_zmod_eight_add_two_eq hε)
  have hsum : γ8 k + γ8 (k + 1) = γ8 2 + γ8 3 := by
    have h : Even (k + 1 + 2) ↔ ¬Even (k + 2) := by
      rw [show k + 1 + 2 = k + 2 + 1 by ring, Nat.even_add_one]
    rw [hp k hk, hp (k + 1) (by lia)]
    grind
  have hexp : 2 ^ (k - 1) - 1 + 2 ^ (k - 1) = 2 ^ k - 1 := by
    rw [two_pow_sub_one_eq (by lia : 1 ≤ k)]
    have := Nat.one_le_two_pow (n := k - 1)
    lia
  rw [reflNum]
  push_cast
  rw [intCast_wSeq hu hε, intCast_wSeq hu hε, Nat.add_sub_cancel, mul_right_comm, ← pow_add, hexp,
    intCast_pow_two_pow_sub_one_zmod_eight_of_odd hs (by lia), ← mul_add, hsum]

/-- The class condition for odd `s` in `ZMod 8`. -/
private lemma intCast_zmod_eight_of_class (hclass : r % 4 = 1 ∨ (r + ε * s) % 4 = 3) :
    (r : ZMod 8) = ((1 : ℤ) : ZMod 8) ∨ (r : ZMod 8) = ((5 : ℤ) : ZMod 8) ∨
      ((r + ε * s : ℤ) : ZMod 8) = ((3 : ℤ) : ZMod 8) ∨
        ((r + ε * s : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8) := by
  rcases (show r % 8 = 1 % 8 ∨ r % 8 = 5 % 8 ∨ (r + ε * s) % 8 = 3 % 8 ∨
      (r + ε * s) % 8 = 7 % 8 by lia) with h | h | h | h
  · exact .inl ((ZMod.intCast_eq_intCast_iff' _ _ 8).mpr h)
  · exact .inr (.inl ((ZMod.intCast_eq_intCast_iff' _ _ 8).mpr h))
  · exact .inr (.inr (.inl ((ZMod.intCast_eq_intCast_iff' _ _ 8).mpr h)))
  · exact .inr (.inr (.inr ((ZMod.intCast_eq_intCast_iff' _ _ 8).mpr h)))

/-- `N ≡ 6 mod 8` or `N ≡ 3 mod 4` from the residue of `N` in `ZMod 8`. -/
private lemma emod_of_intCast_zmod_eight {N : ℤ} (h8 : (N : ZMod 8) = ((6 : ℤ) : ZMod 8) ∨
    (N : ZMod 8) = ((3 : ℤ) : ZMod 8) ∨ (N : ZMod 8) = ((7 : ℤ) : ZMod 8)) :
    N % 8 = 6 ∨ N % 4 = 3 := by
  rcases h8 with h8 | h8 | h8 <;> have := (ZMod.intCast_eq_intCast_iff' _ _ 8).mp h8 <;> lia

/-- **The 2-adic classes, odd `s`.** If `s` is odd and `r ≡ 1 mod 4` or `r + εs ≡ 3 mod 4`, then
`N_k ≡ 6 mod 8` or `N_k ≡ 3 mod 4` for every `k ≥ 2`: modulo `8`, `N_k ≡ s(γ_2 + γ_3)` with
`γ_2 = a + ε`, `γ_3 = a γ_2² + ε`, `a = r s⁻¹ = rs`, a finite check. -/
theorem reflNum_emod_of_odd (hs : s % 2 = 1) (hε : ε ^ 2 = 1)
    (hclass : r % 4 = 1 ∨ (r + ε * s) % 4 = 3) {k : ℕ} (hk : 2 ≤ k) :
    reflNum r s ε k % 8 = 6 ∨ reflNum r s ε k % 4 = 3 := by
  have hs2 := intCast_sq_zmod_eight_of_odd hs
  have he : (ε : ZMod 8) ^ 2 = 1 := by rw [← Int.cast_pow, hε, Int.cast_one]
  have h := intCast_reflNum_zmod_eight (r := r) (u := (s : ZMod 8)) hs (by rw [← sq, hs2]) hε hk
  have hc := intCast_zmod_eight_of_class (s := s) (ε := ε) hclass
  rw [gammaSeq_zmod_eight_three hε, gammaSeq_zmod_eight_two hε] at h
  refine emod_of_intCast_zmod_eight ?_
  rw [h]
  push_cast at hc ⊢
  generalize (r : ZMod 8) = x at hc ⊢
  generalize (s : ZMod 8) = y at hs2 hc ⊢
  generalize (ε : ZMod 8) = e at he hc ⊢
  revert x y e
  decide

end zmod8

/-! ### Even `s` -/

/-- An integer coprime to an even integer is odd. -/
private lemma emod_two_eq_one_of_isCoprime {x y : ℤ} (h : IsCoprime x y) (hy : y % 2 = 0) :
    x % 2 = 1 := by
  by_contra hx
  have := h.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero (by lia)) (Int.dvd_of_emod_eq_zero hy)
  rw [Int.isUnit_iff] at this
  lia

/-- For even `s` (and `r` coprime to `s`), `w_n` is odd, so `w_n² = 1` in `ZMod 8`. -/
private lemma intCast_wSeq_sq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) {n : ℕ}
    (hn : 1 ≤ n) : (wSeq r s ε n : ZMod 8) ^ 2 = 1 :=
  intCast_sq_zmod_eight_of_odd (emod_two_eq_one_of_isCoprime (isCoprime_wSeq_right hrs hn) hs)

/-- For even `s` (and `r` coprime to `s`), `w_n ≡ r mod 8` for all `n ≥ 3`: `w_n` is odd, so
`w_n² ≡ 1`, and `8 ∣ s^(2^n - 1)` for `n ≥ 2`. -/
theorem intCast_wSeq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) :
    ∀ n ≥ 3, (wSeq r s ε n : ZMod 8) = r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [wSeq_succ r s ε one_le_two]
    push_cast
    rw [intCast_wSeq_sq_zmod_eight_of_even hs hrs one_le_two,
      intCast_pow_zmod_eight_of_even hs (by norm_num)]
    ring
  | succ n hn ih =>
    rw [wSeq_succ r s ε (by lia)]
    push_cast
    rw [intCast_wSeq_sq_zmod_eight_of_even hs hrs (by lia), intCast_pow_zmod_eight_of_even hs (by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by lia : 2 ≤ n)
      lia)]
    ring

/-- **The 2-adic classes, even `s`.** If `s` is even and `r ≡ 3 mod 4`, then `N_k ≡ 3 mod 4` for
every `k ≥ 2`: `4 ∣ s^(2^(k-1))` and `w_{k+1} ≡ r mod 8`. -/
theorem reflNum_emod_four_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) (hr : r % 4 = 3)
    {k : ℕ} (hk : 2 ≤ k) : reflNum r s ε k % 4 = 3 := by
  have h1 := (ZMod.intCast_eq_intCast_iff' _ _ 8).mp
    (intCast_wSeq_zmod_eight_of_even (ε := ε) hs hrs (k + 1) (by lia))
  have h4 : (4 : ℤ) ∣ wSeq r s ε k * s ^ 2 ^ (k - 1) := by
    refine Dvd.dvd.mul_left ((pow_dvd_pow 2 (by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by lia : 1 ≤ k - 1)
      lia : 2 ≤ 2 ^ (k - 1))).trans (pow_dvd_pow_of_dvd (Int.dvd_of_emod_eq_zero hs) _)) _
  rw [reflNum]
  lia

/-! ### The corollary: `β_n` for `n` not squarefree -/

/-- The 2-adic classes (C⁺) (for `ε = 1`) and (C⁻) (for `ε = -1`, `|r|` in place of `r`), as a
condition on `r`, `s`, `ε`: `s` odd with `r ≡ 1 mod 4` or `r + εs ≡ 3 mod 4`, or `s` even with
`r ≡ 3 mod 4`. -/
def TwoAdicClass (r s ε : ℤ) : Prop :=
  (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + ε * s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3)

/-- In the 2-adic classes, `-1` is not a square modulo `N_k` for every `k ≥ 2`. -/
theorem not_isSquare_neg_one_zmod_reflNum (hs : 0 < s) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, 0 < wSeq r s ε n) (hc : TwoAdicClass r s ε) {k : ℕ} (hk : 2 ≤ k) :
    ¬IsSquare (-1 : ZMod (reflNum r s ε k).natAbs) :=
  Int.not_isSquare_neg_one_zmod_natAbs_of_emod (reflNum_pos hs hw (by lia)).le
    (hc.elim (fun h ↦ reflNum_emod_of_odd h.1 hε h.2 hk)
      fun h ↦ .inr (reflNum_emod_four_of_even h.1 hrs h.2 hk))

/-- **Corollary (non-squarefree levels).** In the 2-adic classes, `β_n` is not a square for every
`n ≥ 2` with `k = n / rad n ≥ 2`: the reflection lemma with the modulus `N_k` itself. -/
theorem not_isSquare_betaInt_of_two_le (hs : 0 < s) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, 0 < wSeq r s ε n) (hc : TwoAdicClass r s ε) {n k : ℕ} (hn : 2 ≤ n)
    (hk : n = k * radical n) (hk2 : 2 ≤ k) : ¬IsSquare (betaInt r s ε n) := by
  obtain ⟨u, hu⟩ := ((ZMod.coe_int_isUnit_iff_isCoprime s (reflNum r s ε k).natAbs).mpr
    (by rw [Int.natAbs_of_nonneg (reflNum_pos hs hw (one_le_two.trans hk2)).le]
        exact isCoprime_reflNum_right hrs (one_le_two.trans hk2))).exists_right_inv
  exact not_isSquare_betaInt_of_dvd_add_succ_of_two_le hs.ne' hrs hε (fun n hn ↦ (hw n hn).ne')
    hn rfl hk hk2 hu (Int.natAbs_dvd.mpr dvd_rfl)
    (not_isSquare_neg_one_zmod_reflNum hs hrs hε hw hc hk2)

/-! ### The primes of `s` -/

section dvd

variable {M : ℕ}

/-- Modulo a divisor `M` of `s`, `w_n ≡ r^(2^(n-1) - 1)`: the term `ε s^(2^n - 1)` vanishes. -/
lemma intCast_wSeq_zmod_of_dvd (hM : (M : ℤ) ∣ s) :
    ∀ n ≥ 1, (wSeq r s ε n : ZMod M) = (r : ZMod M) ^ (2 ^ (n - 1) - 1) := by
  have hs : (s : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hM
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [wSeq_succ r s ε hn]
    push_cast
    rw [ih, hs, zero_pow (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (by lia))), mul_zero,
      add_zero, two_pow_sub_one_eq hn]
    ring

lemma intCast_prod_wSeq_zmod_of_dvd (hM : (M : ℤ) ∣ s) {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) :
    ((∏ t ∈ S, wSeq r s ε t : ℤ) : ZMod M) = (r : ZMod M) ^ ∑ t ∈ S, (2 ^ (t - 1) - 1) := by
  push_cast
  rw [Finset.prod_congr rfl fun t ht ↦ intCast_wSeq_zmod_of_dvd hM t (hS t ht),
    Finset.prod_pow_eq_pow_sum]

/-- For squarefree `n` and `M ∣ s`, if `β_n` is a square then `r^F` is a square modulo `M`,
`F = ∑_{t ∣ n} (2^(t-1) - 1)` the twist exponent: `β_n = P/Q` with `P ≡ r^(F⁺)`, `Q ≡ r^(F⁻)`. -/
private lemma isSquare_intCast_pow_of_isSquare_betaInt (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hM : (M : ℤ) ∣ s) (hsq : IsSquare (betaInt r s ε n)) :
    IsSquare ((r : ZMod M) ^ ∑ t ∈ n.divisors, (2 ^ (t - 1) - 1)) := by
  have hβ := intCast_betaInt_eq_div hs hrs hε hw (by lia)
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm
  simp only [one_mul] at hβ
  have hpos (S : Finset ℕ) (hS : S ⊆ n.divisors) : ∀ t ∈ S, 1 ≤ t :=
    fun t ht ↦ Nat.pos_of_mem_divisors (hS ht)
  have key := ZMod.isSquare_mul_of_isSquare_div
    (x := (r : ZMod M) ^ ∑ t ∈ n.divisors with μ (n / t) = 1, (2 ^ (t - 1) - 1))
    (y := (r : ZMod M) ^ ∑ t ∈ n.divisors with μ (n / t) = -1, (2 ^ (t - 1) - 1))
    (by rw [intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _)),
      intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _))])
    (by rw [intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _))]
        exact (ZMod.isUnit_intCast_of_isCoprime_of_dvd hrs hM).pow _)
    (hβ ▸ Rat.isSquare_intCast_iff.mpr hsq)
  rwa [← pow_add, ← Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia),
    hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one] at key

/-- **The primes of `s`.** If `M ∣ s` and `r` is not a square modulo `M`, then `β_n` is not a
square for every squarefree `n ≥ 2`: modulo `M`, `β_n ≡ r^F · (unit)²` with the odd twist exponent
`F = ∑_{t ∣ n} (2^(t-1) - 1)`. -/
theorem not_isSquare_betaInt_of_squarefree_of_dvd_of_not_isSquare (hs : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hM : (M : ℤ) ∣ s) (hnsq : ¬IsSquare (r : ZMod M)) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have key := isSquare_intCast_pow_of_isSquare_betaInt hs hrs hε hw hn hsf hM hsq
  obtain ⟨j, hj⟩ := odd_sum_two_pow_sub_one_of_squarefree hsf (by lia)
  rw [hj, pow_succ', pow_mul',
    ((ZMod.isUnit_intCast_of_isCoprime_of_dvd hrs hM).pow j).isSquare_mul_sq_iff] at key
  exact hnsq key

end dvd

/-! ### Squarefree levels for even `s` -/

/-- An odd integer `≢ 1 mod 8` is not a square modulo `8`. -/
lemma not_isSquare_intCast_zmod_eight_of_odd_of_emod_ne_one {x : ℤ} (hx : x % 2 = 1)
    (h1 : x % 8 ≠ 1) : ¬IsSquare (x : ZMod 8) := by
  rcases (show x % 8 = 3 % 8 ∨ x % 8 = 5 % 8 ∨ x % 8 = 7 % 8 by lia) with h | h | h <;>
    rw [(ZMod.intCast_eq_intCast_iff' x _ 8).mpr h] <;> decide

/-- For squarefree `n`, if `β_n` is a square then so is `∏_{t ∣ n} w_t` modulo `8`: the product of
the numerator and the denominator of `β_n`. -/
private lemma isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hsq : IsSquare (betaInt r s ε n)) :
    IsSquare ((∏ t ∈ n.divisors, wSeq r s ε t : ℤ) : ZMod 8) := by
  have hβ := intCast_betaInt_eq_div hs0 hrs hε hw (by lia)
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm
  simp only [one_mul] at hβ
  have key := (Int.isSquare_mul_of_isSquare_div (hβ ▸ Rat.isSquare_intCast_iff.mpr hsq)).map
    (Int.castRingHom (ZMod 8))
  rwa [Int.coe_castRingHom, ← Finset.prod_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia),
    hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one] at key

/-- The product `∏_{t ∣ n} w_t` modulo `8` for even `s`: the factors with `t ≥ 3` are `r`. -/
private lemma intCast_prod_wSeq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s)
    (n : ℕ) : ((∏ t ∈ n.divisors, wSeq r s ε t : ℤ) : ZMod 8) =
      (∏ t ∈ n.divisors with t ≤ 2, (wSeq r s ε t : ZMod 8)) *
        (r : ZMod 8) ^ (n.divisors.filter fun t ↦ ¬t ≤ 2).card := by
  push_cast
  rw [← Finset.prod_filter_mul_prod_filter_not n.divisors (· ≤ 2), ← Finset.prod_const]
  congr 1
  exact Finset.prod_congr rfl fun t ht ↦
    intCast_wSeq_zmod_eight_of_even hs hrs t (by have := (Finset.mem_filter.mp ht).2; lia)

private lemma filter_divisors_le_two_of_odd {n : ℕ} (hn : Odd n) :
    (n.divisors.filter fun t ↦ t ≤ 2) = {1} := by
  ext t
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  refine ⟨fun ⟨⟨ht, hn0⟩, h2⟩ ↦ ?_, fun h ↦ h ▸ ⟨⟨one_dvd n, hn.pos.ne'⟩, one_le_two⟩⟩
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by lia) with rfl | rfl | rfl
  · exact absurd (zero_dvd_iff.mp ht) hn0
  · rfl
  · have := Nat.mod_eq_zero_of_dvd ht
    have := Nat.odd_iff.mp hn
    lia

private lemma filter_divisors_le_two_of_even {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) :
    (n.divisors.filter fun t ↦ t ≤ 2) = {1, 2} := by
  ext t
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun ⟨⟨ht, _⟩, h2⟩ ↦ ?_, fun h ↦ ?_⟩
  · rcases (show t = 0 ∨ t = 1 ∨ t = 2 by lia) with rfl | rfl | rfl
    · exact absurd (zero_dvd_iff.mp ht) hn0
    · exact .inl rfl
    · exact .inr rfl
  · rcases h with rfl | rfl
    · exact ⟨⟨one_dvd n, hn0⟩, one_le_two⟩
    · exact ⟨⟨even_iff_two_dvd.mp hn, hn0⟩, le_rfl⟩

-- The number of divisors `t > 2` of an odd squarefree `n ≥ 2` is odd: `τ(n) - 1`.
private lemma odd_card_filter_divisors_of_odd {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hno : Odd n) : Odd (n.divisors.filter fun t ↦ ¬t ≤ 2).card := by
  have hc := Finset.card_filter_add_card_filter_not (s := n.divisors) fun t ↦ t ≤ 2
  rw [filter_divisors_le_two_of_odd hno, Finset.card_singleton,
    card_divisors_eq_two_mul_of_squarefree hsf (by lia)] at hc
  exact ⟨(n.divisors.filter fun t ↦ μ (n / t) = 1).card - 1, by lia⟩

-- The number of divisors `t > 2` of an even squarefree `n` is even: `τ(n) - 2`.
private lemma even_card_filter_divisors_of_even {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hne : Even n) : Even (n.divisors.filter fun t ↦ ¬t ≤ 2).card := by
  have hc := Finset.card_filter_add_card_filter_not (s := n.divisors) fun t ↦ t ≤ 2
  rw [filter_divisors_le_two_of_even (by lia) hne, Finset.card_pair one_lt_two.ne,
    card_divisors_eq_two_mul_of_squarefree hsf (by lia)] at hc
  exact ⟨(n.divisors.filter fun t ↦ μ (n / t) = 1).card - 1, by lia⟩

/-- **Even `s`, odd squarefree `n ≥ 3`.** If `s` is even and `r ≡ 3 mod 4`, then `β_n` is not a
square: modulo `8`, `∏_{t ∣ n} w_t = r^(τ(n) - 1)` with `τ(n) - 1` odd, and `r` is not a square
modulo `8`. -/
theorem not_isSquare_betaInt_of_squarefree_of_odd_of_even (hs : s % 2 = 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hno : Odd n) (hr : r % 4 = 3) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have key := isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt hs0 hrs hε hw hn hsf hsq
  obtain ⟨j, hj⟩ := odd_card_filter_divisors_of_odd hn hsf hno
  have hr2 : r % 2 = 1 := emod_two_eq_one_of_isCoprime hrs hs
  rw [intCast_prod_wSeq_zmod_eight_of_even hs hrs, filter_divisors_le_two_of_odd hno,
    Finset.prod_singleton, wSeq_one, Int.cast_one, one_mul, hj, pow_succ', pow_mul',
    ((isUnit_intCast_zmod_eight_of_odd hr2).pow j).isSquare_mul_sq_iff] at key
  exact not_isSquare_intCast_zmod_eight_of_odd_of_emod_ne_one hr2 (by lia) key

/-- **Even `s`, even squarefree `n`.** If `s` is even and `r + εs ≢ 1 mod 8`, then `β_n` is not a
square: modulo `8`, `∏_{t ∣ n} w_t = (r + εs) r^(τ(n) - 2)` with `τ(n) - 2` even, and `r + εs` is
odd and not a square modulo `8`. No condition on `r` modulo `4` is needed here. -/
theorem not_isSquare_betaInt_of_squarefree_of_even_of_even (hs : s % 2 = 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hne : Even n) (h8 : (r + ε * s) % 8 ≠ 1) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have key := isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt hs0 hrs hε hw hn hsf hsq
  obtain ⟨j, hj⟩ := even_card_filter_divisors_of_even hn hsf hne
  have hr2 : r % 2 = 1 := emod_two_eq_one_of_isCoprime hrs hs
  rw [intCast_prod_wSeq_zmod_eight_of_even hs hrs, filter_divisors_le_two_of_even (by lia) hne,
    Finset.prod_pair one_lt_two.ne, wSeq_one, wSeq_two, Int.cast_one, one_mul, hj, ← two_mul,
    pow_mul', ((isUnit_intCast_zmod_eight_of_odd hr2).pow j).isSquare_mul_sq_iff] at key
  have : (2 : ℤ) ∣ ε * s := (Int.dvd_of_emod_eq_zero hs).mul_left ε
  exact not_isSquare_intCast_zmod_eight_of_odd_of_emod_ne_one (by lia) h8 key

end QuadraticIterates

end
