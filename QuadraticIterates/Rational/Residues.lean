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
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Defs
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.Moebius
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
(`QuadraticIterates.not_isSquare_neg_one_zmod_reflNum`), and
`QuadraticIterates.not_isSquare_betaInt_of_dvd_reflNum` with the modulus `N_k` makes `β_n` a
non-square for every `n ≥ 2` with `n / rad n ≥ 2`
(`QuadraticIterates.not_isSquare_betaInt_of_twoAdicClass_of_two_le`).

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius Finset

namespace QuadraticIterates

variable {r s ε : ℤ}

/-! ### Residues modulo 8 -/

section zmod8

variable {u : ZMod 8}

local notation "g8" => (C ((r : ZMod 8) * u) * X ^ 2 + C (ε : ZMod 8) : (ZMod 8)[X])
local notation "γ8" => gammaSeq g8 (ε : ZMod 8)

private lemma gammaSeq_zmod_eight_one (hε : ε ^ 2 = 1) : γ8 1 = 1 := by
  rw [gammaSeq_one, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_C]
  linear_combination Int.cast_sq_eq_one_of_sq_eq_one (S := ZMod 8) hε

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
  have he := Int.cast_sq_eq_one_of_sq_eq_one (S := ZMod 8) hε
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
      rw [add_right_comm k 1 2, Nat.even_add_one]
    rw [hp k hk, hp (k + 1) (by lia)]
    grind
  rw [reflNum_eq]
  push_cast
  rw [intCast_wSeq hu hε, intCast_wSeq hu hε, Nat.add_sub_cancel, mul_right_comm, ← pow_add,
    ← Nat.two_pow_sub_one_eq_add (one_le_two.trans hk),
    ZMod.intCast_pow_two_pow_sub_one_eight_of_odd (Int.odd_iff.mpr hs) (by lia), ← mul_add, hsum]

/-- The class condition for odd `s` in `ZMod 8`. -/
private lemma intCast_zmod_eight_of_class (hclass : r % 4 = 1 ∨ (r + ε * s) % 4 = 3) :
    (r : ZMod 8) = ((1 : ℤ) : ZMod 8) ∨ (r : ZMod 8) = ((5 : ℤ) : ZMod 8) ∨
      ((r + ε * s : ℤ) : ZMod 8) = ((3 : ℤ) : ZMod 8) ∨
        ((r + ε * s : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8) := by
  have h8 {x y : ℤ} (h : x % 8 = y % 8) : (x : ZMod 8) = y :=
    (ZMod.intCast_eq_intCast_iff' x y 8).mpr h
  have h : r % 8 = 1 % 8 ∨ r % 8 = 5 % 8 ∨ (r + ε * s) % 8 = 3 % 8 ∨ (r + ε * s) % 8 = 7 % 8 := by
    lia
  exact h.imp h8 (.imp h8 (.imp h8 h8))

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
  have hs2 := ZMod.intCast_sq_eight_eq_one_of_odd (Int.odd_iff.mpr hs)
  have he := Int.cast_sq_eq_one_of_sq_eq_one (S := ZMod 8) hε
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
private lemma odd_of_isCoprime_of_even {x y : ℤ} (h : IsCoprime x y) (hy : Even y) : Odd x :=
  Int.not_even_iff_odd.mp fun hx ↦
    Int.prime_two.not_isUnit (h.isUnit_of_dvd' hx.two_dvd hy.two_dvd)

/-- For even `s` (and `r` coprime to `s`), `w_n` is odd, so `w_n² = 1` in `ZMod 8`. -/
private lemma intCast_wSeq_sq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) {n : ℕ}
    (hn : 1 ≤ n) : (wSeq r s ε n : ZMod 8) ^ 2 = 1 :=
  ZMod.intCast_sq_eight_eq_one_of_odd
    (odd_of_isCoprime_of_even (isCoprime_wSeq_right hrs hn) (Int.even_iff.mpr hs))

/-- For even `s` (and `r` coprime to `s`), `w_n ≡ r mod 8` for all `n ≥ 3`: `w_n` is odd, so
`w_n² ≡ 1`, and `8 ∣ s^(2^n - 1)` for `n ≥ 2`. -/
theorem intCast_wSeq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) :
    ∀ n ≥ 3, (wSeq r s ε n : ZMod 8) = r := fun n hn ↦ by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  have h3 : 3 ≤ 2 ^ m - 1 := by
    have := Nat.pow_le_pow_right two_pos (by lia : 2 ≤ m)
    lia
  rw [wSeq_succ r s ε (by lia)]
  push_cast
  rw [intCast_wSeq_sq_zmod_eight_of_even hs hrs (by lia),
    ZMod.intCast_pow_eight_eq_zero_of_even (Int.even_iff.mpr hs) h3]
  ring

/-- **The 2-adic classes, even `s`.** If `s` is even and `r ≡ 3 mod 4`, then `N_k ≡ 3 mod 4` for
every `k ≥ 2`: `4 ∣ s^(2^(k-1))` and `w_{k+1} ≡ r mod 8`. -/
theorem reflNum_emod_four_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s) (hr : r % 4 = 3)
    {k : ℕ} (hk : 2 ≤ k) : reflNum r s ε k % 4 = 3 := by
  have h1 := (ZMod.intCast_eq_intCast_iff' _ _ 8).mp
    (intCast_wSeq_zmod_eight_of_even (ε := ε) hs hrs (k + 1) (by lia))
  have h4 : (4 : ℤ) ∣ wSeq r s ε k * s ^ 2 ^ (k - 1) :=
    ((pow_dvd_pow 2 (Nat.one_lt_two_pow (show k - 1 ≠ 0 by lia))).trans
      (pow_dvd_pow_of_dvd (Int.dvd_of_emod_eq_zero hs) _)).mul_left _
  rw [reflNum_eq]
  lia

/-! ### The corollary: `β_n` for `n` not squarefree -/

/-- The 2-adic classes (C⁺) (for `ε = 1`) and (C⁻) (for `ε = -1`, `|r|` in place of `r`), as a
condition on `r`, `s`, `ε`: `s` odd with `r ≡ 1 mod 4` or `r + εs ≡ 3 mod 4`, or `s` even with
`r ≡ 3 mod 4`. -/
def TwoAdicClass (r s ε : ℤ) : Prop :=
  (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + ε * s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3)

theorem twoAdicClass_iff : TwoAdicClass r s ε ↔
    (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + ε * s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3) := .rfl

/-- In the 2-adic classes, `-1` is not a square modulo `N_k` for every `k ≥ 2` with `N_k ≥ 0`. -/
theorem not_isSquare_neg_one_zmod_reflNum (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hc : TwoAdicClass r s ε) {k : ℕ} (hk : 2 ≤ k) (hN : 0 ≤ reflNum r s ε k) :
    ¬IsSquare (-1 : ZMod (reflNum r s ε k).natAbs) :=
  (twoAdicClass_iff.mp hc).elim
    (fun h ↦ (reflNum_emod_of_odd h.1 hε h.2 hk).elim
      (Int.not_isSquare_neg_one_zmod_natAbs_of_emod_eight_eq_six hN)
      (Int.not_isSquare_neg_one_zmod_natAbs_of_emod_four_eq_three hN))
    fun h ↦ Int.not_isSquare_neg_one_zmod_natAbs_of_emod_four_eq_three hN
      (reflNum_emod_four_of_even h.1 hrs h.2 hk)

/-- **Non-squarefree levels.** In the 2-adic classes, `β_n` is not a square for every `n ≥ 2`
with `k = n / rad n ≥ 2` and `N_k ≥ 0`: `QuadraticIterates.not_isSquare_betaInt_of_dvd_reflNum`
with the modulus `N_k` itself. -/
theorem not_isSquare_betaInt_of_twoAdicClass_of_two_le (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (hc : TwoAdicClass r s ε) {n k : ℕ}
    (hn : 2 ≤ n) (hk : n = k * radical n) (hk2 : 2 ≤ k) (hN : 0 ≤ reflNum r s ε k) :
    ¬IsSquare (betaInt r s ε n) :=
  not_isSquare_betaInt_of_dvd_reflNum_of_two_le hs hrs hε hw hn rfl hk hk2
    (Int.natAbs_dvd.mpr dvd_rfl) (not_isSquare_neg_one_zmod_reflNum hrs hε hc hk2 hN)

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
      add_zero, Nat.two_pow_sub_one_eq hn]
    ring

private lemma intCast_prod_wSeq_zmod_of_dvd (hM : (M : ℤ) ∣ s) {S : Finset ℕ}
    (hS : ∀ t ∈ S, 1 ≤ t) :
    ((∏ t ∈ S, wSeq r s ε t : ℤ) : ZMod M) = (r : ZMod M) ^ ∑ t ∈ S, (2 ^ (t - 1) - 1) := by
  push_cast
  rw [Finset.prod_congr rfl fun t ht ↦ intCast_wSeq_zmod_of_dvd hM t (hS t ht),
    Finset.prod_pow_eq_pow_sum]

/-- For squarefree `n` and `M ∣ s`, if `β_n` is a square then `r^F` is a square modulo `M`,
`F = ∑_{t ∣ n} (2^(t-1) - 1)` the twist exponent: `β_n = P/Q` with `P ≡ r^(F⁺)`, `Q ≡ r^(F⁻)`. -/
private lemma isSquare_intCast_pow_of_isSquare_betaInt (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hsf : Squarefree n)
    (hM : (M : ℤ) ∣ s) (hsq : IsSquare (betaInt r s ε n)) :
    IsSquare ((r : ZMod M) ^ ∑ t ∈ n.divisors, (2 ^ (t - 1) - 1)) := by
  have hpos (S : Finset ℕ) (hS : S ⊆ n.divisors) : ∀ t ∈ S, 1 ≤ t :=
    fun t ht ↦ Nat.pos_of_mem_divisors (hS ht)
  have key := ZMod.isSquare_mul_of_isSquare_div
    (x := (r : ZMod M) ^ ∑ t ∈ n.divisors with μ (n / t) = 1, (2 ^ (t - 1) - 1))
    (y := (r : ZMod M) ^ ∑ t ∈ n.divisors with μ (n / t) = -1, (2 ^ (t - 1) - 1))
    (by rw [intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _)),
      intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _))])
    (by rw [intCast_prod_wSeq_zmod_of_dvd hM (hpos _ (Finset.filter_subset _ _))]
        exact (ZMod.isUnit_intCast_of_isCoprime_of_dvd hrs hM).pow _)
    (intCast_betaInt_eq_div_of_squarefree hs hrs hε hw hsf ▸ Rat.isSquare_intCast_iff.mpr hsq)
  rwa [← pow_add, hsf.sum_filter_moebius_div_eq_one_add_sum_filter_eq_neg_one] at key

/-- **The primes of `s`.** If `M ∣ s` and `r` is not a square modulo `M`, then `β_n` is not a
square for every squarefree `n ≥ 2`: modulo `M`, `β_n ≡ r^F · (unit)²` with the odd twist exponent
`F = ∑_{t ∣ n} (2^(t-1) - 1)`. -/
theorem not_isSquare_betaInt_of_squarefree_of_dvd_of_not_isSquare (hs : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hM : (M : ℤ) ∣ s) (hnsq : ¬IsSquare (r : ZMod M)) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦
  hnsq (((ZMod.isUnit_intCast_of_isCoprime_of_dvd hrs hM).isSquare_pow_iff_of_odd
    (hsf.odd_sum_two_pow_sub_one (by lia))).mp
      (isSquare_intCast_pow_of_isSquare_betaInt hs hrs hε hw hsf hM hsq))

end dvd

/-! ### Squarefree levels for even `s` -/

/-- For squarefree `n`, if `β_n` is a square then so is `∏_{t ∣ n} w_t` modulo `8`: the product of
the numerator and the denominator of `β_n`. -/
private lemma isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ}
    (hsf : Squarefree n) (hsq : IsSquare (betaInt r s ε n)) :
    IsSquare ((∏ t ∈ n.divisors, wSeq r s ε t : ℤ) : ZMod 8) := by
  have hβ := intCast_betaInt_eq_div_of_squarefree hs0 hrs hε hw hsf
  have key := (Int.isSquare_mul_of_isSquare_div (hβ ▸ Rat.isSquare_intCast_iff.mpr hsq)).map
    (Int.castRingHom (ZMod 8))
  rwa [Int.coe_castRingHom, hsf.prod_filter_moebius_div_eq_one_mul_prod_filter_eq_neg_one] at key

/-- The product `∏_{t ∣ n} w_t` modulo `8` for even `s`: the factors with `t ≥ 3` are `r`. -/
private lemma intCast_prod_wSeq_zmod_eight_of_even (hs : s % 2 = 0) (hrs : IsCoprime r s)
    (n : ℕ) : ((∏ t ∈ n.divisors, wSeq r s ε t : ℤ) : ZMod 8) =
      (∏ t ∈ n.divisors with t ≤ 2, (wSeq r s ε t : ZMod 8)) *
        (r : ZMod 8) ^ #{t ∈ n.divisors | ¬t ≤ 2} := by
  push_cast
  rw [← Finset.prod_filter_mul_prod_filter_not n.divisors (· ≤ 2), ← Finset.prod_const]
  congr 1
  exact Finset.prod_congr rfl fun t ht ↦
    intCast_wSeq_zmod_eight_of_even hs hrs t (by have := (Finset.mem_filter.mp ht).2; lia)

private lemma divisors_filter_le_two_of_odd {n : ℕ} (hn : Odd n) :
    {t ∈ n.divisors | t ≤ 2} = {1} := by
  ext t
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  refine ⟨fun ⟨⟨ht, hn0⟩, h2⟩ ↦ ?_, fun h ↦ h ▸ ⟨⟨one_dvd n, hn.pos.ne'⟩, one_le_two⟩⟩
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by lia) with rfl | rfl | rfl
  · exact absurd (zero_dvd_iff.mp ht) hn0
  · rfl
  · have := Nat.mod_eq_zero_of_dvd ht
    have := Nat.odd_iff.mp hn
    lia

private lemma divisors_filter_le_two_of_even {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) :
    {t ∈ n.divisors | t ≤ 2} = {1, 2} := by
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

-- The divisors `t ≤ 2` and `t > 2` of a squarefree `n ≥ 2` together number `2 #S₊`.
private lemma card_filter_divisors_le_two_add {n : ℕ} (hsf : Squarefree n) (hn : 2 ≤ n) :
    #{t ∈ n.divisors | t ≤ 2} + #{t ∈ n.divisors | ¬t ≤ 2} =
      2 * #{t ∈ n.divisors | μ (n / t) = 1} :=
  (Finset.card_filter_add_card_filter_not (s := n.divisors) (· ≤ 2)).trans
    (hsf.card_divisors_eq_two_mul hn)

-- The number of divisors `t > 2` of an odd squarefree `n ≥ 2` is odd: `τ(n) - 1`.
private lemma odd_card_filter_divisors_of_odd {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hno : Odd n) : Odd #{t ∈ n.divisors | ¬t ≤ 2} := by
  have hc := card_filter_divisors_le_two_add hsf hn
  rw [divisors_filter_le_two_of_odd hno, Finset.card_singleton] at hc
  exact ⟨#{t ∈ n.divisors | μ (n / t) = 1} - 1, by lia⟩

-- The number of divisors `t > 2` of an even squarefree `n` is even: `τ(n) - 2`.
private lemma even_card_filter_divisors_of_even {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hne : Even n) : Even #{t ∈ n.divisors | ¬t ≤ 2} := by
  have hc := card_filter_divisors_le_two_add hsf hn
  rw [divisors_filter_le_two_of_even (by lia) hne, Finset.card_pair one_lt_two.ne] at hc
  exact ⟨#{t ∈ n.divisors | μ (n / t) = 1} - 1, by lia⟩

/-- **Even `s`, odd squarefree `n ≥ 3`.** If `s` is even and `r ≡ 3 mod 4`, then `β_n` is not a
square: modulo `8`, `∏_{t ∣ n} w_t = r^(τ(n) - 1)` with `τ(n) - 1` odd, and `r` is not a square
modulo `8`. -/
theorem not_isSquare_betaInt_of_squarefree_of_odd_of_even (hs : s % 2 = 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hsf : Squarefree n) (hno : Odd n) (hr : r % 4 = 3) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have key := isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt hs0 hrs hε hw hsf hsq
  have hr2 : Odd r := odd_of_isCoprime_of_even hrs (Int.even_iff.mpr hs)
  rw [intCast_prod_wSeq_zmod_eight_of_even hs hrs, divisors_filter_le_two_of_odd hno,
    Finset.prod_singleton, wSeq_one, Int.cast_one, one_mul,
    (ZMod.isUnit_intCast_eight_of_odd hr2).isSquare_pow_iff_of_odd
      (odd_card_filter_divisors_of_odd hn hsf hno)] at key
  exact ZMod.not_isSquare_intCast_eight_of_odd_of_emod_ne_one hr2 (by lia) key

/-- **Even `s`, even squarefree `n`.** If `s` is even and `r + εs ≢ 1 mod 8`, then `β_n` is not a
square: modulo `8`, `∏_{t ∣ n} w_t = (r + εs) r^(τ(n) - 2)` with `τ(n) - 2` even, and `r + εs` is
odd and not a square modulo `8`. No condition on `r` modulo `4` is needed here. -/
theorem not_isSquare_betaInt_of_squarefree_of_even_of_even (hs : s % 2 = 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ}
    (hsf : Squarefree n) (hne : Even n) (h8 : (r + ε * s) % 8 ≠ 1) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have hn : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hne
    have := hsf.ne_zero
    lia
  have key := isSquare_intCast_prod_wSeq_zmod_eight_of_isSquare_betaInt hs0 hrs hε hw hsf hsq
  have hs' : Even s := Int.even_iff.mpr hs
  have hr2 : Odd r := odd_of_isCoprime_of_even hrs hs'
  rw [intCast_prod_wSeq_zmod_eight_of_even hs hrs, divisors_filter_le_two_of_even (by lia) hne,
    Finset.prod_pair one_lt_two.ne, wSeq_one, wSeq_two, Int.cast_one, one_mul,
    (ZMod.isUnit_intCast_eight_of_odd hr2).isSquare_mul_pow_iff_of_even
      (even_card_filter_divisors_of_even hn hsf hne)] at key
  exact ZMod.not_isSquare_intCast_eight_of_odd_of_emod_ne_one (hr2.add_even (hs'.mul_left ε)) h8
    key

end QuadraticIterates

end
