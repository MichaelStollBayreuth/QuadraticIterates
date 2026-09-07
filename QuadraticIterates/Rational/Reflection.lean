/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.Sequence

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# Reflection with the twist: `β_n` modulo `M`

The reflection mechanism of `QuadraticIterates.ArchMath1992.Sequences` for the integer Möbius
factors `β_n` of the sequence `w` of a rational parameter `a = r/s`: if a modulus `M` in which
`s` is invertible divides the numerator `N_k = w_k s^(2^(k-1)) + w_{k+1}` of `γ_k + γ_{k+1}`
(`QuadraticIterates.reflNum`), where `k = n / rad n`, then `γ_{k+1} ≡ -γ_k mod M` and the
constant tail of the `γ`-sequence over `ZMod M` makes `β_n ≡ -s^F · (unit)² mod M`, with the
twist `s^F`, `F = ∑_{t ∣ rad n} (2^(kt-1) - 1)`, coming from the denominators
(`QuadraticIterates.intCast_wSeq`). So `β_n` is not a square when `-1` (for `n` not squarefree,
`F` even) resp. `-s` (for `n` squarefree, `F` odd) is not a square modulo `M`.

## Main statements

* `QuadraticIterates.intCast_betaInt_eq_div`: `β_n` as a quotient of products of the `w_{kt}`.
* `QuadraticIterates.not_isSquare_betaInt_of_dvd_add_succ`: the reflection lemma with the twist,
  and its two consumed forms `QuadraticIterates.not_isSquare_betaInt_of_dvd_add_succ_of_two_le`
  (`n` not squarefree, `-1` not a square mod `M`) and
  `QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_dvd` (`n` squarefree, `M ∣ r + (1+ε)s`,
  `-s` not a square mod `M`).

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial ArithmeticFunction UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

variable {r s ε : ℤ}

/-- `β_n` as the quotient of the products of `w_{kt}` over the two halves of the divisors `t` of
`n' = rad n`, `k = n / n'`, by the sign of `μ(n'/t)`. -/
theorem intCast_betaInt_eq_div (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n k n' : ℕ} (hn : 1 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') : (betaInt r s ε n : ℚ) =
      ((∏ t ∈ n'.divisors with μ (n' / t) = 1, wSeq r s ε (k * t) : ℤ) : ℚ) /
        ((∏ t ∈ n'.divisors with μ (n' / t) = -1, wSeq r s ε (k * t) : ℤ) : ℚ) := by
  rw [intCast_betaInt hs hrs hε hw hn, moebiusFactorK_eq_prod]
  simp only [eq_intCast]
  rw [prod_pow_moebius_eq_div n k n' hn hn' hk (fun d ↦ ((wSeq r s ε d : ℤ) : ℚ)), Int.cast_prod,
    Int.cast_prod]

section zmod

variable {M : ℕ} {u : ZMod M}

local notation "gZ" => (C ((r : ZMod M) * u) * X ^ 2 + C (ε : ZMod M) : (ZMod M)[X])
local notation "γZ" => gammaSeq gZ (ε : ZMod M)

private lemma evenPoly_gZ : EvenPoly gZ := evenPoly_C_mul_X_sq_add_C _ _

private lemma isUnit_intCast_of_mul_eq_one (hu : (s : ZMod M) * u = 1) : IsUnit (s : ZMod M) :=
  isUnit_iff_exists_inv.mpr ⟨u, hu⟩

private lemma isUnit_eval_zero_gZ (hε : ε ^ 2 = 1) : IsUnit (eval 0 gZ) := by
  have : (ε : ZMod M) ^ 2 = 1 := by rw [← Int.cast_pow, hε, Int.cast_one]
  simpa using IsUnit.of_pow_eq_one this two_ne_zero

/-- The certificate `M ∣ N_k` says `γ_k + γ_{k+1} = 0` in `ZMod M`. -/
private lemma gammaSeq_zmod_add_succ_eq_zero (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1) {k : ℕ}
    (hk : 1 ≤ k) (hdvd : (M : ℤ) ∣ reflNum r s ε k) :
    γZ k + γZ (k + 1) = 0 := by
  rw [reflNum] at hdvd
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
  have he : 2 ^ k - 1 = 2 ^ (k - 1) - 1 + 2 ^ (k - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
    have := Nat.one_le_two_pow (n := m)
    rw [Nat.add_sub_cancel, pow_succ]
    lia
  push_cast at h
  rw [intCast_wSeq hu hε, intCast_wSeq hu hε, Nat.add_sub_cancel, he, pow_add] at h
  refine (((isUnit_intCast_of_mul_eq_one hu).pow (2 ^ (k - 1) - 1)).mul
    ((isUnit_intCast_of_mul_eq_one hu).pow (2 ^ (k - 1)))).mul_right_eq_zero.mp ?_
  linear_combination h

private lemma gammaSeq_zmod_add_two_mul_eq_zero (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1)
    {k : ℕ} (hk : 1 ≤ k)
    (hdvd : (M : ℤ) ∣ reflNum r s ε k) :
    γZ k + γZ (2 * k) = 0 :=
  zero_dvd_iff.mp
    (gammaSeq_zmod_add_succ_eq_zero hu hε hk hdvd ▸ gammaSeq_add_succ_dvd evenPoly_gZ _ hk)

private lemma isUnit_gammaSeq_zmod_two_mul (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1) {k : ℕ}
    (hk : 1 ≤ k) (hdvd : (M : ℤ) ∣ reflNum r s ε k) :
    IsUnit (γZ (2 * k)) := by
  have h1 : IsUnit (γZ k) := isCoprime_zero_left.mp
    (gammaSeq_zmod_add_succ_eq_zero hu hε hk hdvd ▸
      isCoprime_gammaSeq_add_succ (ε : ZMod M) hk (isUnit_eval_zero_gZ hε))
  rw [show γZ (2 * k) = -γZ k by
    linear_combination gammaSeq_zmod_add_two_mul_eq_zero hu hε hk hdvd]
  exact h1.neg

/-- A product of `w_{kt}` in `ZMod M` is the corresponding product of `γ_{kt}` times a power
of `s`. -/
private lemma intCast_prod_wSeq_zmod (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1) (k : ℕ)
    (S : Finset ℕ) : ((∏ t ∈ S, wSeq r s ε (k * t) : ℤ) : ZMod M) =
      (∏ t ∈ S, (s : ZMod M) ^ (2 ^ (k * t - 1) - 1)) * ∏ t ∈ S, γZ (k * t) := by
  push_cast
  simp only [intCast_wSeq hu hε]
  exact Finset.prod_mul_distrib

/-- A product of the `w_{kt}` over positive indices `t` is a unit modulo `M`. -/
private lemma isUnit_intCast_prod_wSeq_zmod (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1)
    {k : ℕ} (hk : 1 ≤ k)
    (hdvd : (M : ℤ) ∣ reflNum r s ε k) (S : Finset ℕ)
    (hS : ∀ t ∈ S, 1 ≤ t) : IsUnit ((∏ t ∈ S, wSeq r s ε (k * t) : ℤ) : ZMod M) := by
  rw [intCast_prod_wSeq_zmod hu hε]
  exact (IsUnit.prod_iff.mpr fun _ _ ↦ (isUnit_intCast_of_mul_eq_one hu).pow _).mul
    (isUnit_prod_gammaSeq_mul evenPoly_gZ hk (gammaSeq_zmod_add_two_mul_eq_zero hu hε hk hdvd)
      (isUnit_gammaSeq_zmod_two_mul hu hε hk hdvd) hS)

/-- **Reflection with the twist.** Let `n ≥ 2`, `n' = rad n`, `k = n / n'`, and let `M` be a
modulus in which `s` is invertible (with inverse `u`) and which divides the numerator `N_k` of
`γ_k + γ_{k+1}`. Then `β_n ≡ -s^F · (unit)² mod M` with
`F = ∑_{t ∣ n'} (2^(kt-1) - 1)`, so `β_n` is not a square if `-s^F` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_dvd_add_succ (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') (hu : (s : ZMod M) * u = 1)
    (hdvd : (M : ℤ) ∣ reflNum r s ε k)
    (hnsq : ¬IsSquare (-(s : ZMod M) ^ ∑ t ∈ n'.divisors, (2 ^ (k * t - 1) - 1))) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have hn'1 : 1 < n' := hn' ▸ Nat.one_lt_radical_iff.mpr (by lia)
  have hkpos : 1 ≤ k := by grind
  have hsf : Squarefree n' := hn' ▸ squarefree_radical
  have hz := gammaSeq_zmod_add_two_mul_eq_zero hu hε hkpos hdvd
  have hQu := isUnit_intCast_prod_wSeq_zmod hu hε hkpos hdvd
    (n'.divisors.filter fun t ↦ μ (n' / t) = -1) fun t ht ↦
      Nat.pos_of_mem_divisors (Finset.mem_of_mem_filter t ht)
  have key := ZMod.isSquare_mul_of_isSquare_div
    (x := -∏ t ∈ n'.divisors with μ (n' / t) = 1, (s : ZMod M) ^ (2 ^ (k * t - 1) - 1))
    (y := ∏ t ∈ n'.divisors with μ (n' / t) = -1, (s : ZMod M) ^ (2 ^ (k * t - 1) - 1))
    (by rw [intCast_prod_wSeq_zmod hu hε, intCast_prod_wSeq_zmod hu hε,
      prod_gammaSeq_mul_eq_neg_prod evenPoly_gZ hkpos hz hsf hn'1]; ring) hQu
    (intCast_betaInt_eq_div hs hrs hε hw (by lia) hn' hk ▸ Rat.isSquare_intCast_iff.mpr hsq)
  rw [neg_mul, ← Finset.prod_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia),
    hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one, Finset.prod_pow_eq_pow_sum] at key
  exact hnsq key

/-- The parity of `∑_{t ∈ S} (2^(m t) - 1)` is that of the number of `t ∈ S` with `m t ≥ 1`. -/
private lemma sum_two_pow_sub_one_mod_two (S : Finset ℕ) (m : ℕ → ℕ) :
    (∑ t ∈ S, (2 ^ m t - 1)) % 2 = (S.filter fun t ↦ 1 ≤ m t).card % 2 := by
  rw [Finset.sum_nat_mod, Finset.card_eq_sum_ones, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rcases Nat.eq_zero_or_pos (m t) with h | h
  · simp [h]
  · rw [ite_eq_left (show 1 ≤ m t from h)]
    exact Nat.odd_iff.mp
      (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, h.ne'⟩) odd_one)

/-- A squarefree `n > 1` has `2 #{t ∣ n : μ(n/t) = 1}` divisors: the two halves of the sign
partition have the same size. -/
lemma card_divisors_eq_two_mul_of_squarefree {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n) :
    n.divisors.card = 2 * (n.divisors.filter fun t ↦ μ (n / t) = 1).card := by
  have hc := hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one subset_rfl
    (sum_divisors_moebius_div_eq_zero hn1)
  nth_rw 1 [← hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia), ← hc,
    two_mul]

/-- The twist exponent `F = ∑_{t ∣ n} (2^(kt-1) - 1)` is even for `k ≥ 2` (`n` squarefree,
`n > 1`): all terms are odd and there are evenly many. -/
lemma even_sum_two_pow_mul_sub_one_of_squarefree {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n)
    {k : ℕ} (hk : 2 ≤ k) : Even (∑ t ∈ n.divisors, (2 ^ (k * t - 1) - 1)) := by
  rw [Nat.even_iff, sum_two_pow_sub_one_mod_two, Finset.filter_true_of_mem fun t ht ↦ ?_,
    card_divisors_eq_two_mul_of_squarefree hsf hn1, Nat.mul_mod_right]
  have := hk.trans (Nat.le_mul_of_pos_right k (Nat.pos_of_mem_divisors ht))
  lia

/-- The twist exponent `F = ∑_{t ∣ n} (2^(t-1) - 1)` is odd for squarefree `n > 1`: all terms
but the one at `t = 1` are odd, and there are evenly many divisors. -/
lemma odd_sum_two_pow_sub_one_of_squarefree {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n) :
    Odd (∑ t ∈ n.divisors, (2 ^ (t - 1) - 1)) := by
  have hf : (n.divisors.filter fun t ↦ 1 ≤ t - 1) = n.divisors.erase 1 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨by lia, h1⟩,
      fun ⟨h1, h2⟩ ↦ ⟨h2, by have := Nat.pos_of_mem_divisors h2; lia⟩⟩
  have hA : 1 ≤ (n.divisors.filter fun t ↦ μ (n / t) = 1).card :=
    Finset.card_pos.mpr
      ⟨n, by simp [Nat.mem_divisors_self n (by lia), Nat.div_self (by lia : 0 < n)]⟩
  rw [Nat.odd_iff, sum_two_pow_sub_one_mod_two, hf,
    Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr (by lia)),
    card_divisors_eq_two_mul_of_squarefree hsf hn1]
  lia

/-- The reflection lemma for `n` not squarefree (`k = n / rad n ≥ 2`): the twist `s^F` is a
square, so it suffices that `-1` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_dvd_add_succ_of_two_le (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n)
    (hn' : n' = radical n) (hk : n = k * n') (hk2 : 2 ≤ k) (hu : (s : ZMod M) * u = 1)
    (hdvd : (M : ℤ) ∣ reflNum r s ε k)
    (hnsq : ¬IsSquare (-1 : ZMod M)) : ¬IsSquare (betaInt r s ε n) :=
  not_isSquare_betaInt_of_dvd_add_succ hs hrs hε hw hn hn' hk hu hdvd fun h ↦ hnsq (by
    obtain ⟨j, hj⟩ := even_sum_two_pow_mul_sub_one_of_squarefree (hn' ▸ squarefree_radical)
      (hn' ▸ Nat.one_lt_radical_iff.mpr (by lia)) hk2
    rwa [hj, show -(s : ZMod M) ^ (j + j) = -1 * ((s : ZMod M) ^ j) ^ 2 by ring,
      ((isUnit_intCast_of_mul_eq_one hu).pow j).isSquare_mul_sq_iff] at h)

/-- The reflection lemma for squarefree `n ≥ 2` (`k = 1`): the modulus divides
`r + (1 + ε) s`, the numerator of `γ_1 + γ_2`, and the twist is `s` times a square, so it suffices
that `-s` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_squarefree_of_dvd (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hu : (s : ZMod M) * u = 1) (hdvd : (M : ℤ) ∣ r + (1 + ε) * s)
    (hnsq : ¬IsSquare (-(s : ZMod M))) : ¬IsSquare (betaInt r s ε n) :=
  not_isSquare_betaInt_of_dvd_add_succ hs hrs hε hw hn
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm hu
    (reflNum_one ▸ hdvd) fun h ↦ hnsq (by
      obtain ⟨j, hj⟩ := odd_sum_two_pow_sub_one_of_squarefree hsf (by lia)
      simp only [one_mul] at h
      rwa [hj, show -(s : ZMod M) ^ (2 * j + 1) = -(s : ZMod M) * ((s : ZMod M) ^ j) ^ 2 by ring,
        ((isUnit_intCast_of_mul_eq_one hu).pow j).isSquare_mul_sq_iff] at h)

end zmod

end QuadraticIterates

end
