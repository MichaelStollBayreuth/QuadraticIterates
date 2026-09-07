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
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Defs
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.Moebius
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# Reflection with the twist: `β_n` modulo `M`

The reflection mechanism of `QuadraticIterates.ArchMath1992.Sequences` for the integer Möbius
factors `β_n` of the sequence `w` of a rational parameter `a = r/s`: if a modulus `M` divides
the numerator `N_k = w_k s^(2^(k-1)) + w_{k+1}` of `γ_k + γ_{k+1}` (`QuadraticIterates.reflNum`,
coprime to `s`), where `k = n / rad n`, then `γ_{k+1} ≡ -γ_k mod M` and the
constant tail of the `γ`-sequence over `ZMod M` makes `β_n ≡ -s^F · (unit)² mod M`, with the
twist `s^F`, `F = ∑_{t ∣ rad n} (2^(kt-1) - 1)`, coming from the denominators
(`QuadraticIterates.intCast_wSeq`). So `β_n` is not a square when `-1` (for `n` not squarefree,
`F` even) resp. `-s` (for `n` squarefree, `F` odd) is not a square modulo `M`.

## Main statements

* `QuadraticIterates.intCast_betaInt_eq_div`: `β_n` as a quotient of products of the `w_{kt}`,
  and `QuadraticIterates.intCast_betaInt_eq_div_of_squarefree` for squarefree `n`.
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

/-- `β_n` for squarefree `n` as the quotient of the products of `w_t` over the two halves of the
divisors `t` of `n` by the sign of `μ(n/t)`. -/
theorem intCast_betaInt_eq_div_of_squarefree (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hsf : Squarefree n) : (betaInt r s ε n : ℚ) =
      ((∏ t ∈ n.divisors with μ (n / t) = 1, wSeq r s ε t : ℤ) : ℚ) /
        ((∏ t ∈ n.divisors with μ (n / t) = -1, wSeq r s ε t : ℤ) : ℚ) := by
  simpa using intCast_betaInt_eq_div hs hrs hε hw (Nat.pos_of_ne_zero hsf.ne_zero)
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm

section zmod

variable {M : ℕ} {u : ZMod M}

local notation "gZ" => (C ((r : ZMod M) * u) * X ^ 2 + C (ε : ZMod M) : (ZMod M)[X])
local notation "γZ" => gammaSeq gZ (ε : ZMod M)

private lemma evenPoly_gZ : EvenPoly gZ := evenPoly_C_mul_X_sq_add_C _ _

private lemma isUnit_eval_zero_gZ (hε : ε ^ 2 = 1) : IsUnit (eval 0 gZ) := by
  simpa using IsUnit.of_pow_eq_one (Int.cast_sq_eq_one_of_sq_eq_one (S := ZMod M) hε) two_ne_zero

/-- The certificate `M ∣ N_k` says `γ_k + γ_{k+1} = 0` in `ZMod M`. -/
private lemma gammaSeq_zmod_add_succ_eq_zero (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1) {k : ℕ}
    (hk : 1 ≤ k) (hdvd : (M : ℤ) ∣ reflNum r s ε k) :
    γZ k + γZ (k + 1) = 0 := by
  rw [reflNum_eq] at hdvd
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
  push_cast at h
  rw [intCast_wSeq hu hε, intCast_wSeq hu hε, Nat.add_sub_cancel, Nat.two_pow_sub_one_eq_add hk,
    pow_add] at h
  refine (((IsUnit.of_mul_eq_one _ hu).pow (2 ^ (k - 1) - 1)).mul
    ((IsUnit.of_mul_eq_one _ hu).pow (2 ^ (k - 1)))).mul_right_eq_zero.mp ?_
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
  exact (IsUnit.prod_iff.mpr fun _ _ ↦ (IsUnit.of_mul_eq_one _ hu).pow _).mul
    (isUnit_prod_gammaSeq_mul evenPoly_gZ hk (gammaSeq_zmod_add_two_mul_eq_zero hu hε hk hdvd)
      (isUnit_gammaSeq_zmod_two_mul hu hε hk hdvd) hS)

/-- **Reflection with the twist.** Let `n ≥ 2`, `n' = rad n`, `k = n / n'`, and let `M` divide
the numerator `N_k` of `γ_k + γ_{k+1}` (so that `M` is coprime to `s`). Then
`β_n ≡ -s^F · (unit)² mod M` with `F = ∑_{t ∣ n'} (2^(kt-1) - 1)`, so `β_n` is not a square if
`-s^F` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_dvd_add_succ (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') (hdvd : (M : ℤ) ∣ reflNum r s ε k)
    (hnsq : ¬IsSquare (-(s : ZMod M) ^ ∑ t ∈ n'.divisors, (2 ^ (k * t - 1) - 1))) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  have hn'1 : 1 < n' := hn' ▸ Nat.one_lt_radical_iff.mpr (by lia)
  have hkpos : 1 ≤ k := by grind
  have hsf : Squarefree n' := hn' ▸ squarefree_radical
  obtain ⟨u, hu⟩ := (ZMod.isUnit_intCast_of_isCoprime_of_dvd
    (isCoprime_reflNum_right hrs hkpos).symm hdvd).exists_right_inv
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
  rw [neg_mul, hsf.prod_filter_moebius_div_eq_one_mul_prod_filter_eq_neg_one,
    Finset.prod_pow_eq_pow_sum] at key
  exact hnsq key

/-- The reflection lemma for `n` not squarefree (`k = n / rad n ≥ 2`): the twist `s^F` is a
square, so it suffices that `-1` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_dvd_add_succ_of_two_le (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n)
    (hn' : n' = radical n) (hk : n = k * n') (hk2 : 2 ≤ k) (hdvd : (M : ℤ) ∣ reflNum r s ε k)
    (hnsq : ¬IsSquare (-1 : ZMod M)) : ¬IsSquare (betaInt r s ε n) := by
  have hsu : IsUnit (s : ZMod M) := ZMod.isUnit_intCast_of_isCoprime_of_dvd
    (isCoprime_reflNum_right hrs (one_le_two.trans hk2)).symm hdvd
  refine not_isSquare_betaInt_of_dvd_add_succ hs hrs hε hw hn hn' hk hdvd fun h ↦ hnsq ?_
  rwa [← neg_one_mul, hsu.isSquare_mul_pow_iff_of_even (Squarefree.even_sum_two_pow_mul_sub_one
    (hn' ▸ squarefree_radical) (hn' ▸ Nat.one_lt_radical_iff.mpr (by lia)) hk2)] at h

/-- The reflection lemma for squarefree `n ≥ 2` (`k = 1`): the modulus divides
`r + (1 + ε) s`, the numerator of `γ_1 + γ_2`, and the twist is `s` times a square, so it suffices
that `-s` is not a square mod `M`. -/
theorem not_isSquare_betaInt_of_squarefree_of_dvd (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n)
    (hdvd : (M : ℤ) ∣ r + (1 + ε) * s) (hnsq : ¬IsSquare (-(s : ZMod M))) :
    ¬IsSquare (betaInt r s ε n) := by
  have hd : (M : ℤ) ∣ reflNum r s ε 1 := reflNum_one ▸ hdvd
  have hsu : IsUnit (s : ZMod M) :=
    ZMod.isUnit_intCast_of_isCoprime_of_dvd (isCoprime_reflNum_right hrs le_rfl).symm hd
  refine not_isSquare_betaInt_of_dvd_add_succ hs hrs hε hw hn
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm hd fun h ↦ hnsq ?_
  simp only [one_mul] at h
  rwa [← neg_one_mul, hsu.isSquare_mul_pow_iff_of_odd (hsf.odd_sum_two_pow_sub_one (by lia)),
    neg_one_mul] at h

end zmod

end QuadraticIterates

end
