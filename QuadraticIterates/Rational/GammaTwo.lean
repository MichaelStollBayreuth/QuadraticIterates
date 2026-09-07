/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.Reflection

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Group.Basic
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Defs
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.Moebius
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# The `γ_2` route: `β_n` modulo a divisor of the numerator of `γ_2`

The second mechanism for squarefree levels, the rational form of Lemmas 3.2 and 3.3 of [Li 2020]:
if a modulus `M` divides `w_2 = r + εs`, the numerator of `γ_2` (so that `M` is coprime to `s`),
then `β_n ≡ ε s · (unit)² mod M` for every squarefree `n ≥ 3`
(`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_dvd_wSeq_two`). Modulo `γ_2²` the
`γ`-sequence is `γ_2` at even and `ε` at odd indices `≥ 3`
(`QuadraticIterates.gammaSeq_two_sq_dvd_sub_ite_even` over `ℤ[1/s]`), which descends to `ℤ` as
`w_2 ∣ w_t` for even `t`
(`QuadraticIterates.wSeq_two_dvd_wSeq_of_even`) with `w_t / w_2 ≡ s^(2^(t-1) - 2) mod M`
(`QuadraticIterates.dvd_wSeq_ediv_wSeq_two_sub_pow_of_even`). The two sign classes of the divisors
of `n` contain equally many even divisors, so the common power of `w_2` cancels in `β_n`, and the
product of the `w_2`-free parts of the `w_t` over all divisors `t` of `n` is `ε s^F · (unit)²`
modulo `M`, with the odd twist exponent `F = ∑_{t ∣ n} (2^(t-1) - 1)`.

For `ε = -1` this is the certificate `M ∣ |r| - s`, `-s` not a square modulo `M`, of the theorem
for `a ≤ -2`; for `ε = 1` the certificate `M ∣ r + s`, `s` not a square modulo `M`, which is void
for integers (`s = 1`) and new for rational parameters.

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial
open scoped ArithmeticFunction.Moebius Finset

namespace QuadraticIterates

variable {r s ε : ℤ}

/-! ### Descent from `ℤ[1/s]`: `w_2 ∣ w_t` for even `t`, and `w_t / w_2` modulo divisors of `w_2` -/

section away

private lemma eval_zero_normPolyAway_sq (hε : ε ^ 2 = 1) : (normPolyAway r s ε).eval 0 ^ 2 = 1 :=
  eval_zero_normPolyAway r s ε ▸ Int.cast_sq_eq_one_of_sq_eq_one hε

local notation "γA" => gammaSeq (normPolyAway r s ε) ε

private lemma wSeqAway_two_dvd_wSeqAway_of_even (hε : ε ^ 2 = 1) {t : ℕ} (ht : 2 ≤ t)
    (hte : Even t) : wSeqAway r s ε 2 ∣ wSeqAway r s ε t := by
  rw [wSeqAway_eq_mul_gammaSeq hε, wSeqAway_eq_mul_gammaSeq hε]
  exact mul_dvd_mul (pow_dvd_pow _ (Nat.sub_le_sub_right (Nat.pow_le_pow_right two_pos (by lia)) 1))
    (gammaSeq_two_dvd_of_even (evenPoly_normPolyAway r s ε) (eval_zero_normPolyAway_sq hε)
      (gammaSeq_normPolyAway_one hε) ht hte)

private lemma intCast_dvd_gammaSeq_normPolyAway_two (hε : ε ^ 2 = 1) {M : ℕ}
    (hdvd : (M : ℤ) ∣ wSeq r s ε 2) : (M : Localization.Away s) ∣ γA 2 := by
  have h : (M : Localization.Away s) ∣ wSeqAway r s ε 2 := by
    simpa [wSeqAway_eq_intCast] using _root_.map_dvd (Int.castRingHom (Localization.Away s)) hdvd
  rwa [wSeqAway_two hε, (isUnit_intCast_localizationAway s).dvd_mul_left] at h

end away

/-- For even `t ≥ 2`, `w_2` divides `w_t`: in `ℤ[1/s]`, `γ_2 ∣ γ_t`, and `w_2` is coprime to `s`. -/
lemma wSeq_two_dvd_wSeq_of_even (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) {t : ℕ}
    (hte : Even t) : wSeq r s ε 2 ∣ wSeq r s ε t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have := NeZero.mk hs
  refine IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime (S := Localization.Away s) ?_
    (isCoprime_wSeq_right hrs one_le_two)
  rw [RingHom.ext_int (algebraMap ℤ _) (Int.castRingHom _)]
  exact wSeqAway_two_dvd_wSeqAway_of_even hε (Nat.le_of_dvd ht hte.two_dvd) hte

private lemma intCast_dvd_intCast_ediv_sub_pow [NeZero s] (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw2 : wSeq r s ε 2 ≠ 0) {M : ℕ} (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {t : ℕ} (ht : 2 ≤ t)
    (hte : Even t) : (M : Localization.Away s) ∣
      ((wSeq r s ε t / wSeq r s ε 2 : ℤ) : Localization.Away s) -
        (s : Localization.Away s) ^ (2 ^ (t - 1) - 2) := by
  obtain ⟨z, hz⟩ := gammaSeq_two_sq_dvd_sub_ite_even (evenPoly_normPolyAway r s ε)
    (eval_zero_normPolyAway_sq hε) (gammaSeq_normPolyAway_one hε) t ht
  rw [ite_eq_left hte] at hz
  have hv := congrArg (Int.cast : ℤ → Localization.Away s)
    (Int.mul_ediv_cancel' (wSeq_two_dvd_wSeq_of_even (NeZero.ne s) hrs hε hte))
  push_cast at hv
  rw [← wSeqAway_eq_intCast, ← wSeqAway_eq_intCast, wSeqAway_two hε, wSeqAway_eq_mul_gammaSeq hε]
    at hv
  have hne : (s : Localization.Away s) * gammaSeq (normPolyAway r s ε) ε 2 ≠ 0 := by
    rw [← wSeqAway_two hε, wSeqAway_eq_intCast]
    exact Int.cast_ne_zero.mpr hw2
  refine (intCast_dvd_gammaSeq_normPolyAway_two hε hdvd).trans
    ⟨(s : Localization.Away s) ^ (2 ^ (t - 1) - 2) * z, mul_left_cancel₀ hne ?_⟩
  linear_combination hv + ((s : Localization.Away s) * s ^ (2 ^ (t - 1) - 2)) * hz +
    gammaSeq (normPolyAway r s ε) ε t * pow_sub_one_eq_mul_pow_sub_two (s : Localization.Away s)
      (Nat.one_lt_two_pow (n := t - 1) (by lia))

/-- Modulo a divisor `M` of `w_2` (which is coprime to `s`), the quotient `w_t / w_2` for even
`t` is `s^(2^(t-1) - 2)`: in `ℤ[1/s]`, `γ_t ≡ γ_2 mod γ_2²`, so `γ_t / γ_2 ≡ 1 mod M`. -/
lemma dvd_wSeq_ediv_wSeq_two_sub_pow_of_even (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw2 : wSeq r s ε 2 ≠ 0) {M : ℕ} (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {t : ℕ} (ht : 2 ≤ t)
    (hte : Even t) : (M : ℤ) ∣ wSeq r s ε t / wSeq r s ε 2 - s ^ (2 ^ (t - 1) - 2) := by
  have := NeZero.mk hs
  refine IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime (S := Localization.Away s) ?_
    ((isCoprime_wSeq_right hrs one_le_two).of_isCoprime_of_dvd_left hdvd)
  rw [RingHom.ext_int (algebraMap ℤ _) (Int.castRingHom _)]
  simpa using intCast_dvd_intCast_ediv_sub_pow hrs hε hw2 hdvd ht hte

/-! ### The `w_2`-free part and its residues -/

section zmod

variable {M : ℕ} {u : ZMod M}

local notation "gZ" => (C ((r : ZMod M) * u) * X ^ 2 + C (ε : ZMod M) : (ZMod M)[X])
local notation "γZ" => gammaSeq gZ (ε : ZMod M)

private lemma evenPoly_gZ : EvenPoly gZ := evenPoly_C_mul_X_sq_add_C _ _

/-- The certificate `M ∣ w_2` says `γ_2 = 0` in `ZMod M`. -/
private lemma gammaSeq_zmod_two_eq_zero (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1)
    (hdvd : (M : ℤ) ∣ wSeq r s ε 2) : γZ 2 = 0 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
  rw [intCast_wSeq hu hε, show 2 ^ (2 - 1) - 1 = 1 by norm_num, pow_one] at h
  exact (IsUnit.of_mul_eq_one _ hu).mul_right_eq_zero.mp h

/-- Modulo `M ∣ w_2`, `γ_t = ε` for odd `t ≥ 3`. -/
private lemma gammaSeq_zmod_eq_of_odd (hu : (s : ZMod M) * u = 1) (hε : ε ^ 2 = 1)
    (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {t : ℕ} (ht : 2 ≤ t) (hto : ¬Even t) : γZ t = ε := by
  have hε' := Int.cast_sq_eq_one_of_sq_eq_one (S := ZMod M) hε
  have h : γZ 2 ^ 2 ∣ γZ t - if Even t then γZ 2 else eval 0 gZ :=
    gammaSeq_two_sq_dvd_sub_ite_even evenPoly_gZ (by simpa using hε')
      (by simp [gammaSeq_one, ← sq, hε']) t ht
  rw [gammaSeq_zmod_two_eq_zero hu hε hdvd, ite_eq_right hto, zero_pow two_ne_zero, zero_dvd_iff,
    sub_eq_zero] at h
  simpa using h

/-- The `w_2`-free part of `w_t`: `w_t / w_2` for even `t`, and `w_t` itself for odd `t`. -/
private def wOddPart (r s ε : ℤ) (t : ℕ) : ℤ :=
  if t % 2 = 0 then wSeq r s ε t / wSeq r s ε 2 else wSeq r s ε t

private lemma wSeq_eq_mul_wOddPart (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (t : ℕ) :
    wSeq r s ε t = (if t % 2 = 0 then wSeq r s ε 2 else 1) * wOddPart r s ε t := by
  rw [wOddPart]
  split_ifs with he
  · exact (Int.mul_ediv_cancel' (wSeq_two_dvd_wSeq_of_even hs hrs hε (Nat.even_iff.mpr he))).symm
  · rw [one_mul]

private lemma prod_wSeq_eq_pow_mul_prod_wOddPart (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (S : Finset ℕ) :
    ∏ t ∈ S, wSeq r s ε t = wSeq r s ε 2 ^ #{t ∈ S | t % 2 = 0} * ∏ t ∈ S, wOddPart r s ε t := by
  rw [Finset.prod_congr rfl fun t _ ↦ wSeq_eq_mul_wOddPart hs hrs hε t, Finset.prod_mul_distrib,
    Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- Modulo `M ∣ w_2` with `s u = 1`, the `w_2`-free part of `w_t` is `u s^(2^(t-1)-1)` for even
`t` and `ε s^(2^(t-1)-1)` for odd `t ≥ 3`. -/
private lemma intCast_wOddPart_zmod (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw2 : wSeq r s ε 2 ≠ 0) (hu : (s : ZMod M) * u = 1) (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {t : ℕ}
    (ht : 2 ≤ t) : (wOddPart r s ε t : ZMod M) =
      (if t % 2 = 0 then u else (ε : ZMod M)) * (s : ZMod M) ^ (2 ^ (t - 1) - 1) := by
  rw [wOddPart]
  split_ifs with he
  · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr
      (dvd_wSeq_ediv_wSeq_two_sub_pow_of_even hs hrs hε hw2 hdvd ht (Nat.even_iff.mpr he))
    push_cast at h
    rw [sub_eq_zero.mp h, pow_sub_one_eq_mul_pow_sub_two (s : ZMod M)
      (Nat.one_lt_two_pow (n := t - 1) (by lia))]
    linear_combination -(s : ZMod M) ^ (2 ^ (t - 1) - 2) * hu
  · rw [intCast_wSeq hu hε, gammaSeq_zmod_eq_of_odd hu hε hdvd ht (Nat.even_iff.not.mpr he),
      mul_comm]

/-- The product of the `w_2`-free parts over the divisors of `n` modulo `M ∣ w_2`. -/
private lemma intCast_prod_wOddPart_zmod (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw2 : wSeq r s ε 2 ≠ 0) (hu : (s : ZMod M) * u = 1) (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {n : ℕ}
    (hn : 1 ≤ n) : ((∏ t ∈ n.divisors, wOddPart r s ε t : ℤ) : ZMod M) =
      u ^ #{t ∈ n.divisors | t % 2 = 0} * (ε : ZMod M) ^ (#{t ∈ n.divisors | t % 2 = 1} - 1) *
        (s : ZMod M) ^ ∑ t ∈ n.divisors, (2 ^ (t - 1) - 1) := by
  rw [← Finset.mul_prod_erase _ _ (Nat.one_mem_divisors.mpr (by lia)), wOddPart,
    ite_eq_right (by decide), wSeq_one, one_mul]
  push_cast
  rw [Finset.prod_congr rfl fun t ht ↦ intCast_wOddPart_zmod hs hrs hε hw2 hu hdvd
      (by have := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase ht)
          have := Finset.ne_of_mem_erase ht
          lia),
    Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, Finset.sum_erase _ (by simp), Finset.filter_erase,
    Finset.filter_erase, Finset.erase_eq_of_notMem (by simp),
    Finset.card_erase_of_mem (by simp [Nat.one_mem_divisors.mpr (by lia : n ≠ 0)])]
  simp only [Nat.mod_two_ne_zero]

/-- For squarefree `n ≥ 3`, the product of the `w_2`-free parts over the divisors of `n` is
`ε s · (unit)²` modulo `M ∣ w_2`: evenly many even and evenly many odd divisors, and the odd twist
exponent. -/
private lemma exists_isUnit_intCast_prod_wOddPart_zmod_eq (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw2 : wSeq r s ε 2 ≠ 0) (hu : (s : ZMod M) * u = 1)
    (hdvd : (M : ℤ) ∣ wSeq r s ε 2) {n : ℕ} (hn : 3 ≤ n) (hsf : Squarefree n) :
    ∃ v : ZMod M, IsUnit v ∧
      ((∏ t ∈ n.divisors, wOddPart r s ε t : ℤ) : ZMod M) = ε * s * v ^ 2 := by
  obtain ⟨N, hN⟩ := hsf.even_card_filter_divisors_mod_two hn 0
  obtain ⟨N', hN'⟩ := hsf.even_card_filter_divisors_mod_two hn 1
  obtain ⟨j, hj⟩ := hsf.odd_sum_two_pow_sub_one (by lia)
  have h1 : 1 ≤ #{t ∈ n.divisors | t % 2 = 1} :=
    Finset.card_pos.mpr ⟨1, by simp [Nat.one_mem_divisors.mpr (by lia : n ≠ 0)]⟩
  refine ⟨u ^ N * s ^ j, ((IsUnit.of_mul_eq_one_right _ hu).pow N).mul
    ((IsUnit.of_mul_eq_one _ hu).pow j), ?_⟩
  rw [intCast_prod_wOddPart_zmod hs hrs hε hw2 hu hdvd (by lia), hN, hN', hj,
    show N' + N' - 1 = 2 * (N' - 1) + 1 by lia, pow_succ (ε : ZMod M), pow_mul, ← Int.cast_pow,
    hε, Int.cast_one, one_pow, one_mul]
  ring

private lemma isSquare_intCast_prod_wOddPart_of_isSquare_betaInt (hs : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    (hsf : Squarefree n) (hsq : IsSquare (betaInt r s ε n)) :
    IsSquare ((∏ t ∈ n.divisors, wOddPart r s ε t : ℤ) : ZMod M) := by
  have hβ := intCast_betaInt_eq_div_of_squarefree hs hrs hε hw hsf
  have hcard : #{t ∈ {t ∈ n.divisors | μ (n / t) = 1} | t % 2 = 0}
      = #{t ∈ {t ∈ n.divisors | μ (n / t) = -1} | t % 2 = 0} := by
    simpa [Finset.filter_filter, and_comm] using
      hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one (Finset.filter_subset _ _)
        (ArithmeticFunction.sum_divisors_filter_mod_two_moebius_div hn 0)
  rw [prod_wSeq_eq_pow_mul_prod_wOddPart hs hrs hε, prod_wSeq_eq_pow_mul_prod_wOddPart hs hrs hε,
    hcard, Int.cast_mul, Int.cast_mul, Int.cast_pow,
    mul_div_mul_left _ _ (pow_ne_zero _ (Int.cast_ne_zero.mpr (hw 2 one_le_two)))] at hβ
  have key := (Int.isSquare_mul_of_isSquare_div (hβ ▸ Rat.isSquare_intCast_iff.mpr hsq)).map
    (Int.castRingHom (ZMod M))
  rwa [Int.coe_castRingHom, hsf.prod_filter_moebius_div_eq_one_mul_prod_filter_eq_neg_one] at key

/-- **The `γ_2` route.** Let `M` divide `w_2 = r + εs`, the numerator of `γ_2` (so that `M` is
coprime to `s`). Then `β_n ≡ ε s · (unit)² mod M` for every squarefree `n ≥ 3`, so `β_n` is not a
square when `ε s` is not a square modulo `M`. Modulo
`γ_2²`, `γ_t ≡ γ_2` for even `t` and `γ_t ≡ ε` for odd `t ≥ 3`; the numerator and the denominator
of `β_n` contain the same power of `w_2` (the sign partition of the divisors of `n` is balanced
on the even divisors), and after cancelling it their product is `ε s^F · (unit)²` with the odd
twist exponent `F = ∑_{t ∣ n} (2^(t-1) - 1)`. Rational form of Lemmas 3.2 and 3.3 of [Li 2020]. -/
theorem not_isSquare_betaInt_of_squarefree_of_dvd_wSeq_two (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 3 ≤ n) (hsf : Squarefree n)
    (hdvd : (M : ℤ) ∣ wSeq r s ε 2) (hnsq : ¬IsSquare ((ε : ZMod M) * s)) :
    ¬IsSquare (betaInt r s ε n) := fun hsq ↦ by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_intCast_of_isCoprime_of_dvd
    (isCoprime_wSeq_right hrs one_le_two).symm hdvd).exists_right_inv
  obtain ⟨v, hv, h⟩ :=
    exists_isUnit_intCast_prod_wOddPart_zmod_eq hs hrs hε (hw 2 one_le_two) hu hdvd hn hsf
  exact hnsq ((hv.isSquare_mul_sq_iff _).mp
    (h ▸ isSquare_intCast_prod_wOddPart_of_isSquare_betaInt hs hrs hε hw hn hsf hsq))

end zmod

end QuadraticIterates

end
