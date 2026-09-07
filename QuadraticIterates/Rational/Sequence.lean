/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import QuadraticIterates.ArchMath1992.Sequences
public import QuadraticIterates.Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The rescaled sequence of a rational parameter and its integer Möbius factors

For `a = r/s` with coprime integers `r`, `s` and a sign `ε`, the `γ`-sequence of `a X² + ε`
has the form `γ_n = w_n / s^(2^(n-1) - 1)` with integers `w_n` (`QuadraticIterates.wSeq`,
`QuadraticIterates.intCast_wSeq`) coprime to `r` and to `s`. Over the unique factorization domain
`ℤ[1/s]` the sequence `w` is the `γ`-sequence up to units, so the theory of
`QuadraticIterates.ArchMath1992.Sequences` applies to it there: its Möbius factors are pairwise
relatively prime (`QuadraticIterates.isRelPrime_moebiusFactorR_wSeqAway`). This descends to `ℤ`:
the integer Möbius factors `β_n = ∏_{d ∣ n} w_d^{μ(n/d)}` (`QuadraticIterates.betaInt`) are
integers (`QuadraticIterates.intCast_betaInt`), nonzero, pairwise coprime
(`QuadraticIterates.isCoprime_betaInt`) and coprime to `r` and `s`, with `w_n = ∏_{d ∣ n} β_d`.

## Main definitions and statements

* `QuadraticIterates.wSeq`: `w_1 = 1`, `w_{n+1} = r w_n² + ε s^(2^n - 1)`, and
  `QuadraticIterates.intCast_wSeq`: in any commutative ring in which `s` is invertible,
  `w_n = s^(2^(n-1) - 1) γ_n`.
* `QuadraticIterates.wSeqAway`, `QuadraticIterates.normPolyAway`: `w` and the rescaled
  polynomial over `ℤ[1/s]`, and `QuadraticIterates.isRelPrime_moebiusFactorR_wSeqAway`.
* `QuadraticIterates.betaInt` with `QuadraticIterates.betaInt_mul_denProd`,
  `QuadraticIterates.intCast_betaInt`, `QuadraticIterates.wSeq_eq_prod_betaInt`,
  `QuadraticIterates.isCoprime_betaInt`, `QuadraticIterates.isCoprime_betaInt_left`,
  `QuadraticIterates.isCoprime_betaInt_right`.

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace QuadraticIterates

/-! ### The integer sequence `w` -/

section wSeq

variable (r s ε : ℤ)

/-- The numerators `w_n` of the rescaled sequence of `a = r/s`: `w_1 = 1` and
`w_{n+1} = r w_n² + ε s^(2^n - 1)`, so that `γ_n = w_n / s^(2^(n-1) - 1)` for the `γ`-sequence of
`a X² + ε` with sign `ε` (`QuadraticIterates.intCast_wSeq`); junk value `w_0 = 0`. -/
def wSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => r * wSeq (n + 1) ^ 2 + ε * s ^ (2 ^ (n + 1) - 1)

@[simp] lemma wSeq_zero : wSeq r s ε 0 = 0 := rfl

@[simp] lemma wSeq_one : wSeq r s ε 1 = 1 := rfl

lemma wSeq_succ {n : ℕ} (hn : 1 ≤ n) :
    wSeq r s ε (n + 1) = r * wSeq r s ε n ^ 2 + ε * s ^ (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rfl

variable {r s ε}

private lemma two_pow_sub_one_eq {n : ℕ} (hn : 1 ≤ n) : 2 ^ n - 1 = 2 * (2 ^ (n - 1) - 1) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have := Nat.one_le_two_pow (n := m)
  rw [Nat.add_sub_cancel, pow_succ]
  lia

/-- In a commutative ring `S` in which `s` is invertible, with inverse `u`, the cast of `w_n` is
`s^(2^(n-1) - 1) γ_n` for the `γ`-sequence of `(r u) X² + ε` with sign `ε`. -/
theorem intCast_wSeq {S : Type*} [CommRing S] {u : S} (hu : (s : S) * u = 1) (hε : ε ^ 2 = 1)
    (n : ℕ) : (wSeq r s ε n : S) =
      (s : S) ^ (2 ^ (n - 1) - 1) * gammaSeq (C ((r : S) * u) * X ^ 2 + C (ε : S)) (ε : S) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (ε : S) ^ 2 = 1 := by rw [← Int.cast_pow, hε, Int.cast_one]
      simp [← sq, this]
    · rw [wSeq_succ r s ε hn, gammaSeq_succ _ _ hn, Nat.add_sub_cancel, two_pow_sub_one_eq hn,
        eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_C]
      push_cast
      rw [ih]
      linear_combination (-(r : S) * ((s : S) ^ (2 ^ (n - 1) - 1)) ^ 2 *
        gammaSeq (C ((r : S) * u) * X ^ 2 + C (ε : S)) (ε : S) n ^ 2) * hu

/-- `w_n` is coprime to `r`: `w_{n+1} ≡ ε s^(2^n - 1) mod r`. -/
lemma isCoprime_wSeq_left (hrs : IsCoprime r s) (hε : IsUnit ε) {n : ℕ} (hn : 1 ≤ n) :
    IsCoprime (wSeq r s ε n) r := by
  rcases hn.eq_or_lt with rfl | hn
  · exact isCoprime_one_left
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
    rw [wSeq_succ r s ε (by lia), add_comm]
    exact ((isCoprime_mul_unit_left_left hε _ _).mpr hrs.symm.pow_left).add_mul_left_left _

/-- `w_n` is coprime to `s`: `w_{n+1} ≡ r w_n² mod s`, by induction from `w_1 = 1`. -/
lemma isCoprime_wSeq_right (hrs : IsCoprime r s) {n : ℕ} (hn : 1 ≤ n) :
    IsCoprime (wSeq r s ε n) s := by
  induction n, hn using Nat.le_induction with
  | base => exact isCoprime_one_left
  | succ n hn ih =>
    obtain ⟨z, hz⟩ : s ∣ ε * s ^ (2 ^ n - 1) :=
      (dvd_pow_self s (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (by lia)))).mul_left ε
    rw [wSeq_succ r s ε hn, hz]
    exact (hrs.mul_left ih.pow_left).add_mul_left_left z

end wSeq

/-! ### The sequence `w` over `ℤ[1/s]` -/

section away

variable (r s ε : ℤ)

/-- `a = r / s` as an element of `ℤ[1/s]`. -/
noncomputable def aAway : Localization.Away s := r * IsLocalization.Away.invSelf s

lemma intCast_mul_invSelf : (s : Localization.Away s) * IsLocalization.Away.invSelf s = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Localization.Away s) s
  rwa [eq_intCast] at h

lemma isUnit_intCast_localizationAway : IsUnit (s : Localization.Away s) :=
  isUnit_iff_exists_inv.mpr ⟨_, intCast_mul_invSelf s⟩

/-- The rescaled polynomial `a X² + ε` over `ℤ[1/s]`, `a = r / s`. -/
noncomputable def normPolyAway : (Localization.Away s)[X] :=
  C (aAway r s) * X ^ 2 + C (ε : Localization.Away s)

lemma evenPoly_normPolyAway : EvenPoly (normPolyAway r s ε) := evenPoly_C_mul_X_sq_add_C _ _

/-- The sequence `w` in `ℤ[1/s]`. -/
def wSeqAway (n : ℕ) : Localization.Away s := wSeq r s ε n

variable {r s ε}

lemma wSeqAway_eq_mul_gammaSeq (hε : ε ^ 2 = 1) (n : ℕ) :
    wSeqAway r s ε n =
      (s : Localization.Away s) ^ (2 ^ (n - 1) - 1) * gammaSeq (normPolyAway r s ε) ε n :=
  intCast_wSeq (intCast_mul_invSelf s) hε n

private lemma associated_wSeqAway (hε : ε ^ 2 = 1) (n : ℕ) :
    Associated (wSeqAway r s ε n) (gammaSeq (normPolyAway r s ε) ε n) :=
  wSeqAway_eq_mul_gammaSeq hε n ▸
    associated_unit_mul_left _ _ ((isUnit_intCast_localizationAway s).pow _)

variable [NeZero s]

private lemma wSeqAway_ne_zero (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) : ∀ n ≥ 1, wSeqAway r s ε n ≠ 0 :=
  fun n hn h ↦ hw n hn (Int.cast_injective (h.trans (Int.cast_zero).symm))

private lemma gammaSeq_normPolyAway_ne_zero (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) :
    ∀ n ≥ 1, gammaSeq (normPolyAway r s ε) ε n ≠ 0 := fun n hn h ↦
  wSeqAway_ne_zero hw n hn (by rw [wSeqAway_eq_mul_gammaSeq hε, h, mul_zero])

private noncomputable local instance instNormalizationMonoidLocalizationAway :
    NormalizationMonoid (Localization.Away s) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid

private noncomputable local instance instNormalizedGCDMonoidLocalizationAway :
    NormalizedGCDMonoid (Localization.Away s) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

private lemma wSeqAway_associated_gcd (hε : ε ^ 2 = 1) (m n : ℕ) :
    Associated (gcd (wSeqAway r s ε m) (wSeqAway r s ε n)) (wSeqAway r s ε (m.gcd n)) :=
  ((associated_wSeqAway hε m).gcd (associated_wSeqAway hε n)).trans
    ((gammaSeq_associated_gcd (evenPoly_normPolyAway r s ε)
      (by rw [← Int.cast_pow, hε, Int.cast_one]) m n).trans (associated_wSeqAway hε _).symm)

open Classical in
private lemma factorization_wSeqAway_shape (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) :
    ∀ p : Localization.Away s, Prime p → normalize p = p → ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1,
      factorization (wSeqAway r s ε k) p = if m ∣ k then E else 0 :=
  fun p hp hpn ↦ by
    obtain ⟨m, hm, E, hE⟩ := factorization_gammaSeq_shape (evenPoly_normPolyAway r s ε)
      (by rw [← Int.cast_pow, hε, Int.cast_one]) (gammaSeq_normPolyAway_ne_zero hε hw) hp hpn
    exact ⟨m, hm, E, fun k hk ↦ by rw [(associated_wSeqAway hε k).factorization_eq]; exact hE k hk⟩

/-- The Möbius factors of `w` in `ℤ[1/s]` are pairwise relatively prime: `w` is, up to units, the
`γ`-sequence of the rescaled polynomial, a strong divisibility sequence with the
constant-valuation shape. -/
theorem isRelPrime_moebiusFactorR_wSeqAway (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    IsRelPrime (moebiusFactorR (wSeqAway r s ε) m) (moebiusFactorR (wSeqAway r s ε) n) := by
  classical
  exact moebiusFactorR_isRelPrime (wSeqAway_ne_zero hw) (wSeqAway_associated_gcd hε)
    (factorization_wSeqAway_shape hε hw) hm hn hmn

private lemma denProd_wSeqAway_dvd_numProd_wSeqAway (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    denProd (wSeqAway r s ε) n ∣ numProd (wSeqAway r s ε) n :=
  denProd_dvd_numProd (wSeqAway_ne_zero hw) (wSeqAway_associated_gcd hε) hn

end away

/-! ### The integer Möbius factors `β` -/

section betaInt

variable {r s ε : ℤ}

private lemma isCoprime_denProd_wSeq (hrs : IsCoprime r s) (n : ℕ) :
    IsCoprime (denProd (wSeq r s ε) n) s :=
  IsCoprime.prod_left fun x hx ↦ isCoprime_wSeq_right hrs (Nat.pos_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal (Finset.mem_of_mem_filter x hx)))

/-- The denominator product of the Möbius factor of `w` divides the numerator product: in
`ℤ[1/s]`, where `w` is a strong divisibility sequence up to units, this is `denProd_dvd_numProd`,
and it descends to `ℤ` because the denominator product is coprime to `s`. -/
theorem denProd_wSeq_dvd_numProd_wSeq (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    denProd (wSeq r s ε) n ∣ numProd (wSeq r s ε) n := by
  have := NeZero.mk hs
  refine IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime (S := Localization.Away s) ?_
    (isCoprime_denProd_wSeq hrs n)
  rw [RingHom.ext_int (algebraMap ℤ _) (Int.castRingHom _), map_denProd, map_numProd]
  exact denProd_wSeqAway_dvd_numProd_wSeqAway hε hw hn

/-- The integer Möbius factors `β_n = ∏_{d ∣ n} w_d^{μ(n/d)}` of the sequence `w`, as elements of
`ℤ` (`QuadraticIterates.intCast_betaInt`). -/
noncomputable def betaInt (r s ε : ℤ) (n : ℕ) : ℤ := moebiusFactorR (wSeq r s ε) n

lemma betaInt_eq_moebiusFactorR (n : ℕ) : betaInt r s ε n = moebiusFactorR (wSeq r s ε) n := rfl

@[simp] lemma betaInt_one : betaInt r s ε 1 = 1 := by simp [betaInt_eq_moebiusFactorR]

variable (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0)
include hs hrs hε hw

theorem betaInt_mul_denProd {n : ℕ} (hn : 1 ≤ n) :
    betaInt r s ε n * denProd (wSeq r s ε) n = numProd (wSeq r s ε) n :=
  moebiusFactorR_mul_denProd_of_dvd hw (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hn)

/-- The image of `β_n` in `ℚ` is the Möbius product `∏_{ed = n} w_d^{μ(e)}`. -/
theorem intCast_betaInt {n : ℕ} (hn : 1 ≤ n) :
    (betaInt r s ε n : ℚ) = moebiusFactorK (wSeq r s ε) n :=
  algebraMap_moebiusFactorR_of_dvd hw (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hn)

theorem betaInt_ne_zero {n : ℕ} (hn : 1 ≤ n) : betaInt r s ε n ≠ 0 :=
  moebiusFactorR_ne_zero_of_dvd hw (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hn)

/-- Möbius inversion: `w_n = ∏_{d ∣ n} β_d`. -/
theorem wSeq_eq_prod_betaInt {n : ℕ} (hn : 1 ≤ n) :
    wSeq r s ε n = ∏ d ∈ n.divisors, betaInt r s ε d :=
  prod_moebiusFactorR_of_dvd hw hn fun _ hd ↦
    denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw (Nat.pos_of_mem_divisors hd)

theorem isCoprime_betaInt_right {n : ℕ} (hn : 1 ≤ n) : IsCoprime (betaInt r s ε n) s :=
  IsCoprime.of_mul_left_left (y := denProd (wSeq r s ε) n)
    (betaInt_mul_denProd hs hrs hε hw hn ▸ IsCoprime.prod_left fun x hx ↦
      isCoprime_wSeq_right hrs (Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal (Finset.mem_of_mem_filter x hx))))

theorem isCoprime_betaInt_left {n : ℕ} (hn : 1 ≤ n) : IsCoprime (betaInt r s ε n) r :=
  IsCoprime.of_mul_left_left (y := denProd (wSeq r s ε) n)
    (betaInt_mul_denProd hs hrs hε hw hn ▸ IsCoprime.prod_left fun x hx ↦
      isCoprime_wSeq_left hrs (IsUnit.of_pow_eq_one hε two_ne_zero) (Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal (Finset.mem_of_mem_filter x hx))))

/-- The integer Möbius factors are pairwise coprime: this holds in `ℤ[1/s]`
(`QuadraticIterates.isRelPrime_moebiusFactorR_wSeqAway`) and descends since `β_m` is coprime
to `s`. -/
theorem isCoprime_betaInt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    IsCoprime (betaInt r s ε m) (betaInt r s ε n) := by
  have := NeZero.mk hs
  refine (IsLocalization.Away.isRelPrime_of_isRelPrime_algebraMap (S := Localization.Away s) hs ?_
    (isCoprime_betaInt_right hs hrs hε hw hm)).isCoprime
  rw [RingHom.ext_int (algebraMap ℤ _) (Int.castRingHom _), betaInt_eq_moebiusFactorR,
    betaInt_eq_moebiusFactorR,
    map_moebiusFactorR _ (wSeqAway_ne_zero hw) (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hm),
    map_moebiusFactorR _ (wSeqAway_ne_zero hw) (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hn)]
  exact isRelPrime_moebiusFactorR_wSeqAway hε hw hm hn hmn

end betaInt

end QuadraticIterates

end
