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
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Defs
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
* The sign worlds: `w_n > 0` for `a > 0` (`QuadraticIterates.wSeq_pos_of_pos`), for
  `-1 < a < 0` (`QuadraticIterates.wSeq_pos_of_neg_lt`) and, in Stoll's normalization `ε = -1`
  with `|r|` in place of `r`, for `a ≤ -2` (`QuadraticIterates.wSeq_pos_of_two_mul_le`); then
  `β_n > 0` (`QuadraticIterates.betaInt_pos`).
* `QuadraticIterates.reflNum`: the numerator `N_k = w_k s^(2^(k-1)) + w_{k+1}` of `γ_k + γ_{k+1}`,
  coprime to `s`, whose divisors are the moduli of the reflection lemma.

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

@[simp] lemma wSeq_two : wSeq r s ε 2 = r + ε * s := (wSeq_succ r s ε le_rfl).trans (by simp)

variable {r s ε}

/-- In a commutative ring `S` in which `s` is invertible, with inverse `u`, the cast of `w_n` is
`s^(2^(n-1) - 1) γ_n` for the `γ`-sequence of `(r u) X² + ε` with sign `ε`. -/
theorem intCast_wSeq {S : Type*} [CommRing S] {u : S} (hu : (s : S) * u = 1) (hε : ε ^ 2 = 1)
    (n : ℕ) : (wSeq r s ε n : S) =
      (s : S) ^ (2 ^ (n - 1) - 1) * gammaSeq (C ((r : S) * u) * X ^ 2 + C (ε : S)) (ε : S) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [← sq, Int.cast_sq_eq_one_of_sq_eq_one (S := S) hε]
    · rw [wSeq_succ r s ε hn, gammaSeq_succ _ _ hn, Nat.add_sub_cancel, Nat.two_pow_sub_one_eq hn,
        eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_C]
      push_cast
      rw [ih]
      linear_combination (-(r : S) * ((s : S) ^ (2 ^ (n - 1) - 1)) ^ 2 *
        gammaSeq (C ((r : S) * u) * X ^ 2 + C (ε : S)) (ε : S) n ^ 2) * hu

/-- `w_n` is coprime to `r`: `w_{n+1} ≡ ε s^(2^n - 1) mod r`. -/
lemma isCoprime_wSeq_left (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsCoprime (wSeq r s ε n) r := by
  rcases hn.eq_or_lt with rfl | hn
  · exact isCoprime_one_left
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
    rw [wSeq_succ r s ε (by lia), add_comm]
    exact ((isCoprime_mul_unit_left_left (IsUnit.of_pow_eq_one hε two_ne_zero) _ _).mpr
      hrs.symm.pow_left).add_mul_left_left _

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

lemma aAway_eq : aAway r s = r * IsLocalization.Away.invSelf s := rfl

lemma intCast_mul_invSelf : (s : Localization.Away s) * IsLocalization.Away.invSelf s = 1 :=
  eq_intCast (algebraMap ℤ (Localization.Away s)) s ▸ IsLocalization.Away.mul_invSelf s

lemma isUnit_intCast_localizationAway : IsUnit (s : Localization.Away s) :=
  eq_intCast (algebraMap ℤ (Localization.Away s)) s ▸ IsLocalization.Away.algebraMap_isUnit s

/-- The rescaled polynomial `a X² + ε` over `ℤ[1/s]`, `a = r / s`. -/
noncomputable def normPolyAway : (Localization.Away s)[X] :=
  C (aAway r s) * X ^ 2 + C (ε : Localization.Away s)

lemma evenPoly_normPolyAway : EvenPoly (normPolyAway r s ε) := evenPoly_C_mul_X_sq_add_C _ _

lemma normPolyAway_eq :
    normPolyAway r s ε = C (aAway r s) * X ^ 2 + C (ε : Localization.Away s) := rfl

@[simp] lemma eval_zero_normPolyAway : (normPolyAway r s ε).eval 0 = ε := by
  simp [normPolyAway_eq]

/-- The sequence `w` in `ℤ[1/s]`. -/
def wSeqAway (n : ℕ) : Localization.Away s := wSeq r s ε n

lemma wSeqAway_eq_intCast (n : ℕ) : wSeqAway r s ε n = (wSeq r s ε n : Localization.Away s) := rfl

variable {r s ε}

lemma wSeqAway_eq_mul_gammaSeq (hε : ε ^ 2 = 1) (n : ℕ) :
    wSeqAway r s ε n =
      (s : Localization.Away s) ^ (2 ^ (n - 1) - 1) * gammaSeq (normPolyAway r s ε) ε n := by
  rw [wSeqAway_eq_intCast, normPolyAway_eq, aAway_eq]
  exact intCast_wSeq (intCast_mul_invSelf s) hε n

lemma gammaSeq_normPolyAway_one (hε : ε ^ 2 = 1) : gammaSeq (normPolyAway r s ε) ε 1 = 1 := by
  rw [gammaSeq_one, eval_zero_normPolyAway, ← sq, Int.cast_sq_eq_one_of_sq_eq_one hε]

lemma wSeqAway_two (hε : ε ^ 2 = 1) :
    wSeqAway r s ε 2 = s * gammaSeq (normPolyAway r s ε) ε 2 := by
  rw [wSeqAway_eq_mul_gammaSeq hε]
  norm_num

private lemma associated_wSeqAway (hε : ε ^ 2 = 1) (n : ℕ) :
    Associated (wSeqAway r s ε n) (gammaSeq (normPolyAway r s ε) ε n) :=
  wSeqAway_eq_mul_gammaSeq hε n ▸
    associated_unit_mul_left _ _ ((isUnit_intCast_localizationAway s).pow _)

variable [NeZero s]

private lemma wSeqAway_ne_zero (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) : ∀ n ≥ 1, wSeqAway r s ε n ≠ 0 :=
  fun n hn ↦ wSeqAway_eq_intCast r s ε n ▸ Int.cast_ne_zero.mpr (hw n hn)

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
      (Int.cast_sq_eq_one_of_sq_eq_one hε) m n).trans (associated_wSeqAway hε _).symm)

open Classical in
private lemma factorization_wSeqAway_shape (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) :
    ∀ p : Localization.Away s, Prime p → normalize p = p → ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1,
      factorization (wSeqAway r s ε k) p = if m ∣ k then E else 0 :=
  fun p hp hpn ↦ by
    obtain ⟨m, hm, E, hE⟩ := factorization_gammaSeq_shape (evenPoly_normPolyAway r s ε)
      (Int.cast_sq_eq_one_of_sq_eq_one hε) (gammaSeq_normPolyAway_ne_zero hε hw) hp hpn
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

/-- The denominator product of the Möbius factor of `w` divides the numerator product: in
`ℤ[1/s]`, where `w` is a strong divisibility sequence up to units, this is `denProd_dvd_numProd`,
and it descends to `ℤ` because the denominator product is coprime to `s`. -/
theorem denProd_wSeq_dvd_numProd_wSeq (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    denProd (wSeq r s ε) n ∣ numProd (wSeq r s ε) n := by
  have := NeZero.mk hs
  refine IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime (S := Localization.Away s) ?_
    (isCoprime_denProd (fun _ hd ↦ isCoprime_wSeq_right hrs hd) n)
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

/-- `β_2 = w_2 = r + εs`: `w_2 = β_1 β_2` with `β_1 = 1`. -/
theorem betaInt_two : betaInt r s ε 2 = r + ε * s := by
  have h := (wSeq_eq_prod_betaInt hs hrs hε hw one_le_two).symm
  rwa [Nat.prime_two.divisors, Finset.prod_pair one_lt_two.ne, betaInt_one, one_mul, wSeq_two] at h

theorem isCoprime_betaInt_right {n : ℕ} (hn : 1 ≤ n) : IsCoprime (betaInt r s ε n) s :=
  IsCoprime.of_mul_left_left (y := denProd (wSeq r s ε) n) (betaInt_mul_denProd hs hrs hε hw hn ▸
    isCoprime_numProd (fun _ hd ↦ isCoprime_wSeq_right hrs hd) n)

theorem isCoprime_betaInt_left {n : ℕ} (hn : 1 ≤ n) : IsCoprime (betaInt r s ε n) r :=
  IsCoprime.of_mul_left_left (y := denProd (wSeq r s ε) n) (betaInt_mul_denProd hs hrs hε hw hn ▸
    isCoprime_numProd (fun _ hd ↦ isCoprime_wSeq_left hrs hε hd) n)

/-- The integer Möbius factors are pairwise coprime: this holds in `ℤ[1/s]`
(`QuadraticIterates.isRelPrime_moebiusFactorR_wSeqAway`) and descends since `β_m` is coprime
to `s`. -/
theorem isCoprime_betaInt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    IsCoprime (betaInt r s ε m) (betaInt r s ε n) := by
  have := NeZero.mk hs
  refine (IsLocalization.Away.isRelPrime_of_isRelPrime_algebraMap (S := Localization.Away s) ?_
    (isCoprime_betaInt_right hs hrs hε hw hm)).isCoprime
  rw [RingHom.ext_int (algebraMap ℤ _) (Int.castRingHom _), betaInt_eq_moebiusFactorR,
    betaInt_eq_moebiusFactorR,
    map_moebiusFactorR _ (wSeqAway_ne_zero hw) (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hm),
    map_moebiusFactorR _ (wSeqAway_ne_zero hw) (denProd_wSeq_dvd_numProd_wSeq hs hrs hε hw hn)]
  exact isRelPrime_moebiusFactorR_wSeqAway hε hw hm hn hmn

end betaInt

section sign

variable {r s ε : ℤ}

/-! ### The sign worlds -/

/-- For `a > 0` (and `ε = 1`), `w_n > 0` for all `n ≥ 1`. -/
lemma wSeq_pos_of_pos (hr : 0 < r) (hs : 0 < s) : ∀ n ≥ 1, 0 < wSeq r s 1 n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [wSeq_succ r s 1 hn]
    positivity

/-- For `-1 < a < 0`, i.e. `-s < r < 0` (and `ε = 1`), `0 < w_n ≤ s^(2^(n-1) - 1)`: the
`γ`-sequence stays in `(0, 1]`. -/
private lemma wSeq_pos_and_le_of_neg_lt (hr : r < 0) (hrs : -s < r) :
    ∀ n ≥ 1, 0 < wSeq r s 1 n ∧ wSeq r s 1 n ≤ s ^ (2 ^ (n - 1) - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs : 0 < s := by lia
    have h1 : r * (s ^ (2 ^ (n - 1) - 1)) ^ 2 ≤ r * wSeq r s 1 n ^ 2 :=
      mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ih.1.le ih.2 2) hr.le
    have h2 : 0 < s ^ (2 ^ (n - 1) - 1) := pow_pos hs _
    have h3 : 0 ≤ wSeq r s 1 n ^ 2 := sq_nonneg _
    rw [wSeq_succ r s 1 hn, Nat.add_sub_cancel, pow_two_pow_sub_one_eq s hn, one_mul]
    constructor <;> nlinarith

lemma wSeq_pos_of_neg_lt (hr : r < 0) (hrs : -s < r) : ∀ n ≥ 1, 0 < wSeq r s 1 n :=
  fun n hn ↦ (wSeq_pos_and_le_of_neg_lt hr hrs n hn).1

/-- For `a ≤ -2`, i.e. `2s ≤ |r|`, in Stoll's normalization (`ε = -1`, `|r|` in place of `r`):
`w_n ≥ s^(2^(n-1) - 1)`, the `γ`-sequence stays `≥ 1`. -/
lemma pow_le_wSeq_of_two_mul_le (hs : 0 < s) (hr : 2 * s ≤ r) :
    ∀ n ≥ 1, s ^ (2 ^ (n - 1) - 1) ≤ wSeq r s (-1) n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h2 : 0 < s ^ (2 ^ (n - 1) - 1) := pow_pos hs _
    have h1 : 2 * s * (s ^ (2 ^ (n - 1) - 1)) ^ 2 ≤ r * wSeq r s (-1) n ^ 2 :=
      mul_le_mul hr (pow_le_pow_left₀ h2.le ih 2) (by positivity) (by lia)
    have h3 : 0 < s * (s ^ (2 ^ (n - 1) - 1)) ^ 2 := by positivity
    rw [wSeq_succ r s (-1) hn, Nat.add_sub_cancel, pow_two_pow_sub_one_eq s hn]
    nlinarith

lemma wSeq_pos_of_two_mul_le (hs : 0 < s) (hr : 2 * s ≤ r) : ∀ n ≥ 1, 0 < wSeq r s (-1) n :=
  fun n hn ↦ (pow_pos hs _).trans_le (pow_le_wSeq_of_two_mul_le hs hr n hn)

/-- If all `w_n > 0`, then `β_n > 0`: `β_n` is a quotient of products of the `w_d`. -/
theorem betaInt_pos (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, 0 < wSeq r s ε n) {n : ℕ} (hn : 1 ≤ n) : 0 < betaInt r s ε n :=
  (pos_iff_pos_of_mul_pos (betaInt_mul_denProd hs hrs hε (fun n hn ↦ (hw n hn).ne') hn ▸
    numProd_pos (fun _ hd ↦ hw _ hd) n)).mpr (denProd_pos (fun _ hd ↦ hw _ hd) n)

/-! ### The numerator of `γ_k + γ_{k+1}` -/

/-- `N_k = w_k s^(2^(k-1)) + w_{k+1}`, the numerator of `γ_k + γ_{k+1}`
(`QuadraticIterates.intCast_wSeq`): its divisors coprime to `s` are the moduli of the reflection
lemma `QuadraticIterates.not_isSquare_betaInt_of_dvd_reflNum`. -/
def reflNum (r s ε : ℤ) (k : ℕ) : ℤ := wSeq r s ε k * s ^ 2 ^ (k - 1) + wSeq r s ε (k + 1)

lemma reflNum_eq (k : ℕ) :
    reflNum r s ε k = wSeq r s ε k * s ^ 2 ^ (k - 1) + wSeq r s ε (k + 1) := rfl

/-- `N_k ≡ w_{k+1} mod s` is coprime to `s`. -/
lemma isCoprime_reflNum_right (hrs : IsCoprime r s) {k : ℕ} (hk : 1 ≤ k) :
    IsCoprime (reflNum r s ε k) s := by
  rw [reflNum_eq, add_comm, ← mul_pow_sub_one (Nat.two_pow_pos _).ne' s, mul_left_comm]
  exact (isCoprime_wSeq_right hrs (Nat.le_succ_of_le hk)).add_mul_left_left _

lemma reflNum_one : reflNum r s ε 1 = r + (1 + ε) * s := by
  rw [reflNum_eq, wSeq_succ r s ε le_rfl, wSeq_one]
  ring

lemma reflNum_pos (hs : 0 ≤ s) (hw : ∀ n ≥ 1, 0 < wSeq r s ε n) {k : ℕ} (hk : 1 ≤ k) :
    0 < reflNum r s ε k := by
  have := hw k hk
  have := hw (k + 1) (by lia)
  have := pow_nonneg hs (2 ^ (k - 1))
  rw [reflNum_eq]
  positivity

end sign

end QuadraticIterates

end
