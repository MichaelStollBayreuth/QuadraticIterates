/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Main
public import QuadraticIterates.Rational.Sequence

import Mathlib.Tactic.LinearCombination
import QuadraticIterates.ArchMath1992.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Squares

/-!
# Square classes for a rational parameter, and the shared-part lemma

For `a = εr/s` (`ε² = 1`, `r` and `s` coprime), `c_n = r w_n / s^(2^(n-1))` for `n ≥ 2`, where
`w = QuadraticIterates.wSeq r s ε` (`QuadraticIterates.cSeq_div_eq`), so in `ℚˣ/(ℚˣ)²` the class
of `c_n` is that of `r w_n`, and the class of `b_n` is `μ(n) [-εs] + [β_n]` with the integer
Möbius factors `β_n = QuadraticIterates.betaInt r s ε n` (`QuadraticIterates.sqClass_bSeq_div`).
Hence a square subproduct of the `b_n` gives a square integer `(-εs)^k r^c ∏ β_n`, and by the
pairwise coprimality of the `β_n` and their coprimality to `r` and `s`
(`Int.isSquare_abs_of_isSquare_mul_prod_of_pairwise_isCoprime`) some `|β_n|` with `n ≥ 2` is a
square, unless the subproduct is `b_1 = -a` alone. So if `-εrs` and all `|β_n|`, `n ≥ 2`, are
non-squares, the `b_n` are 2-independent (`QuadraticIterates.twoIndependent_bSeq_div`), hence the
`c_n` are, all iterates are irreducible (Lemma 1.2), and `Ω_n ≅ [C₂]ⁿ` for all `n` by the
Section 1 theorem: the **shared-part lemma** of the rational program,
`QuadraticIterates.nonempty_mulEquiv_of_forall_not_isSquare_abs_betaInt`.

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open Polynomial
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

variable {r s ε : ℤ}

/-! ### The sequences `c` and `b` of `a = εr/s` -/

private lemma isUnit_intCast_of_sq_eq_one (hε : ε ^ 2 = 1) : IsUnit (ε : ℚ) :=
  IsUnit.of_pow_eq_one (mod_cast hε : (ε : ℚ) ^ 2 = 1) two_ne_zero

/-- For `a = εr/s`, `c_n = r w_n / s^(2^(n-1))` for `n ≥ 2`:
`QuadraticIterates.cSeq_eq_mul_gammaSeq` with `εa = r/s`, and `QuadraticIterates.intCast_wSeq`
over `ℚ`. -/
theorem cSeq_div_eq (hs : s ≠ 0) (hε : ε ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    cSeq (ε * r / s : ℚ) n = r * wSeq r s ε n / s ^ 2 ^ (n - 1) := by
  have hs' : (s : ℚ) ≠ 0 := mod_cast hs
  have hu : (s : ℚ) * (s : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hs'
  have hε' : (ε : ℚ) ^ 2 = 1 := mod_cast hε
  have hεa : (ε : ℚ) * (ε * r / s) = r * (s : ℚ)⁻¹ := by
    rw [← mul_div_assoc, ← mul_assoc, ← sq, hε', one_mul, div_eq_mul_inv]
  have hpow : (s : ℚ) ^ 2 ^ (n - 1) = s * s ^ (2 ^ (n - 1) - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  rw [cSeq_eq_mul_gammaSeq _ hε' hn, hεa, intCast_wSeq hu hε n, hpow]
  have := pow_ne_zero (2 ^ (n - 1) - 1) hs'
  field

lemma cSeq_div_ne_zero (hs : s ≠ 0) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0)
    (hr : r ≠ 0) : ∀ k ≥ 1, cSeq (ε * r / s : ℚ) k ≠ 0 := fun k hk ↦ by
  rcases (show k = 1 ∨ 2 ≤ k by lia) with rfl | hk2
  · have := (isUnit_intCast_of_sq_eq_one hε).ne_zero
    simp [hr, hs, this]
  · rw [cSeq_div_eq hs hε hk2]
    exact div_ne_zero (mul_ne_zero (mod_cast hr) (mod_cast hw k hk))
      (pow_ne_zero _ (mod_cast hs))

/-- The square class of `c_n`, `n ≥ 2`, is that of `r w_n`: the denominator `s^(2^(n-1))` is a
square. -/
theorem sqClass_cSeq_div (hs : s ≠ 0) (hε : ε ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    sqClass (cSeq (ε * r / s : ℚ) n) = sqClass ((r * wSeq r s ε n : ℤ) : ℚ) := by
  have h2 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    lia
  rw [cSeq_div_eq hs hε hn, h2, pow_mul, sqClass_div_sq _ (pow_ne_zero _ (mod_cast hs))]
  push_cast
  rfl

/-- The square class of `-a = -εr/s` is that of `-εs · r`. -/
theorem sqClass_neg_div (hs : s ≠ 0) :
    sqClass (-(ε * r / s) : ℚ) = sqClass ((-(ε * s) * r : ℤ) : ℚ) := by
  have hs' : (s : ℚ) ≠ 0 := mod_cast hs
  rw [← sqClass_div_sq (((-(ε * s) * r : ℤ) : ℚ)) hs']
  congr 1
  push_cast
  field

/-! ### The square classes of `b_n` and `β_n` -/

/-- In `ℚˣ/(ℚˣ)²`, the class of `β_n` is the Möbius-weighted sum of the classes of the `w_d`. -/
theorem sqClass_betaInt (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    sqClass (betaInt r s ε n : ℚ) =
      ∑ x ∈ n.divisorsAntidiagonal, (μ x.1) • sqClass (wSeq r s ε x.2 : ℚ) := by
  rw [intCast_betaInt hs hrs hε hw hn, moebiusFactorK_eq_prod]
  simp only [eq_intCast]
  exact sqClass_prod_zpow _ fun x hx ↦ mod_cast ne_zero_of_mem_divisorsAntidiagonal hw hx

/-- On the divisors `d ≥ 2` of `n`, the class of `c_d` is `[r] + [w_d]`. -/
private lemma sum_erase_sqClass_cSeq_div (hs : s ≠ 0) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (hr : r ≠ 0) (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal.erase (n, 1), (μ x.1) • sqClass (cSeq (ε * r / s : ℚ) x.2) =
      (∑ x ∈ n.divisorsAntidiagonal.erase (n, 1), μ x.1) • sqClass (r : ℚ) +
        ∑ x ∈ n.divisorsAntidiagonal.erase (n, 1), (μ x.1) • sqClass (wSeq r s ε x.2 : ℚ) := by
  rw [← zmultiplesHom_apply, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [zmultiplesHom_apply]
  have hx' := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_of_mem_erase hx)
  have hx2 : 2 ≤ x.2 := by
    rcases (show x.2 = 0 ∨ x.2 = 1 ∨ 2 ≤ x.2 by lia) with h | h | h
    · rw [h, mul_zero] at hx'
      exact (hx'.2 hx'.1.symm).elim
    · exact absurd (Prod.ext (by simpa [h] using hx'.1) h) (Finset.ne_of_mem_erase hx)
    · exact h
  rw [sqClass_cSeq_div hs hε hx2, Int.cast_mul, sqClass_mul (mod_cast hr)
    (mod_cast hw _ (by lia)), zsmul_add]

/-- **Square classes.** For `a = εr/s` and `n ≥ 2`, `[b_n] = μ(n) [-εs] + [β_n]` in `ℚˣ/(ℚˣ)²`. -/
theorem sqClass_bSeq_div (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (hr : r ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    sqClass (bSeq (ε * r / s : ℚ) n) =
      (μ n) • sqClass (-(ε * s) : ℚ) + sqClass (betaInt r s ε n : ℚ) := by
  have hmem : (n, 1) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, by lia⟩
  have hμ := ArithmeticFunction.sum_divisorsAntidiagonal_moebius_eq_zero hn
  rw [← Finset.add_sum_erase _ _ hmem] at hμ
  rw [sqClass_bSeq_eq_sum_divisorsAntidiagonal (cSeq_div_ne_zero hs hε hw hr),
    sqClass_betaInt hs hrs hε hw (by lia), ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem, sum_erase_sqClass_cSeq_div hs hε hw hr, cSeq_one,
    sqClass_neg_div hs, Int.cast_mul,
    sqClass_mul (by simp [hs, (isUnit_intCast_of_sq_eq_one hε).ne_zero]) (mod_cast hr),
    wSeq_one, Int.cast_one, sqClass_one, zsmul_zero, zero_add,
    show ∑ x ∈ n.divisorsAntidiagonal.erase (n, 1), μ x.1 = -μ n by linear_combination hμ,
    neg_zsmul (sqClass (r : ℚ)) (μ n), zsmul_add]
  push_cast
  abel

/-! ### The shared-part lemma -/

private lemma bSeq_div_ne_zero (hs : s ≠ 0) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0)
    (hr : r ≠ 0) (n : ℕ) : bSeq (ε * r / s : ℚ) n ≠ 0 := by
  rw [bSeq_eq_moebiusFactorK]
  exact moebiusFactorK_ne_zero (cSeq_div_ne_zero hs hε hw hr) n

/-- The class of `b_{i+1}` uniformly in `i`: `μ(i+1) [-εs] + [β_{i+1}]`, plus `[r]` at `i = 0`. -/
private lemma sqClass_bSeq_div_succ (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (hr : r ≠ 0) (i : ℕ) :
    sqClass (bSeq (ε * r / s : ℚ) (i + 1)) = (μ (i + 1)) • sqClass (-(ε * s) : ℚ) +
      sqClass (betaInt r s ε (i + 1) : ℚ) + if i = 0 then sqClass (r : ℚ) else 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [zero_add, bSeq_one, sqClass_neg_div hs, Int.cast_mul,
      sqClass_mul (by simp [hs, (isUnit_intCast_of_sq_eq_one hε).ne_zero]) (mod_cast hr),
      ArithmeticFunction.moebius_apply_one, one_zsmul, betaInt_one, Int.cast_one, sqClass_one,
      ite_eq_left rfl]
    push_cast
    abel
  · rw [sqClass_bSeq_div hs hrs hε hw hr (by lia), ite_eq_right (by lia)]
    exact (add_zero _).symm

private lemma isCoprime_betaInt_unit (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) {n : ℕ} (hn : 1 ≤ n) (k c : ℕ) :
    IsCoprime (betaInt r s ε n) ((-(ε * s)) ^ k * r ^ c) :=
  ((((show IsCoprime (betaInt r s ε n) ε from
    ⟨0, ε, by rw [zero_mul, zero_add, ← sq, hε]⟩).mul_right
      (isCoprime_betaInt_right hs hrs hε hw hn)).neg_right).pow_right).mul_right
    (isCoprime_betaInt_left hs hrs hε hw hn).pow_right

/-- If a subproduct of the `b_{i+1}` is a square, then `(-εs)^k r^c ∏ β_{i+1}` is a square in `ℤ`
for suitable `k`, `c`. -/
private lemma exists_isSquare_mul_prod_betaInt (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (hr : r ≠ 0) {m : ℕ} {S : Finset (Fin m)}
    (hsq : IsSquare (∏ i ∈ S, bSeq (ε * r / s : ℚ) ((i : ℕ) + 1))) :
    ∃ k c : ℕ, IsSquare ((-(ε * s)) ^ k * r ^ c * ∏ i ∈ S, betaInt r s ε ((i : ℕ) + 1)) := by
  have hβ (i : Fin m) : (betaInt r s ε ((i : ℕ) + 1) : ℚ) ≠ 0 :=
    mod_cast betaInt_ne_zero hs hrs hε hw i.1.succ_pos
  have hεs : (-(ε * s) : ℚ) ≠ 0 := by simp [hs, (isUnit_intCast_of_sq_eq_one hε).ne_zero]
  rw [isSquare_prod_iff_sum_sqClass_eq_zero fun i _ ↦ bSeq_div_ne_zero hs hε hw hr _,
    Finset.sum_congr rfl fun (i : Fin m) _ ↦ sqClass_bSeq_div_succ hs hrs hε hw hr i,
    Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    ← sqClass_pow, ← sqClass_prod fun i _ ↦ hβ i,
    show ∑ i ∈ S, μ ((i : ℕ) + 1) • sqClass (-(ε * s) : ℚ) =
      (∑ i ∈ S, μ ((i : ℕ) + 1)) • sqClass (-(ε * s) : ℚ) from
        (map_sum (zmultiplesHom (SquareClasses ℚ) (sqClass (-(ε * s) : ℚ))) _ _).symm,
    zsmul_eq_natAbs_nsmul, ← sqClass_pow, ← sqClass_mul (pow_ne_zero _ hεs)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hβ i), ← sqClass_mul (mul_ne_zero (pow_ne_zero _ hεs)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hβ i)) (pow_ne_zero _ (mod_cast hr)),
    sqClass_eq_zero_iff, mul_right_comm] at hsq
  exact ⟨_, _, Rat.isSquare_intCast_iff.mp (by push_cast; exact hsq)⟩

/-- **The shared part, 2-independence.** For `a = εr/s` with `-εrs` not a square and `|β_n|` not a
square for every `n ≥ 2`, the `b_1, …, b_m` are 2-independent for every `m`. -/
theorem twoIndependent_bSeq_div (hs : s ≠ 0) (hrs : IsCoprime r s) (hε : ε ^ 2 = 1)
    (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (ha : ¬IsSquare (-(ε * r * s)))
    (hβ : ∀ n ≥ 2, ¬IsSquare |betaInt r s ε n|) (m : ℕ) :
    TwoIndependent (fun i : Fin m ↦ bSeq (ε * r / s : ℚ) ((i : ℕ) + 1)) := fun S hS hsq ↦ by
  have hr : r ≠ 0 := fun h ↦ ha (by simp [h])
  rcases em (∃ i ∈ S, (i : ℕ) ≠ 0) with ⟨i, hi, hi0⟩ | h0
  · obtain ⟨k, c, hsq'⟩ := exists_isSquare_mul_prod_betaInt hs hrs hε hw hr hsq
    refine hβ ((i : ℕ) + 1) (by lia) (Int.isSquare_abs_of_isSquare_mul_prod_of_pairwise_isCoprime
      (fun i _ j _ hij ↦ isCoprime_betaInt hs hrs hε hw i.1.succ_pos j.1.succ_pos
        (by simpa [Fin.ext_iff] using hij))
      (fun i _ ↦ isCoprime_betaInt_unit hs hrs hε hw i.1.succ_pos k c) hsq' hi)
  · have h0 (i : Fin m) (hi : i ∈ S) : (i : ℕ) = 0 := by_contra fun h ↦ h0 ⟨i, hi, h⟩
    obtain ⟨i, hi⟩ := hS
    rw [Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨⟨i, hi⟩, fun j hj ↦ Fin.ext ((h0 j hj).trans (h0 i hi).symm)⟩, Finset.prod_singleton,
      h0 i hi, zero_add, bSeq_one] at hsq
    have := Int.isSquare_mul_of_isSquare_div (P := -(ε * r)) (Q := s) (by push_cast; rwa [neg_div])
    exact ha (by rwa [neg_mul] at this)

/-- **The shared-part lemma.** For `a = εr/s` with `-εrs` not a square and `|β_n|` not a square for
every `n ≥ 2`, `Ω_n ≅ [C₂]ⁿ` for all `n`: the `b_k` are 2-independent, hence the `c_k`, so no `c_k`
is a square and all iterates are irreducible (Lemma 1.2), and the Section 1 theorem applies. -/
theorem nonempty_mulEquiv_of_forall_not_isSquare_abs_betaInt (hs : s ≠ 0) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0) (ha : ¬IsSquare (-(ε * r * s)))
    (hβ : ∀ n ≥ 2, ¬IsSquare |betaInt r s ε n|) (n : ℕ) :
    Nonempty (GaloisGroup (ε * r / s : ℚ) n ≃* WreathPower n) := by
  have hr : r ≠ 0 := fun h ↦ ha (by simp [h])
  have hb := twoIndependent_bSeq_div hs hrs hε hw ha hβ
  have hc (m : ℕ) : TwoIndependent (fun i : Fin m ↦ cSeq (ε * r / s : ℚ) ((i : ℕ) + 1)) :=
    (section1_b_iff_c (cSeq_div_ne_zero hs hε hw hr) m).mpr (hb m)
  have hirr (k : ℕ) : Irreducible fℚ[(ε * r / s : ℚ), k] :=
    irreducible_iteratedPoly_of_not_isSquare_cSeq fun j hj _ ↦ by
      simpa [Nat.sub_add_cancel hj] using (hc j).not_isSquare ⟨j - 1, by lia⟩
  exact ((section1_tfae_of_irreducible hirr n).out 1 3).mpr (hb n)

end QuadraticIterates

end
