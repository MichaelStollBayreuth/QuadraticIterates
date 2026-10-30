/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.TwoIndependent
public import QuadraticIterates.Sequence.MoebiusQuotient

import Mathlib.LinearAlgebra.Dimension.Finite
import QuadraticIterates.Characters.Criterion
import QuadraticIterates.Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import QuadraticIterates.Mathlib.NumberTheory.ArithmeticFunction.Moebius
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat
import QuadraticIterates.Patterns.Sign
import QuadraticIterates.Sequence.Signs
import QuadraticIterates.Sequence.Valuation

/-!
# Sign patterns and 2-independence through the Möbius quotients

For `a ∈ ℚ \ {0, -1}`, a sign pattern along `(c_n)` corresponds to its Möbius transform along the
Möbius quotients `(b_d)` (`QuadraticIterates.bSeq`); for `φ₀`, `φ₁` and `τ` these are `-1` at
`b_1` only, `-1` at the squarefree `d`, and `-1` at the squarefree `d > 1`. By duality, a pattern
is realized iff it multiplies to `1` along the square products of the `b_d`, and
`QuadraticIterates.isSquare_prod_bSeq_iff` decides which products are squares. So a pattern along
`(b_d)` is realized iff on `D = QuadraticIterates.bSeqSquareIndices a` it is
`u^{[b_d < 0]} v^{[d squarefree]}` for two signs `u`, `v` (with `v = 1` if the denominator of `a`
is a square), and `(c_n)` is 2-independent iff the vectors `([b_d < 0], [d squarefree, s ≠ □])`,
`d ∈ D`, are linearly independent over `ZMod 2`.

## Main statements

* `QuadraticIterates.hasCharPattern_neg_one_iff_forall_not_isSquare`,
  `QuadraticIterates.not_hasCharPattern_neg_one_iff_exists_finset`: `φ₀` exactly.
* `QuadraticIterates.hasCharPattern_neg_one_iff_of_forall_pos`: `φ₀` when `c_n > 0` for `n ≥ 2`.
* `QuadraticIterates.hasCharPattern_neg_one_iff_of_neg_one_lt_of_neg`: `φ₀` for `-1 < a < 0`.
* `QuadraticIterates.hasCharPattern_neg_one_iff_bSeq`,
  `QuadraticIterates.hasCharPattern_mulSingle_one_iff_bSeq`,
  `QuadraticIterates.hasCharPattern_neg_mulSingle_one_iff_bSeq`: `φ₀`, `φ₁`, `τ` along `(b_d)`.
* `QuadraticIterates.hasCharPattern_bSeq_iff`: the realizable patterns along `(b_d)`.
* `QuadraticIterates.twoIndependent_cSeq_iff`,
  `QuadraticIterates.twoIndependent_cSeq_iff_linearIndependent`,
  `QuadraticIterates.encard_bSeqSquareIndices_le_two`: 2-independence of `(c_n)`.
* `QuadraticIterates.hasCharPattern_neg_one_iff_of_neg_of_not_isSquare_den`: `φ₀` for `a < 0`
  when `|r|` is a square and the denominator is not.
-/

@[expose] public section

namespace QuadraticIterates

open Finset

variable {a : ℚ}

/-- `φ₀` along `(c_n)` is the pattern `-1` at `b_1` and `1` at all `b_d` with `d > 1`. -/
theorem hasCharPattern_neg_one_iff_bSeq (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    HasCharPattern (cSeq a) 1 (-1) ↔ HasCharPattern (bSeq a) 1 (Pi.mulSingle 1 (-1)) := by
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀ h₁ hn
  refine hasCharPattern_one_iff_of_prod_divisors (fun n _ ↦ bSeq_ne_zero hc n)
    (fun n hn ↦ prod_divisors_bSeq hc hn) (fun n _ ↦ ?_) fun n hn ↦ ?_
  · rcases eq_or_ne n 1 with rfl | hn <;> simp [*]
  · simp [prod_pi_mulSingle', Nat.one_le_iff_ne_zero.mp hn]

/-- **`φ₀` via the Möbius quotients**: `a` has `φ₀` iff no product `∏_{d ∈ T} b_d` with `1 ∈ T`
is a square. -/
theorem hasCharPattern_neg_one_iff_forall_not_isSquare (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    HasCharPattern (cSeq a) 1 (-1) ↔
      ∀ T : Finset ℕ, 1 ∈ T → 0 ∉ T → ¬IsSquare (∏ d ∈ T, bSeq a d) := by
  rw [hasCharPattern_neg_one_iff_bSeq h₀ h₁, hasCharPattern_one_iff_forall_isSquare
    (fun n _ ↦ bSeq_ne_zero (fun _ hn ↦ cSeq_ne_zero h₀ h₁ hn) n)
    fun n _ ↦ by rcases eq_or_ne n 1 with rfl | hn <;> simp [*]]
  refine forall_congr' fun T ↦ ?_
  rw [prod_pi_mulSingle']
  by_cases h1 : 1 ∈ T <;> simp [h1]

/-- **`φ₀` exactly**: `a` lacks `φ₀` iff some finite `T ∋ 1` lies in
`D = QuadraticIterates.bSeqSquareIndices a`, has `∏_{d ∈ T} b_d > 0`, and either the denominator
of `a` is a square or `T` contains an even number of squarefree `d`
(`QuadraticIterates.isSquare_prod_bSeq_iff`). -/
theorem not_hasCharPattern_neg_one_iff_exists_finset (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    ¬HasCharPattern (cSeq a) 1 (-1) ↔ ∃ T : Finset ℕ, 1 ∈ T ∧ 0 ∉ T ∧
      (∀ d ∈ T, d ∈ bSeqSquareIndices a) ∧ 0 < ∏ d ∈ T, bSeq a d ∧
        (IsSquare a.den ∨ Even #{d ∈ T | Squarefree d}) := by
  rw [hasCharPattern_neg_one_iff_forall_not_isSquare h₀ h₁]
  push Not
  exact exists_congr fun T ↦ and_congr_right fun _ ↦ and_congr_right fun hT ↦
    isSquare_prod_bSeq_iff h₀ h₁ hT

/-- A square product `∏_{d ∈ T} b_d` (`1 ∈ T`) with a squarefree `d ∈ T`, `d ≠ 1`, makes
`b_1 b_d` a square when `c_n > 0` for `n ≥ 2`: `{1, d}` inherits the conditions of
`QuadraticIterates.isSquare_prod_bSeq_iff`. -/
private lemma isSquare_bSeq_one_mul_bSeq_of_isSquare_prod (h : ∀ n ≥ 2, 0 < cSeq a n)
    {T : Finset ℕ} (h1T : 1 ∈ T) (hT0 : 0 ∉ T) (hT : IsSquare (∏ d ∈ T, bSeq a d)) {d : ℕ}
    (hdT : d ∈ T) (hd1 : d ≠ 1) (hd : Squarefree d) :
    IsSquare (bSeq a 1 * bSeq a d) := by
  have h₀ := ne_zero_of_cSeq_two_pos (h 2 le_rfl)
  have h₁ := ne_neg_one_of_cSeq_two_pos (h 2 le_rfl)
  obtain ⟨hD, -, -⟩ := (isSquare_prod_bSeq_iff h₀ h₁ hT0).mp hT
  rw [← prod_pair hd1.symm]
  refine (isSquare_prod_bSeq_iff h₀ h₁ (by simpa using (ne_of_mem_of_not_mem hdT hT0).symm)).mpr
    ⟨fun e he ↦ hD e (by rcases mem_insert.mp he with rfl | he <;> simp_all), ?_, .inr ?_⟩
  · simpa [prod_pair hd1.symm] using mul_bSeq_pos_of_squarefree h hd
  · simp [filter_insert, filter_singleton, hd, hd1.symm]

/-- A square product `∏_{d ∈ T} b_d` (`1 ∈ T`) without squarefree `d ∈ T \ {1}` makes `c_1` a
square when `c_n > 0` for `n ≥ 2`: then `b_1 > 0`, and the denominator of `a` is a square. -/
private lemma isSquare_cSeq_one_of_isSquare_prod (h : ∀ n ≥ 2, 0 < cSeq a n) {T : Finset ℕ}
    (h1T : 1 ∈ T) (hT0 : 0 ∉ T) (hT : IsSquare (∏ d ∈ T, bSeq a d))
    (hsf : ∀ d ∈ T, d ≠ 1 → ¬Squarefree d) :
    IsSquare (cSeq a 1) := by
  have h₀ := ne_zero_of_cSeq_two_pos (h 2 le_rfl)
  have h₁ := ne_neg_one_of_cSeq_two_pos (h 2 le_rfl)
  obtain ⟨hD, hpos, hpar⟩ := (isSquare_prod_bSeq_iff h₀ h₁ hT0).mp hT
  have hfilter : {d ∈ T | Squarefree d} = {1} := by
    ext d
    simp only [mem_filter, mem_singleton]
    exact ⟨fun ⟨hd, hsq⟩ ↦ by_contra fun h1 ↦ hsf d hd h1 hsq, fun h1 ↦ h1 ▸ ⟨h1T, squarefree_one⟩⟩
  rw [← mul_prod_erase _ _ h1T] at hpos
  have hb1 := (mul_pos_iff_of_pos_right (prod_pos fun d hd ↦ bSeq_pos_of_not_squarefree h
    (hsf d (mem_of_mem_erase hd) (ne_of_mem_erase hd)))).mp hpos
  have := (isSquare_prod_bSeq_iff h₀ h₁ (T := {1}) (by simp)).mpr
    ⟨by simpa using hD 1 h1T, by simpa using hb1, .inl (hpar.resolve_right (by simp [hfilter]))⟩
  simpa using this

/-- **`φ₀` when `c_n > 0` for `n ≥ 2`** (that is, `a > 0` or `a ≤ -2`): `a` has `φ₀` iff `c_1` is
not a square and, for no squarefree `d > 1`, the product `∏_{1 < e ∣ d} c_e` is a square. A square
product of the `b_d` with `1 ∈ T` reduces to `T = {1}` or `T = {1, d}`. -/
theorem hasCharPattern_neg_one_iff_of_forall_pos (h : ∀ n ≥ 2, 0 < cSeq a n) :
    HasCharPattern (cSeq a) 1 (-1) ↔ ¬IsSquare (cSeq a 1) ∧
      ∀ d > 1, Squarefree d → ¬IsSquare (∏ e ∈ d.divisors.erase 1, cSeq a e) := by
  have h₀ := ne_zero_of_cSeq_two_pos (h 2 le_rfl)
  have h₁ := ne_neg_one_of_cSeq_two_pos (h 2 le_rfl)
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀ h₁ hn
  rw [hasCharPattern_neg_one_iff_forall_not_isSquare h₀ h₁]
  refine ⟨fun H ↦ ⟨fun hsq ↦ H {1} (mem_singleton_self 1) (by simp) (by simpa using hsq),
    fun d hd hsf hsq ↦ H {1, d} (by simp) (by simp; lia) ?_⟩, fun ⟨H1, Hd⟩ T h1T hT0 hT ↦ ?_⟩
  · rw [prod_pair (by lia)]
    exact (isSquare_bSeq_one_mul_bSeq_iff hc hsf).mpr hsq
  by_cases hex : ∃ d ∈ T, d ≠ 1 ∧ Squarefree d
  · obtain ⟨d, hdT, hd1, hd⟩ := hex
    exact Hd d (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_mem_of_not_mem hdT hT0, hd1⟩) hd
      ((isSquare_bSeq_one_mul_bSeq_iff hc hd).mp
        (isSquare_bSeq_one_mul_bSeq_of_isSquare_prod h h1T hT0 hT hdT hd1 hd))
  · push Not at hex
    exact H1 (isSquare_cSeq_one_of_isSquare_prod h h1T hT0 hT hex)

/-- **`φ₀` for `-1 < a < 0`**: `a` has `φ₀` iff `-a` is not a square. A prime `q` with `v_q(a)`
odd gives `val_q` as a `φ₀` if `q` divides the numerator of `a`, and as a `φ₁` otherwise, which
the sign (a `τ`) completes to a `φ₀`. -/
theorem hasCharPattern_neg_one_iff_of_neg_one_lt_of_neg (h₁ : -1 < a) (h₀ : a < 0) :
    HasCharPattern (cSeq a) 1 (-1) ↔ ¬IsSquare (-a) := by
  refine ⟨fun h hsq ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.prod_eq_one_of_isSquare (S := {1}) (fun _ _ ↦ .inr rfl) (by simp)
      (by simpa using hsq)
  obtain ⟨q, hq, hodd⟩ : ∃ q : ℕ, q.Prime ∧ ¬Even (padicValRat q a) := by
    simpa [Rat.isSquare_iff_even_factorization, (neg_pos.mpr h₀).le, padicValRat.neg] using h
  have : Fact q.Prime := ⟨hq⟩
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀.ne h₁.ne' hn
  have hodd' : Odd (padicValRat q a).natAbs := Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hodd)
  rcases lt_or_gt_of_ne (fun h0 : padicValRat q a = 0 ↦ hodd (h0 ▸ Even.zero)) with hv | hv
  · refine hasCharPattern_neg_of_mulSingle_of_neg_mulSingle ⟨Rat.valChar q, fun n hn ↦ ?_⟩
      (hasCharPattern_neg_mulSingle_one_of_neg_one_lt h₁ h₀)
    rw [Rat.valChar_apply (hc n hn), padicValRat_cSeq_of_padicValRat_neg hv hn]
    rcases hn.eq_or_lt with rfl | hn
    · simpa using hodd'.neg_one_pow
    · rw [Pi.mulSingle_eq_of_ne (by lia), Even.neg_one_pow]
      exact Int.natAbs_even.mpr ((Nat.even_pow.mpr ⟨even_two, by lia⟩).natCast.mul_right _)
  · exact ⟨Rat.valChar q, fun n hn ↦ by
      rw [Rat.valChar_apply (hc n hn), padicValRat_cSeq_of_padicValRat_pos h₀.ne h₁.ne' hv hn,
        hodd'.neg_one_pow]; rfl⟩

/-- `∏_{d ∣ n} (-1)^{[d squarefree]}` is `-1` for `n = 1` and `1` for `n > 1`
(`ArithmeticFunction.even_card_filter_squarefree_divisors`). -/
private lemma prod_divisors_ite_squarefree {n : ℕ} (hn : 1 ≤ n) :
    ∏ d ∈ n.divisors, (if Squarefree d then (-1 : ℤ) else 1) = (Pi.mulSingle 1 (-1) : ℕ → ℤ) n := by
  simp only [prod_ite, prod_const_one, mul_one, prod_const]
  rcases eq_or_ne n 1 with rfl | h1
  · simp [filter_singleton]
  · rw [(ArithmeticFunction.even_card_filter_squarefree_divisors h1).neg_one_pow,
      Pi.mulSingle_eq_of_ne h1]

/-- `φ₁` along `(c_n)` is the pattern `-1` at the squarefree `d` and `1` at the others along
`(b_d)`. -/
theorem hasCharPattern_mulSingle_one_iff_bSeq (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    HasCharPattern (cSeq a) 1 (Pi.mulSingle 1 (-1)) ↔
      HasCharPattern (bSeq a) 1 fun d ↦ if Squarefree d then -1 else 1 := by
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀ h₁ hn
  exact hasCharPattern_one_iff_of_prod_divisors (fun n _ ↦ bSeq_ne_zero hc n)
    (fun n hn ↦ prod_divisors_bSeq hc hn) (fun n _ ↦ by split_ifs <;> simp)
    fun n hn ↦ prod_divisors_ite_squarefree hn

/-- `τ` along `(c_n)` is the pattern `1` at `b_1`, `-1` at the squarefree `d > 1` and `1` at the
other `d` along `(b_d)`. -/
theorem hasCharPattern_neg_mulSingle_one_iff_bSeq (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    HasCharPattern (cSeq a) 1 (-Pi.mulSingle 1 (-1)) ↔
      HasCharPattern (bSeq a) 1 (Pi.mulSingle 1 (-1) * fun d ↦ if Squarefree d then -1 else 1) := by
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀ h₁ hn
  refine hasCharPattern_one_iff_of_prod_divisors (fun n _ ↦ bSeq_ne_zero hc n)
    (fun n hn ↦ prod_divisors_bSeq hc hn) (fun n _ ↦ ?_) fun n hn ↦ ?_
  · have h1 : (Pi.mulSingle 1 (-1) : ℕ → ℤ) n = 1 ∨ (Pi.mulSingle 1 (-1) : ℕ → ℤ) n = -1 := by
      rcases eq_or_ne n 1 with rfl | hn <;> simp [*]
    simp only [Pi.mul_apply]
    rcases h1 with h1 | h1 <;> split_ifs <;> simp [h1]
  · simp only [Pi.mul_apply]
    rw [prod_mul_distrib, prod_pi_mulSingle', prod_divisors_ite_squarefree hn]
    simp [Nat.one_le_iff_ne_zero.mp hn]

/-- A product of nonzero rationals is positive iff an even number of its factors are negative. -/
private lemma prod_pos_iff_even_card {ι : Type*} {T : Finset ι} {f : ι → ℚ}
    (hf : ∀ d ∈ T, f d ≠ 0) :
    0 < ∏ d ∈ T, f d ↔ Even #{d ∈ T | f d < 0} := by
  have hP : ∏ d ∈ T, f d ≠ 0 := prod_ne_zero_iff.mpr hf
  have h : Rat.signChar (∏ d ∈ T, f d) = (-1) ^ #{d ∈ T | f d < 0} := by
    rw [map_prod, prod_congr rfl fun d hd ↦ show Rat.signChar (f d) = if f d < 0 then -1 else 1 by
      split_ifs with h
      exacts [Rat.signChar_apply_of_neg h,
        Rat.signChar_apply_of_pos (lt_of_le_of_ne (not_lt.mp h) (hf d hd).symm)]]
    simp only [prod_ite, prod_const, one_pow, mul_one]
  rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1), ← h]
  exact ⟨Rat.signChar_apply_of_pos, fun h1 ↦ (lt_or_gt_of_ne hP).resolve_left fun hneg ↦ by
    simp [Rat.signChar_apply_of_neg hneg] at h1⟩

/-- The value of a character at `b_d` for `d ∈ D`: `b_d ∼ sign(b_d) · s^{[d squarefree]}`
(`QuadraticIterates.mem_bSeqSquareIndices_iff_isSquare`). -/
private lemma apply_bSeq_of_mem (h₀ : a ≠ 0) (h₁ : a ≠ -1) (χ : MulChar ℚ ℤ) {d : ℕ}
    (hd : d ∈ bSeqSquareIndices a) :
    χ (bSeq a d) = (if bSeq a d < 0 then χ (-1) else 1) * if Squarefree d then χ a.den else 1 := by
  have hb := bSeq_ne_zero (fun _ ↦ cSeq_ne_zero h₀ h₁) d
  have hS : (if Squarefree d then (a.den : ℚ) else 1) ≠ 0 := by split_ifs <;> simp
  have hsq := (mem_bSeqSquareIndices_iff_isSquare h₀ h₁ hd.1).mp hd
  have hu := (mul_ne_zero (abs_ne_zero.mpr hb) hS).isUnit
  have h1 := (χ.apply_eq_one_or_eq_neg_one hu).resolve_right (χ.apply_ne_neg_one_of_isSquare hsq)
  have hχS : χ (if Squarefree d then (a.den : ℚ) else 1) = if Squarefree d then χ a.den else 1 := by
    split_ifs <;> simp
  rw [map_mul, hχS] at h1
  have habs : χ |bSeq a d| = if Squarefree d then χ a.den else 1 := by
    rcases χ.apply_eq_one_or_eq_neg_one hS.isUnit with h | h <;> rw [hχS] at h <;>
      rw [h] at h1 ⊢ <;> lia
  rcases lt_or_gt_of_ne hb with h | h
  · simp only [h, ite_true]
    conv_lhs => rw [← neg_neg (bSeq a d), ← abs_of_neg h, neg_eq_neg_one_mul, map_mul, habs]
  · simp only [not_lt.mpr h.le, ite_false, one_mul]
    conv_lhs => rw [← abs_of_pos h, habs]

/-- The values of a sign `u` raised to the size of a set with even size. -/
private lemma units_pow_of_even (u : ℤˣ) {k : ℕ} (hk : Even k) : (u : ℤ) ^ k = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [hk.neg_one_pow]

/-- The pattern `u^{[b_d < 0]} v^{[d squarefree]}` on `D` multiplies to `1` along every square
product of the `b_d` (`QuadraticIterates.isSquare_prod_bSeq_iff`). -/
private lemma prod_eq_one_of_isSquare_prod_bSeq (h₀ : a ≠ 0) (h₁ : a ≠ -1) {u v : ℤˣ}
    (hv : IsSquare a.den → v = 1) {β : ℕ → ℤ} (hβ : ∀ d ∈ bSeqSquareIndices a,
      β d = (if bSeq a d < 0 then (u : ℤ) else 1) * if Squarefree d then (v : ℤ) else 1)
    {T : Finset ℕ} (hT : 0 ∉ T) (hsq : IsSquare (∏ d ∈ T, bSeq a d)) :
    ∏ d ∈ T, β d = 1 := by
  obtain ⟨hD, hpos, hs⟩ := (isSquare_prod_bSeq_iff h₀ h₁ hT).mp hsq
  have hneg := (prod_pos_iff_even_card fun d _ ↦
    bSeq_ne_zero (fun _ hn ↦ cSeq_ne_zero h₀ h₁ hn) d).mp hpos
  rw [prod_congr rfl fun d hd ↦ hβ d (hD d hd), prod_mul_distrib, prod_ite, prod_ite]
  simp only [prod_const, one_pow, mul_one, units_pow_of_even u hneg, one_mul]
  rcases hs with hs | hs
  · simp [hv hs]
  · exact units_pow_of_even v hs

/-- **The realizable patterns along `(b_d)`**: for `a ∈ ℚ \ {0, -1}`, a sign pattern `β` is
realized along `(b_d)` iff on `D = QuadraticIterates.bSeqSquareIndices a` it is
`β d = u^{[b_d < 0]} v^{[d squarefree]}` for two signs `u`, `v`, with `v = 1` if the denominator
`s` of `a` is a square. Off `D` the values of `β` are free. For a character `χ` realizing `β`,
`u = χ(-1)` and `v = χ(s)`, as `b_d ∼ sign(b_d) · s^{[d squarefree]}` for `d ∈ D`. -/
theorem hasCharPattern_bSeq_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) {β : ℕ → ℤ}
    (hβ : ∀ d ≥ 1, β d = 1 ∨ β d = -1) :
    HasCharPattern (bSeq a) 1 β ↔ ∃ u v : ℤˣ, (IsSquare a.den → v = 1) ∧
      ∀ d ∈ bSeqSquareIndices a,
        β d = (if bSeq a d < 0 then (u : ℤ) else 1) * if Squarefree d then (v : ℤ) else 1 := by
  have hunit {x : ℚ} (hx : x ≠ 0) (χ : MulChar ℚ ℤ) : ∃ u : ℤˣ, (u : ℤ) = χ x :=
    (χ.apply_eq_one_or_eq_neg_one hx.isUnit).elim (fun h ↦ ⟨1, h.symm⟩) fun h ↦ ⟨-1, by simp [h]⟩
  refine ⟨fun ⟨χ, hχ⟩ ↦ ?_, fun ⟨u, v, hv, hβ'⟩ ↦ ?_⟩
  · obtain ⟨u, hu⟩ := hunit (neg_ne_zero.mpr one_ne_zero) χ
    obtain ⟨v, hv⟩ := hunit (Nat.cast_ne_zero.mpr a.den_nz) χ
    refine ⟨u, v, fun hs ↦ Units.ext ?_, fun d hd ↦ ?_⟩
    · exact hv.trans ((χ.apply_eq_one_or_eq_neg_one (Nat.cast_ne_zero.mpr a.den_nz).isUnit
        ).resolve_right (χ.apply_ne_neg_one_of_isSquare (hs.map (Nat.castRingHom ℚ))))
    · rw [← hχ d hd.1, apply_bSeq_of_mem h₀ h₁ χ hd, hu, hv]
  · exact (hasCharPattern_one_iff_forall_isSquare (fun n _ ↦ bSeq_ne_zero
      (fun _ hn ↦ cSeq_ne_zero h₀ h₁ hn) n) hβ).mpr fun T hT hsq ↦
      prod_eq_one_of_isSquare_prod_bSeq h₀ h₁ hv hβ' hT hsq

/-- A sequence `w 1, w 2, …` is 2-independent iff no product over a nonempty finite set of
positive indices is a square. -/
private lemma twoIndependent_succ_iff {M : Type*} [CommMonoid M] {w : ℕ → M} :
    TwoIndependent (fun n ↦ w (n + 1)) ↔
      ∀ T : Finset ℕ, T.Nonempty → 0 ∉ T → ¬IsSquare (∏ d ∈ T, w d) := by
  refine ⟨fun h T hT h0 hsq ↦ h (T.image (· - 1)) (hT.image _) ?_, fun h S hS ↦ ?_⟩
  · have hpos {d : ℕ} (hd : d ∈ T) : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h ↦ h0 (h ▸ hd)
    rwa [prod_image fun x hx y hy hxy ↦ by lia [hpos hx, hpos hy],
      prod_congr rfl fun d hd ↦ by rw [Nat.sub_add_cancel (hpos hd)]]
  · simpa [prod_map] using h (S.map (addRightEmbedding 1)) (hS.map) (by simp)

/-- **2-independence via the Möbius quotients**: `c_1, c_2, …` are 2-independent iff every nonempty
finite `T ⊆ D = QuadraticIterates.bSeqSquareIndices a` with `∏_{d ∈ T} b_d > 0` contains an odd
number of squarefree `d`, and the denominator of `a` is not a square (unless `D` contains no such
`T`). -/
theorem twoIndependent_cSeq_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    TwoIndependent (fun n ↦ cSeq a (n + 1)) ↔ ∀ T : Finset ℕ, T.Nonempty →
      (∀ d ∈ T, d ∈ bSeqSquareIndices a) → 0 < ∏ d ∈ T, bSeq a d →
        ¬IsSquare a.den ∧ Odd #{d ∈ T | Squarefree d} := by
  have hc (n : ℕ) (hn : 1 ≤ n) := cSeq_ne_zero h₀ h₁ hn
  rw [twoIndependent_iff_of_prod_divisors (fun n _ ↦ bSeq_ne_zero hc n)
    (fun n hn ↦ prod_divisors_bSeq hc hn), twoIndependent_succ_iff]
  refine ⟨fun h T hT hD hpos ↦ ?_, fun h T hT h0 hsq ↦ ?_⟩
  · have h0 : 0 ∉ T := fun h0 ↦ by simpa using (hD 0 h0).1
    have := h T hT h0
    rw [isSquare_prod_bSeq_iff h₀ h₁ h0, not_and, not_and, not_or, Nat.not_even_iff_odd] at this
    exact this hD hpos
  · obtain ⟨hD, hpos, hs⟩ := (isSquare_prod_bSeq_iff h₀ h₁ h0).mp hsq
    obtain ⟨h1, h2⟩ := h T hT hD hpos
    exact hs.elim h1 (Nat.not_even_iff_odd.mpr h2)

/-- The sum of the vectors `([b_d < 0], [d squarefree, s ≠ □])` over a finite subset of `D`
vanishes iff the corresponding product of the `b_d` is a square
(`QuadraticIterates.isSquare_prod_bSeq_iff`, conditions (2) and (3)). -/
private lemma sum_eq_zero_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) (s : Finset (bSeqSquareIndices a)) :
    ∑ d ∈ s, ((if bSeq a d < 0 then 1 else 0 : ZMod 2),
      (if Squarefree (d : ℕ) ∧ ¬IsSquare a.den then 1 else 0 : ZMod 2)) = 0 ↔
      0 < ∏ d ∈ s, bSeq a d ∧ (IsSquare a.den ∨ Even #{d ∈ s | Squarefree d.1}) := by
  rw [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero, sum_boole, sum_boole,
    ZMod.natCast_eq_zero_iff_even, ZMod.natCast_eq_zero_iff_even,
    ← prod_pos_iff_even_card (f := fun d : bSeqSquareIndices a ↦ bSeq a d)
      fun d _ ↦ bSeq_ne_zero (fun _ hn ↦ cSeq_ne_zero h₀ h₁ hn) d]
  by_cases hs : IsSquare a.den <;> simp [hs]

/-- **2-independence as linear independence in `𝔽₂²`**: `c_1, c_2, …` are 2-independent iff the
vectors `([b_d < 0], [d squarefree and s ≠ □])`, `d ∈ D = QuadraticIterates.bSeqSquareIndices a`,
are linearly independent over `ZMod 2`; in particular `D` has at most two elements
(`QuadraticIterates.encard_bSeqSquareIndices_le_two`). -/
theorem twoIndependent_cSeq_iff_linearIndependent (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    TwoIndependent (fun n ↦ cSeq a (n + 1)) ↔
      LinearIndependent (ZMod 2) fun d : bSeqSquareIndices a ↦
        ((if bSeq a d < 0 then 1 else 0 : ZMod 2),
          (if Squarefree (d : ℕ) ∧ ¬IsSquare a.den then 1 else 0 : ZMod 2)) := by
  classical
  rw [twoIndependent_cSeq_iff h₀ h₁, linearIndependent_zmod_two_iff]
  simp_rw [Ne, sum_eq_zero_iff h₀ h₁]
  refine ⟨fun h s hs ⟨hpos, hsq⟩ ↦ ?_, fun h T hT hD hpos ↦ ?_⟩
  · obtain ⟨h1, h2⟩ := h (s.map (.subtype _)) hs.map (fun d hd ↦ by
      obtain ⟨d, -, rfl⟩ := mem_map.mp hd; exact d.2) (by rwa [prod_map])
    rw [filter_map, card_map] at h2
    exact hsq.elim h1 (Nat.not_even_iff_odd.mpr h2)
  · have hsT := subtype_map_of_mem (p := (· ∈ bSeqSquareIndices a)) hD
    by_contra hcon
    rw [not_and_or, not_not, Nat.not_odd_iff_even] at hcon
    refine h (T.subtype _) (by rw [← map_nonempty, hsT]; exact hT) ⟨?_, ?_⟩
    · rwa [← hsT, prod_map] at hpos
    · rw [← hsT, filter_map, card_map] at hcon
      exact hcon

/-- If `c_1, c_2, …` are 2-independent, then `D = QuadraticIterates.bSeqSquareIndices a` has at
most two elements (`QuadraticIterates.twoIndependent_cSeq_iff_linearIndependent`). -/
theorem encard_bSeqSquareIndices_le_two (h₀ : a ≠ 0) (h₁ : a ≠ -1)
    (h : TwoIndependent (fun n ↦ cSeq a (n + 1))) :
    (bSeqSquareIndices a).encard ≤ 2 := by
  have hli := (twoIndependent_cSeq_iff_linearIndependent h₀ h₁).mp h
  have := hli.finite
  have := Fintype.ofFinite (bSeqSquareIndices a)
  have hcard := hli.fintype_card_le_finrank
  simp only [Module.finrank_prod, Module.finrank_self] at hcard
  rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, Set.encard_le_coe_iff_finite_ncard_le,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact ⟨Set.toFinite _, hcard⟩

/-- **`φ₀` in the open case**: for `a < 0`, `a ≠ -1`, with `1 ∈ D` (`|r|` a square) and
denominator `s` not a square, `a` has `φ₀` iff `D \ {1}` contains no squarefree `d`, or
`b_d < 0 ↔ d squarefree` for all `d ∈ D \ {1}` (`QuadraticIterates.hasCharPattern_bSeq_iff` with
`(u, v) = (1, -1)`, resp. `(-1, -1)`). -/
theorem hasCharPattern_neg_one_iff_of_neg_of_not_isSquare_den (ha : a < 0) (h₁ : a ≠ -1)
    (hr : 1 ∈ bSeqSquareIndices a) (hs : ¬IsSquare a.den) :
    HasCharPattern (cSeq a) 1 (-1) ↔ (∀ d ∈ bSeqSquareIndices a, d ≠ 1 → ¬Squarefree d) ∨
      ∀ d ∈ bSeqSquareIndices a, d ≠ 1 → (bSeq a d < 0 ↔ Squarefree d) := by
  have h₀ := ha.ne
  have hb1 : ¬bSeq a 1 < 0 := by rw [bSeq_one]; linarith
  rw [hasCharPattern_neg_one_iff_bSeq h₀ h₁, hasCharPattern_bSeq_iff h₀ h₁
    fun d _ ↦ by rcases eq_or_ne d 1 with rfl | hd <;> simp [*]]
  simp only [hs, false_imp_iff, true_and]
  refine ⟨fun ⟨u, v, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hv : (v : ℤ) = -1 := by simpa [not_lt.mpr ha.le] using (h 1 hr).symm
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact .inl fun d hd hd1 hsq ↦ by have := h d hd; split_ifs at this <;> simp_all
    · exact .inr fun d hd hd1 ↦ by have := h d hd; split_ifs at this <;> simp_all
  · rcases h with h | h
    · exact ⟨1, -1, fun d hd ↦ by rcases eq_or_ne d 1 with rfl | hd1 <;> simp [*]⟩
    · refine ⟨-1, -1, fun d hd ↦ ?_⟩
      rcases eq_or_ne d 1 with rfl | hd1
      · simp [ha.le]
      · have := h d hd hd1
        split_ifs <;> simp_all

end QuadraticIterates
