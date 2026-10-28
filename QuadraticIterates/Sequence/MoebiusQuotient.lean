/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import QuadraticIterates.Galois.Iterates

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Defs
import QuadraticIterates.Mathlib.NumberTheory.ArithmeticFunction.Moebius
import QuadraticIterates.Mathlib.NumberTheory.Padics.PadicVal.Basic
import QuadraticIterates.Sequence.Signs
import QuadraticIterates.Sequence.Valuation

/-!
# The Möbius quotients of `(c_n)` and their square products

The Möbius quotients `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}` satisfy `c_n = ∏_{d ∣ n} b_d`. For
`a ∈ ℚ \ {0, -1}`, the rigid divisibility of `(c_n)`
(`QuadraticIterates.padicValRat_cSeq_trichotomy`) becomes: a prime `p` not dividing the
denominator of `a` occurs in at most one `b_d`, and at a prime of the denominator,
`v_p(b_d) ≡ μ(d) v_p(a) (mod 2)`. This decides exactly which products of the `b_d` are squares.

## Main definitions

* `QuadraticIterates.bSeq a n`: the Möbius quotient `b_n`.

## Main statements

* `QuadraticIterates.prod_divisors_bSeq`: `c_n = ∏_{d ∣ n} b_d`.
* `QuadraticIterates.isSquare_bSeq_mul_prod_of_squarefree`,
  `QuadraticIterates.isSquare_bSeq_one_mul_bSeq_iff`: for squarefree `d`, `b_d` has the square
  class of `∏_{e ∣ d} c_e`, and `b_1 b_d` that of `∏_{1 < e ∣ d} c_e`.
* `QuadraticIterates.bSeq_pos_of_not_squarefree`, `QuadraticIterates.mul_bSeq_pos_of_squarefree`:
  the signs of the `b_d` when `c_n > 0` for `n ≥ 2`.
* `QuadraticIterates.padicValRat_bSeq_eq_ite`,
  `QuadraticIterates.padicValRat_bSeq_modEq_of_padicValRat_neg`: the valuations of the `b_d`.
* `QuadraticIterates.isSquare_prod_bSeq_iff`: the square products of the `b_d`.
-/

@[expose] public section

namespace QuadraticIterates

open Finset
open scoped ArithmeticFunction.Moebius

section Field

variable {K : Type*} [Field K] {a : K}

/-- The **Möbius quotients** `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}` of the sequence `(c_n)` of `X² + a`,
so that `c_n = ∏_{d ∣ n} b_d` (`QuadraticIterates.prod_divisors_bSeq`). As polynomials in `a`
they are, up to sign, the Gleason polynomials; for `a ∈ ℚ`, the `b_d` with distinct indices have no
common prime away from the denominator of `a` (`QuadraticIterates.padicValRat_bSeq_eq_ite`). -/
noncomputable def bSeq (a : K) (n : ℕ) : K :=
  ∏ x ∈ n.divisorsAntidiagonal, cSeq a x.2 ^ μ x.1

theorem bSeq_ne_zero (hc : ∀ n ≥ 1, cSeq a n ≠ 0) (n : ℕ) : bSeq a n ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hx ↦ zpow_ne_zero _ <|
    hc _ (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))

theorem prod_divisors_bSeq (hc : ∀ n ≥ 1, cSeq a n ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∏ d ∈ n.divisors, bSeq a d = cSeq a n :=
  (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n _ ↦ bSeq_ne_zero hc n)
    hc).mpr (fun _ _ ↦ rfl) n hn

@[simp] theorem bSeq_one : bSeq a 1 = -a := by simp [bSeq]

/-- For squarefree `d`, `b_d` and `∏_{e ∣ d} c_e` have the same square class: all exponents
`μ(d/e)` are `±1`. -/
theorem isSquare_bSeq_mul_prod_of_squarefree {d : ℕ} (hd : Squarefree d) :
    IsSquare (bSeq a d * ∏ e ∈ d.divisors, cSeq a e) := by
  rw [bSeq, ← Nat.prod_divisorsAntidiagonal' fun _ e ↦ cSeq a e, ← prod_mul_distrib]
  refine isSquare_prod _ fun x hx ↦ ?_
  rw [ArithmeticFunction.moebius_apply_of_squarefree
    (hd.squarefree_of_dvd (Nat.fst_mem_divisors_of_mem_antidiagonal hx |> Nat.dvd_of_mem_divisors))]
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors x.1) with h | h <;> rw [h]
  · exact ⟨_, by rw [zpow_one]⟩
  · rcases eq_or_ne (cSeq a x.2) 0 with h0 | h0 <;> simp [h0]

/-- In a field, two nonzero elements whose product is a square are both squares or both not. -/
private lemma isSquare_iff_of_isSquare_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : IsSquare (x * y)) :
    IsSquare x ↔ IsSquare y := by
  obtain ⟨z, hz⟩ := h
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨z / w, ?_⟩, fun ⟨w, hw⟩ ↦ ⟨z / w, ?_⟩⟩
  · rw [div_mul_div_comm, ← hz, ← hw, mul_div_cancel_left₀ y hx]
  · rw [div_mul_div_comm, ← hz, ← hw, mul_div_cancel_right₀ x hy]

/-- For squarefree `d`, `b_1 b_d` and `∏_{1 < e ∣ d} c_e` have the same square class. -/
theorem isSquare_bSeq_one_mul_bSeq_iff (hc : ∀ n ≥ 1, cSeq a n ≠ 0) {d : ℕ} (hd : Squarefree d) :
    IsSquare (bSeq a 1 * bSeq a d) ↔ IsSquare (∏ e ∈ d.divisors.erase 1, cSeq a e) := by
  have hX : ∏ e ∈ d.divisors.erase 1, cSeq a e ≠ 0 := prod_ne_zero_iff.mpr fun e he ↦
    hc e (Nat.pos_of_mem_divisors (mem_of_mem_erase he))
  have h := isSquare_bSeq_mul_prod_of_squarefree (a := a) hd
  rw [← mul_prod_erase _ _ (Nat.one_mem_divisors.mpr hd.ne_zero), cSeq_one, ← bSeq_one,
    ← mul_assoc, mul_comm (bSeq a d)] at h
  exact isSquare_iff_of_isSquare_mul (mul_ne_zero (bSeq_ne_zero hc 1) (bSeq_ne_zero hc d)) hX h

end Field

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a : K}

/-- If `c_n > 0` for all `n ≥ 2`, then `b_d > 0` for every `d` that is not squarefree: the only
factor of `b_d` that can be negative, `c_1^{μ(d)}`, is `1`. -/
theorem bSeq_pos_of_not_squarefree (h : ∀ n ≥ 2, 0 < cSeq a n) {d : ℕ} (hd : ¬Squarefree d) :
    0 < bSeq a d := by
  refine prod_pos fun x hx ↦ ?_
  have hx2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  rcases eq_or_ne x.2 1 with h1 | h1
  · have hx1 : x.1 = d := by simpa [h1] using (Nat.mem_divisorsAntidiagonal.mp hx).1
    simp [h1, hx1, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
  · exact zpow_pos (h _ (by lia)) _

/-- If `c_n > 0` for all `n ≥ 2`, then `b_d` has the sign of `c_1` for squarefree `d`
(`QuadraticIterates.isSquare_bSeq_mul_prod_of_squarefree`). -/
theorem mul_bSeq_pos_of_squarefree (h : ∀ n ≥ 2, 0 < cSeq a n) {d : ℕ} (hd : Squarefree d) :
    0 < cSeq a 1 * bSeq a d := by
  have ha := ne_zero_of_cSeq_two_pos (h 2 le_rfl)
  have h₁ : cSeq a 1 ≠ 0 := by rwa [cSeq_one, neg_ne_zero]
  have hc (n : ℕ) (hn : 1 ≤ n) : cSeq a n ≠ 0 := hn.eq_or_lt.elim (· ▸ h₁) fun hn ↦ (h n hn).ne'
  have hQ : 0 < ∏ e ∈ d.divisors.erase 1, cSeq a e := prod_pos fun e he ↦ h e <| by
    lia [Nat.pos_of_mem_divisors (mem_of_mem_erase he), ne_of_mem_erase he]
  obtain ⟨z, hz⟩ := isSquare_bSeq_mul_prod_of_squarefree (a := a) hd
  rw [← mul_prod_erase _ _ (Nat.one_mem_divisors.mpr hd.ne_zero), mul_left_comm, ← mul_assoc]
    at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [bSeq_ne_zero hc d, ha, hQ.ne'] at hz
  exact (mul_pos_iff_of_pos_right hQ).mp (hz ▸ mul_self_pos.mpr hz0)

end LinearOrderedField

section Rat

variable {p : ℕ} [Fact p.Prime] {a : ℚ}

theorem padicValRat_bSeq (h₀ : a ≠ 0) (h₁ : a ≠ -1) (n : ℕ) :
    padicValRat p (bSeq a n) =
      ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * padicValRat p (cSeq a x.2) := by
  rw [bSeq, padicValRat.prod fun x hx ↦ zpow_ne_zero _ <| cSeq_ne_zero h₀ h₁ <|
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)]
  simp only [padicValRat.zpow]

theorem padicValRat_bSeq_eq_zero (h₀ : a ≠ 0) (h₁ : a ≠ -1)
    (h : ∀ n ≥ 1, padicValRat p (cSeq a n) = 0) (d : ℕ) :
    padicValRat p (bSeq a d) = 0 := by
  rw [padicValRat_bSeq h₀ h₁]
  exact sum_eq_zero fun x hx ↦ by
    rw [h _ (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)), mul_zero]

/-- **Rigid divisibility for `(b_n)`**: if `v_p(c_n) = e` for the multiples `n` of `m` and
`v_p(c_n) = 0` otherwise, then `p` occurs only in `b_m`, with `v_p(b_m) = e`. -/
theorem padicValRat_bSeq_eq_ite (h₀ : a ≠ 0) (h₁ : a ≠ -1) {m : ℕ} {e : ℤ}
    (h : ∀ n ≥ 1, padicValRat p (cSeq a n) = if m ∣ n then e else 0) {d : ℕ} (hd : 1 ≤ d) :
    padicValRat p (bSeq a d) = if d = m then e else 0 := by
  rw [padicValRat_bSeq h₀ h₁, sum_congr rfl fun x hx ↦ by
    rw [h _ (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))]]
  simpa only [Int.cast_id] using (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d ↦ if d = m then e else 0) (g := fun n ↦ if m ∣ n then e else 0)).mp
    (fun n hn ↦ by simp [sum_ite_eq', Nat.mem_divisors, hn.ne']) d hd

/-- At a prime of the denominator of `a`, `v_p(b_d) ≡ μ(d) v_p(a) (mod 2)`: from
`v_p(c_n) = 2^{n-1} v_p(a)`, only the term of `c_1` in `b_d = ∏_{e ∣ d} c_e^{μ(d/e)}` has odd
valuation. -/
theorem padicValRat_bSeq_modEq_of_padicValRat_neg (h₀ : a ≠ 0) (h₁ : a ≠ -1)
    (ha : padicValRat p a < 0) {d : ℕ} (hd : 1 ≤ d) :
    padicValRat p (bSeq a d) ≡ μ d * padicValRat p a [ZMOD 2] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).mp ?_
  rw [padicValRat_bSeq h₀ h₁, sum_congr rfl fun x hx ↦ by
    rw [padicValRat_cSeq_of_padicValRat_neg ha
      (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))]]
  push_cast
  rw [sum_eq_single (d, 1) (fun x hx hne ↦ ?_) (by simp [Nat.mem_divisorsAntidiagonal]; lia)]
  · simp
  · have hx2 : x.2 ≠ 1 := fun h ↦ hne <| Prod.ext (by
      simpa [h] using (Nat.mem_divisorsAntidiagonal.mp hx).1) h
    have hx0 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by lia), zero_mul, mul_zero]

/-- At a prime of the denominator of `a`, `Σ_{d ∈ T} v_p(b_d) ≡ v_p(a) · #{d ∈ T squarefree}`
modulo `2`. -/
private lemma even_sum_padicValRat_bSeq_iff_of_padicValRat_neg (h₀ : a ≠ 0) (h₁ : a ≠ -1)
    {T : Finset ℕ} (hT : 0 ∉ T) (ha : padicValRat p a < 0) :
    Even (∑ d ∈ T, padicValRat p (bSeq a d)) ↔
      Even (padicValRat p a) ∨ Even #{d ∈ T | Squarefree d} := by
  have hb {d : ℕ} (hd : d ∈ T) : ((padicValRat p (bSeq a d) : ℤ) : ZMod 2) =
      (if Squarefree d then 1 else 0) * padicValRat p a := by
    rw [(ZMod.intCast_eq_intCast_iff _ _ 2).mpr (padicValRat_bSeq_modEq_of_padicValRat_neg h₀ h₁
      ha (Nat.one_le_iff_ne_zero.mpr fun h ↦ hT (h ▸ hd))), Int.cast_mul,
      ArithmeticFunction.intCast_moebius_zmod_two]
  rw [← ZMod.intCast_eq_zero_iff_even, Int.cast_sum, sum_congr rfl fun d hd ↦ hb hd, ← sum_mul,
    sum_boole, mul_eq_zero, ZMod.natCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even, or_comm]

/-- The parity of `v_p(∏_{d ∈ T} b_d)` at one prime `p`: away from the denominator of `a`, each
`v_p(b_d)` must be even (`p` occurs in at most one `b_d`); at a prime of the denominator, the
condition is on the number of squarefree `d ∈ T`. -/
private lemma even_padicValRat_prod_bSeq_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) {T : Finset ℕ}
    (hT : 0 ∉ T) :
    Even (padicValRat p (∏ d ∈ T, bSeq a d)) ↔
      (0 ≤ padicValRat p a → ∀ d ∈ T, Even (padicValRat p (bSeq a d))) ∧
        (padicValRat p a < 0 → Even (padicValRat p a) ∨ Even #{d ∈ T | Squarefree d}) := by
  have hpos {d : ℕ} (hd : d ∈ T) : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h ↦ hT (h ▸ hd)
  have ha : padicValRat p a = padicValRat p (cSeq a 1) := by rw [cSeq_one, padicValRat.neg]
  rw [padicValRat.prod fun d _ ↦ bSeq_ne_zero (fun _ ↦ cSeq_ne_zero h₀ h₁) d]
  rcases padicValRat_cSeq_trichotomy (p := p) h₀ h₁ with h | ⟨m, -, e, he, h⟩ | ⟨e, he, h⟩
  · simp [padicValRat_bSeq_eq_zero h₀ h₁ h, ha.trans (h 1 le_rfl)]
  · have hb {d : ℕ} (hd : d ∈ T) := padicValRat_bSeq_eq_ite h₀ h₁ h (hpos hd)
    rw [sum_congr rfl fun d hd ↦ hb hd, sum_ite_eq', ha, h 1 le_rfl]
    have : 0 ≤ if m ∣ 1 then e else 0 := by split_ifs <;> lia
    simp only [this, not_lt.mpr this, true_imp_iff, false_imp_iff, and_true]
    split_ifs with hm
    · exact ⟨fun h d hd ↦ by rw [hb hd]; split_ifs <;> simp [h],
        fun h ↦ by simpa [hb hm] using h m hm⟩
    · exact ⟨fun _ d hd ↦ by simp [hb hd, ne_of_mem_of_not_mem hd hm], fun _ ↦ by simp⟩
  · have ha' : padicValRat p a < 0 := by rw [ha, h 1 le_rfl]; simpa using he
    simpa [ha'.not_ge, ha'] using even_sum_padicValRat_bSeq_iff_of_padicValRat_neg h₀ h₁ hT ha'

private lemma isSquare_den_iff :
    IsSquare a.den ↔ ∀ p : ℕ, p.Prime → padicValRat p a < 0 → Even (padicValRat p a) := by
  rw [Nat.isSquare_iff_even_factorization]
  refine forall₂_congr fun p hp ↦ ?_
  rw [Nat.factorization_def _ hp, padicValRat_def]
  rcases Rat.num_or_den_zero_padicVal a hp with h | h <;> simp only [h]
  · rcases Nat.eq_zero_or_pos (padicValNat p a.den) with h0 | h0 <;> simp [h0]
  · simp

/-- `v_p(s) = max(0, -v_p(a))` for the denominator `s` of `a`. -/
private lemma padicValRat_den :
    padicValRat p a.den = if padicValRat p a < 0 then -padicValRat p a else 0 := by
  rw [padicValRat.of_nat, padicValRat_def]
  rcases Rat.num_or_den_zero_padicVal a (Fact.out : p.Prime) with h | h <;> simp only [h]
  · rcases Nat.eq_zero_or_pos (padicValNat p a.den) with h0 | h0 <;> simp [h0]
  · simp

/-- The set `D` of the indices `d ≥ 1` at which the Möbius quotient `b_d` has even valuation at
every prime not dividing the denominator `s` of `a`. For `a = r/s` in lowest terms, `d ∈ D` iff
`|B_d(r, s)|` is a square, where `B_d` is the homogenization of `b_d`; equivalently, iff
`|b_d| · s^{[d squarefree]}` is a square
(`QuadraticIterates.mem_bSeqSquareIndices_iff_isSquare`). -/
def bSeqSquareIndices (a : ℚ) : Set ℕ :=
  {d | 1 ≤ d ∧ ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a → Even (padicValRat p (bSeq a d))}

theorem mem_bSeqSquareIndices {d : ℕ} :
    d ∈ bSeqSquareIndices a ↔
      1 ≤ d ∧ ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a → Even (padicValRat p (bSeq a d)) :=
  Iff.rfl

/-- The parity of `v_p(|b_d| · s^{[d squarefree]})` at one prime `p`: it is that of `v_p(b_d)`
if `p ∤ s`, and always even if `p ∣ s`. -/
private lemma even_padicValRat_abs_bSeq_mul_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) {d : ℕ} (hd : 1 ≤ d) :
    Even (padicValRat p (|bSeq a d| * if Squarefree d then (a.den : ℚ) else 1)) ↔
      (0 ≤ padicValRat p a → Even (padicValRat p (bSeq a d))) := by
  have hb := bSeq_ne_zero (fun _ ↦ cSeq_ne_zero h₀ h₁) d
  have hS : (if Squarefree d then (a.den : ℚ) else 1) ≠ 0 := by split_ifs <;> simp
  have habs : padicValRat p |bSeq a d| = padicValRat p (bSeq a d) := by
    rcases abs_choice (bSeq a d) with h | h <;> rw [h]; exact padicValRat.neg _
  have hden := padicValRat_den (p := p) (a := a)
  rw [padicValRat.mul (abs_ne_zero.mpr hb) hS, habs]
  rcases le_or_gt 0 (padicValRat p a) with hv | hv
  · have hS0 : padicValRat p (if Squarefree d then (a.den : ℚ) else 1) = 0 := by
      split_ifs <;> simp [hden, not_lt.mpr hv]
    simp [hS0, hv]
  · have hS1 : padicValRat p (if Squarefree d then (a.den : ℚ) else 1) =
        if Squarefree d then -padicValRat p a else 0 := by
      split_ifs <;> simp [hden, hv]
    simp only [not_le.mpr hv, false_imp_iff, iff_true, ← ZMod.intCast_eq_zero_iff_even, hS1]
    rw [Int.cast_add, (ZMod.intCast_eq_intCast_iff _ _ 2).mpr
      (padicValRat_bSeq_modEq_of_padicValRat_neg h₀ h₁ hv hd), Int.cast_mul,
      ArithmeticFunction.intCast_moebius_zmod_two]
    split_ifs <;> simp [CharTwo.add_self_eq_zero]

/-- An index `d ≥ 1` lies in `QuadraticIterates.bSeqSquareIndices a` iff
`|b_d| · s^{[d squarefree]}` is a square, `s` the denominator of `a`: at a prime of `s`, the
valuation of `|b_d| · s` is even for squarefree `d` and that of `b_d` is even otherwise
(`QuadraticIterates.padicValRat_bSeq_modEq_of_padicValRat_neg`). -/
theorem mem_bSeqSquareIndices_iff_isSquare (h₀ : a ≠ 0) (h₁ : a ≠ -1) {d : ℕ} (hd : 1 ≤ d) :
    d ∈ bSeqSquareIndices a ↔ IsSquare (|bSeq a d| * if Squarefree d then (a.den : ℚ) else 1) := by
  rw [mem_bSeqSquareIndices, Rat.isSquare_iff_even_factorization, and_iff_right hd,
    and_iff_right (by positivity)]
  exact forall₂_congr fun p hp ↦
    have : Fact p.Prime := ⟨hp⟩
    (even_padicValRat_abs_bSeq_mul_iff h₀ h₁ hd).symm

/-- **Square products of the `b_d`** for `a ∈ ℚ \ {0, -1}`: a product `∏_{d ∈ T} b_d` is a
square iff `T ⊆ D = QuadraticIterates.bSeqSquareIndices a` (each `b_d` has even valuation at all
primes not dividing the denominator `s` of `a`), the product is positive, and `s` is a square or
`T` contains an even number of squarefree `d`. -/
theorem isSquare_prod_bSeq_iff (h₀ : a ≠ 0) (h₁ : a ≠ -1) {T : Finset ℕ} (hT : 0 ∉ T) :
    IsSquare (∏ d ∈ T, bSeq a d) ↔ (∀ d ∈ T, d ∈ bSeqSquareIndices a) ∧
      0 < ∏ d ∈ T, bSeq a d ∧ (IsSquare a.den ∨ Even #{d ∈ T | Squarefree d}) := by
  have hP : 0 ≠ ∏ d ∈ T, bSeq a d :=
    (prod_ne_zero_iff.mpr fun d _ ↦ bSeq_ne_zero (fun _ ↦ cSeq_ne_zero h₀ h₁) d).symm
  have key (p : ℕ) (hp : p.Prime) :=
    have : Fact p.Prime := ⟨hp⟩
    even_padicValRat_prod_bSeq_iff (p := p) h₀ h₁ hT
  rw [Rat.isSquare_iff_even_factorization, hP.le_iff_lt, isSquare_den_iff]
  refine ⟨fun ⟨hpos, h⟩ ↦ ⟨fun d hd ↦ ⟨Nat.one_le_iff_ne_zero.mpr fun h ↦ hT (h ▸ hd),
    fun p hp hv ↦ ((key p hp).mp (h p hp)).1 hv d hd⟩, hpos,
    or_iff_not_imp_right.mpr fun hT' p hp hv ↦ (((key p hp).mp (h p hp)).2 hv).resolve_right hT'⟩,
    fun ⟨hD, hpos, hs⟩ ↦ ⟨hpos, fun p hp ↦ (key p hp).mpr
      ⟨fun hv d hd ↦ (hD d hd).2 p hp hv, fun hv ↦ hs.imp_left fun h ↦ h p hp hv⟩⟩⟩

end Rat

end QuadraticIterates
