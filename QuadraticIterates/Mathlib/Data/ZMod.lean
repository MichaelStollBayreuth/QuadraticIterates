/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs

/-!
# `ZMod` lemmas

Units and negatives modulo `m` from coprimality and divisibility data; residues of odd and even
integers modulo `8`; integer scalars on a `ZMod 2`-module.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

lemma ZMod.intCast_eq_neg_intCast_of_dvd_add {a b : ℤ} {m : ℕ} (h : (m : ℤ) ∣ a + b) :
    (b : ZMod m) = -(a : ZMod m) := by
  rw [← Int.cast_neg, intCast_eq_intCast_iff_dvd_sub, ← neg_add']
  exact h.neg_right

lemma ZMod.isUnit_intCast_of_isCoprime_of_dvd {a b : ℤ} {m : ℕ} (h : IsCoprime a b)
    (hm : (m : ℤ) ∣ b) : IsUnit (a : ZMod m) :=
  (coe_int_isUnit_iff_isCoprime a m).mpr (h.of_isCoprime_of_dvd_right hm).symm

lemma ZMod.isUnit_intCast_of_isCoprime_of_dvd_add {a b : ℤ} {m : ℕ}
    (hcop : IsCoprime (m : ℤ) a) (h : (m : ℤ) ∣ a + b) : IsUnit ((b : ZMod m)) := by
  have hu := (coe_int_isUnit_iff_isCoprime a m).mpr hcop
  simpa [intCast_eq_neg_intCast_of_dvd_add h] using hu.neg

/-! ### Residues modulo `8` -/

/-- The square of an odd integer is `1` in `ZMod 8`. -/
lemma ZMod.intCast_sq_eight_eq_one_of_odd {x : ℤ} (hx : Odd x) : (x : ZMod 8) ^ 2 = 1 := by
  rw [← Int.cast_pow, ← Int.cast_one, intCast_eq_intCast_iff_dvd_sub]
  exact_mod_cast dvd_sub_comm.mp (Int.eight_dvd_sq_sub_one_of_odd hx)

lemma ZMod.isUnit_intCast_eight_of_odd {x : ℤ} (hx : Odd x) : IsUnit (x : ZMod 8) :=
  .of_mul_eq_one _ (sq (x : ZMod 8) ▸ intCast_sq_eight_eq_one_of_odd hx)

/-- A power `≥ 3` of an even integer is `0` in `ZMod 8`. -/
lemma ZMod.intCast_pow_eight_eq_zero_of_even {x : ℤ} (hx : Even x) {m : ℕ} (hm : 3 ≤ m) :
    (x : ZMod 8) ^ m = 0 := by
  obtain ⟨t, rfl⟩ := hx.two_dvd
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  push_cast
  rw [mul_pow, show (2 : ZMod 8) ^ 3 = 0 by decide, zero_mul, zero_mul]

/-- For odd `x`, `x^(2^k - 1) = x` in `ZMod 8` (`k ≥ 1`): the exponent is odd and `x² = 1`. -/
lemma ZMod.intCast_pow_two_pow_sub_one_eight_of_odd {x : ℤ} (hx : Odd x) {k : ℕ} (hk : 1 ≤ k) :
    (x : ZMod 8) ^ (2 ^ k - 1) = x := by
  rw [Nat.two_pow_sub_one_eq hk, pow_succ, pow_mul, intCast_sq_eight_eq_one_of_odd hx, one_pow,
    one_mul]

/-! ### `ZMod 2`-modules -/

/-- In a `ZMod 2`-module an integer scalar acts through its absolute value. -/
theorem ZModModule.zsmul_eq_natAbs_nsmul {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (k : ℤ)
    (v : M) : k • v = k.natAbs • v := by
  rcases Int.natAbs_eq k with h | h <;> nth_rw 1 [h]
  · rw [natCast_zsmul]
  · rw [neg_zsmul, natCast_zsmul, ZModModule.neg_eq_self]
