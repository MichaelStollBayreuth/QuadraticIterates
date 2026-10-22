/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.Data.ZMod.Units
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs
import QuadraticIterates.Mathlib.RingTheory.Int.Basic

/-!
# `ZMod` lemmas

Residues modulo `8` of odd integers and of integers with a given residue modulo `4`; units modulo
a prime power; congruence modulo an integer `m` as equality in `ZMod |m|`; integer scalars on a
`ZMod 2`-module.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-! ### Residues modulo `8` -/

/-- The square of an odd integer is `1` in `ZMod 8`. -/
lemma ZMod.intCast_sq_eight_eq_one_of_odd {x : ℤ} (hx : Odd x) : (x : ZMod 8) ^ 2 = 1 := by
  rw [← Int.cast_pow, ← Int.cast_one, intCast_eq_intCast_iff_dvd_sub]
  exact_mod_cast dvd_sub_comm.mp (Int.eight_dvd_sq_sub_one_of_odd hx)

/-- An odd integer is its own inverse in `ZMod 8`. -/
lemma ZMod.intCast_mul_self_eight_eq_one_of_odd {x : ℤ} (hx : Odd x) : (x : ZMod 8) * x = 1 :=
  (sq (x : ZMod 8)).symm.trans (intCast_sq_eight_eq_one_of_odd hx)

/-- For odd `x`, `x^(2^k) = 1` in `ZMod 8` (`k ≥ 1`). -/
lemma ZMod.intCast_pow_two_pow_eight_of_odd {x : ℤ} (hx : Odd x) {k : ℕ} (hk : 1 ≤ k) :
    (x : ZMod 8) ^ 2 ^ k = 1 := by
  rw [← Nat.sub_add_cancel hk, pow_succ, pow_mul', intCast_sq_eight_eq_one_of_odd hx, one_pow]

/-- For odd `x`, `x^(2^k - 1) = x` in `ZMod 8` (`k ≥ 1`): the exponent is odd and `x² = 1`. -/
lemma ZMod.intCast_pow_two_pow_sub_one_eight_of_odd {x : ℤ} (hx : Odd x) {k : ℕ} (hk : 1 ≤ k) :
    (x : ZMod 8) ^ (2 ^ k - 1) = x := by
  rw [Nat.two_pow_sub_one_eq hk, pow_succ, pow_mul, intCast_sq_eight_eq_one_of_odd hx, one_pow,
    one_mul]

/-- An integer `≡ c (mod 4)` is `c` or `c + 4` in `ZMod 8`. -/
lemma ZMod.intCast_eight_eq_or_eq_of_emod_four {x c : ℤ} (h : x % 4 = c) :
    (x : ZMod 8) = c ∨ (x : ZMod 8) = c + 4 := by
  rcases (by lia : x % 8 = c % 8 ∨ x % 8 = (c + 4) % 8) with h8 | h8
  · exact .inl ((ZMod.intCast_eq_intCast_iff' x c 8).mpr h8)
  · exact .inr (mod_cast (ZMod.intCast_eq_intCast_iff' x (c + 4) 8).mpr h8)

/-! ### Units modulo a prime power, congruences modulo an integer -/

/-- Modulo a power `N` of a prime `p`, an integer prime to `p` is a unit. -/
lemma ZMod.isUnit_intCast_of_not_dvd {p N k : ℕ} [Fact p.Prime] (hN : N = p ^ k) {m : ℤ}
    (hm : ¬(p : ℤ) ∣ m) : IsUnit (m : ZMod N) := by
  refine (ZMod.coe_int_isUnit_iff_isCoprime m N).mpr ?_
  rw [hN, Nat.cast_pow]
  exact ((Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr hm).pow_left

/-- Modulo a power `N = p^k`, `k ≥ 1`, of a prime `p`, an integer divisible by `p` is not a
unit. -/
lemma ZMod.not_isUnit_intCast_of_dvd {p N k : ℕ} [Fact p.Prime] (hN : N = p ^ k) (hk : k ≠ 0)
    {m : ℤ} (hm : (p : ℤ) ∣ m) : ¬IsUnit (m : ZMod N) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  refine fun h ↦ Int.Prime.not_dvd_of_isCoprime Fact.out h hm ?_
  rw [hN, Nat.cast_pow]
  exact dvd_pow_self _ hk

/-- Congruence modulo an integer `m` is equality in `ZMod |m|`. -/
lemma ZMod.intCast_eq_intCast_iff_modEq {m a b : ℤ} : (a : ZMod m.natAbs) = b ↔ a ≡ b [ZMOD m] :=
  (ZMod.intCast_eq_intCast_iff a b m.natAbs).trans Int.modEq_natAbs

@[simp] lemma ZMod.intCast_self_natAbs (m : ℤ) : (m : ZMod m.natAbs) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd m m.natAbs).mpr (Int.natAbs_dvd.mpr dvd_rfl)

/-! ### `ZMod 2`-modules -/

/-- In a `ZMod 2`-module an integer scalar acts through its absolute value. -/
theorem ZModModule.zsmul_eq_natAbs_nsmul {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (k : ℤ)
    (v : M) : k • v = k.natAbs • v := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k <;> simp [ZModModule.neg_eq_self]
