/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import QuadraticIterates.Mathlib.Data.ZMod

/-!
# Quadratic characters of `ℚ`

A multiplicative function `f` on `ℤ` that is a unit at every nonzero integer extends uniquely to
a multiplicative character `x ↦ f(num x) · f(den x)` of `ℚ` with values in `ℤ`
(`Rat.mulCharOfInt`). This gives the characters of `ℚ` used to detect non-squares.

## Main definitions

* `Rat.mulCharOfInt f`: the character `x ↦ f(num x) · f(den x)` of `ℚ`.
* `Rat.signChar`: the sign.
* `Rat.valChar p`: the parity `x ↦ (-1)^{v_p(x)}` of the `p`-adic valuation.
* `Rat.unitPartChar p ψ`: for a character `ψ` modulo a power `N` of the prime `p`, the value of
  `ψ` at the prime-to-`p` part `x / p^{v_p(x)}` of `x`. For an odd prime `p` and `ψ` the Legendre
  symbol (`quadraticChar (ZMod p)`), and for `p = 2` and `ψ = ZMod.χ₄` or `ψ = ZMod.χ₈`, these
  and `Rat.valChar p` generate the characters of `ℚ_p^×/ℚ_p^{×2}`.

## Main statements

* `Rat.unitPartChar_intCast`: `unitPartChar p ψ m = ψ m` for an integer `m` prime to `p`.
* `Rat.unitPartChar_natCast_self`: `unitPartChar p ψ p = 1`.
* `Rat.valChar_intCast`: `valChar p m = (-1)^{v_p(m)}` for a nonzero integer `m`.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Rat

/-- The extension `x ↦ f(num x) · f(den x)` of a multiplicative function `f` on `ℤ` is
multiplicative when `f` is a unit at every nonzero integer: `f(den x)² = 1`. -/
lemma map_num_mul_map_den_mul {f : ℤ →*₀ ℤ} (hf : ∀ m ≠ 0, IsUnit (f m)) (x y : ℚ) :
    f (x * y).num * f (x * y).den = f x.num * f x.den * (f y.num * f y.den) := by
  have h := congr(f $(Rat.mul_num_den' x y))
  simp only [map_mul] at h
  grobner [Int.isUnit_mul_self (hf _ (Int.natCast_ne_zero.mpr x.den_nz)),
    Int.isUnit_mul_self (hf _ (Int.natCast_ne_zero.mpr y.den_nz)),
    Int.isUnit_mul_self (hf _ (Int.natCast_ne_zero.mpr (x * y).den_nz))]

/-- The extension `x ↦ f(num x) · f(den x)` to `ℚ` of a multiplicative function `f` on `ℤ` that is
a unit at every nonzero integer; it is the only multiplicative character of `ℚ` extending `f`,
because `f(den x)⁻¹ = f(den x)`. If `f` is not a unit at some nonzero integer, the junk value is
the trivial character. -/
noncomputable def mulCharOfInt (f : ℤ →*₀ ℤ) : MulChar ℚ ℤ := by
  classical
  exact if hf : ∀ m ≠ 0, IsUnit (f m) then
    { toFun x := f x.num * f x.den
      map_one' := by simp
      map_mul' := map_num_mul_map_den_mul hf
      map_nonunit' x hx := by
        rw [isUnit_iff_ne_zero, not_not] at hx
        simp [hx] }
  else 1

variable {f : ℤ →*₀ ℤ}

lemma mulCharOfInt_apply (hf : ∀ m ≠ 0, IsUnit (f m)) (x : ℚ) :
    mulCharOfInt f x = f x.num * f x.den := by
  rw [mulCharOfInt, dite_eq_left hf]
  rfl

@[simp] lemma mulCharOfInt_intCast (hf : ∀ m ≠ 0, IsUnit (f m)) (m : ℤ) :
    mulCharOfInt f m = f m := by
  simp [mulCharOfInt_apply hf]

/-! ### The sign -/

/-- The sign of a rational number, as a multiplicative character. -/
noncomputable def signChar : MulChar ℚ ℤ :=
  mulCharOfInt
    { toFun := Int.sign
      map_zero' := Int.sign_zero
      map_one' := Int.sign_one
      map_mul' := Int.sign_mul }

lemma signChar_apply (x : ℚ) : signChar x = x.num.sign := by
  rw [signChar, mulCharOfInt_apply fun m hm ↦
    Int.isUnit_iff_natAbs_eq.mpr (Int.natAbs_sign_of_ne_zero hm)]
  simp [Int.sign_natCast_of_ne_zero x.den_nz]

lemma signChar_apply_of_pos {x : ℚ} (hx : 0 < x) : signChar x = 1 := by
  rw [signChar_apply, Int.sign_eq_one_of_pos (Rat.num_pos.mpr hx)]

lemma signChar_apply_of_neg {x : ℚ} (hx : x < 0) : signChar x = -1 := by
  rw [signChar_apply, Int.sign_eq_neg_one_of_neg (Rat.num_neg.mpr hx)]

/-! ### The parity of the `p`-adic valuation -/

section valChar

variable (p : ℕ) [Fact p.Prime]

/-- The parity character `x ↦ (-1)^{v_p(x)}` of the `p`-adic valuation. -/
noncomputable def valChar : MulChar ℚ ℤ :=
  mulCharOfInt
    { toFun m := if m = 0 then 0 else (-1) ^ padicValInt p m
      map_zero' := by simp
      map_one' := by simp
      map_mul' m n := by
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn, padicValInt.mul, pow_add] }

variable {p}

lemma valChar_intCast {m : ℤ} (hm : m ≠ 0) : valChar p m = (-1) ^ padicValInt p m := by
  rw [valChar, mulCharOfInt_intCast fun n hn ↦ by simp [hn, (isUnit_neg_one (α := ℤ)).pow]]
  simp [hm]

lemma valChar_intCast_of_not_dvd {m : ℤ} (hm : ¬(p : ℤ) ∣ m) : valChar p m = 1 := by
  rw [valChar_intCast fun h ↦ hm (by simp [h]), padicValInt.eq_zero_of_not_dvd hm, pow_zero]

lemma valChar_natCast_self : valChar p p = -1 := by
  rw [← Int.cast_natCast, valChar_intCast (mod_cast (Fact.out : p.Prime).ne_zero),
    padicValInt.self (Fact.out : p.Prime).one_lt, pow_one]

lemma valChar_neg_one : valChar p (-1) = 1 :=
  mod_cast valChar_intCast_of_not_dvd (p := p) (m := -1)
    (dvd_neg.not.mpr (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_one)

lemma valChar_intCast_pow_mul (k : ℕ) {m : ℤ} (hm : ¬(p : ℤ) ∣ m) :
    valChar p (((p : ℤ) ^ k * m : ℤ) : ℚ) = (-1) ^ k := by
  simp [valChar_natCast_self, valChar_intCast_of_not_dvd hm]

end valChar

/-! ### Characters of the prime-to-`p` part -/

section unitPartChar

variable (p : ℕ) {N : ℕ} (ψ : MulChar (ZMod N) ℤ)

/-- The character `x ↦ ψ(x_p)` of `ℚ` attached to a character `ψ` of `ZMod N`, `N` a power of the
prime `p`, where `x_p = x / p^{v_p(x)}` is the prime-to-`p` part of `x`, reduced modulo `N` as a
fraction with denominator prime to `p`. On a nonzero integer `m` it is `ψ(sign m · m')`, with
`m' = |m| / p^{v_p(m)}`. If `ψ` is not a unit at some such residue (so `N` is not a power of `p`),
it is the trivial character (`Rat.mulCharOfInt`). -/
noncomputable def unitPartChar : MulChar ℚ ℤ :=
  mulCharOfInt
    { toFun m := if m = 0 then 0 else ψ (m.sign * (ordCompl[p] m.natAbs : ℕ))
      map_zero' := by simp
      map_one' := by simp
      map_mul' m n := by
        rcases eq_or_ne m 0 with rfl | hm
        · simp
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        simp only [mul_eq_zero, hm, hn, or_self, ite_false, Int.sign_mul, Int.natAbs_mul,
          Nat.ordCompl_mul, Nat.cast_mul, Int.cast_mul, ← map_mul]
        ring_nf }

variable {p ψ} [Fact p.Prime] {k : ℕ}

private lemma isUnit_apply_sign_mul_ordCompl (hN : N = p ^ k) {m : ℤ} (hm : m ≠ 0) :
    IsUnit (ψ (m.sign * (ordCompl[p] m.natAbs : ℕ))) := by
  have hdvd : ¬(p : ℤ) ∣ m.sign * (ordCompl[p] m.natAbs : ℕ) := by
    rw [(Int.isUnit_iff_natAbs_eq.mpr (Int.natAbs_sign_of_ne_zero hm)).dvd_mul_left,
      Int.natCast_dvd_natCast]
    exact Nat.not_dvd_ordCompl Fact.out (Int.natAbs_ne_zero.mpr hm)
  simpa only [Int.cast_mul, Int.cast_natCast] using (ZMod.isUnit_intCast_of_not_dvd hN hdvd).map ψ

private lemma unitPartChar_intCast_eq (hN : N = p ^ k) (m : ℤ) :
    unitPartChar p ψ m = if m = 0 then 0 else ψ (m.sign * (ordCompl[p] m.natAbs : ℕ)) :=
  mulCharOfInt_intCast (fun n hn ↦ by simpa [hn] using isUnit_apply_sign_mul_ordCompl hN hn) m

lemma unitPartChar_intCast (hN : N = p ^ k) {m : ℤ} (hm : ¬(p : ℤ) ∣ m) :
    unitPartChar p ψ m = ψ m := by
  have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ dvd_zero _)
  rw [unitPartChar_intCast_eq hN, ite_eq_right hm0,
    Nat.factorization_eq_zero_of_not_dvd (Int.natCast_dvd.not.mp hm), pow_zero, Nat.div_one,
    ← Int.cast_natCast, ← Int.cast_mul, Int.sign_mul_natAbs]

lemma unitPartChar_natCast_self (hN : N = p ^ k) : unitPartChar p ψ p = 1 := by
  have hp : p.Prime := Fact.out
  rw [← Int.cast_natCast, unitPartChar_intCast_eq hN]
  simp [hp.ne_zero, hp.factorization_self, Nat.div_self hp.pos,
    Int.sign_natCast_of_ne_zero hp.ne_zero]

lemma unitPartChar_neg_one {N k : ℕ} (hN : N = p ^ k) (ψ : MulChar (ZMod N) ℤ) :
    unitPartChar p ψ (-1) = ψ (-1) :=
  mod_cast unitPartChar_intCast (ψ := ψ) hN (m := -1)
    (dvd_neg.not.mpr (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_one)

lemma unitPartChar_intCast_pow_mul {N j : ℕ} (hN : N = p ^ j) (ψ : MulChar (ZMod N) ℤ) (k : ℕ)
    {m : ℤ} (hm : ¬(p : ℤ) ∣ m) : unitPartChar p ψ (((p : ℤ) ^ k * m : ℤ) : ℚ) = ψ m := by
  simp [unitPartChar_natCast_self hN, unitPartChar_intCast hN hm]

end unitPartChar

end Rat
