/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat
public import QuadraticIterates.Sequence.WSeq

import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Sequence.SquareClasses

/-!
# Characters at the primes of `r` and of `s`

For `a = r/s` with `r, s` coprime, the values along `(c_n)` of the characters at a prime `p`
dividing `r` or `s`: the valuation parity `Rat.valChar p` and the characters
`Rat.unitPartChar p ψ` for `ψ` modulo a power of `p`. At `p ∣ r` they are constant from `n = 2`
on (with a twist by `ψ(-1)` at `n = 1`); at `p ∣ s` they are trivial from `n = 2` on (from `n = 3`
on for `p = 2` and `ψ` modulo `8`, `4` or `2`).

## Main statements

* `QuadraticIterates.valChar_cSeq_of_dvd_left`, `QuadraticIterates.unitPartChar_cSeq_of_dvd_left`:
  `p ∣ r`.
* `QuadraticIterates.valChar_cSeq_of_dvd_right`, `QuadraticIterates.unitPartChar_cSeq_of_dvd_right`,
  `QuadraticIterates.unitPartChar_two_cSeq_of_even`: `p ∣ s`.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

section Primes

variable {r s : ℤ} {p : ℕ} [Fact p.Prime]

private lemma not_dvd_of_isCoprime {x y : ℤ} (h : IsCoprime x y) (hy : (p : ℤ) ∣ y) :
    ¬(p : ℤ) ∣ x :=
  fun hx ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (h.isUnit_of_dvd' hx hy)

private lemma odd_two_pow_sub_one {m : ℕ} (hm : m ≠ 0) : Odd (2 ^ m - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hm⟩) odd_one

/-- At a prime `p ∣ r`, `c_n` has the `p`-adic valuation of `r` modulo `2`, for all `n ≥ 1`. -/
theorem valChar_cSeq_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) (hp : (p : ℤ) ∣ r) {n : ℕ}
    (hn : 1 ≤ n) : valChar p (cSeq ((r : ℚ) / s) n) = valChar p r := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [mulChar_cSeq_one_eq_mul _ hs, valChar_neg_one,
      valChar_intCast_of_not_dvd (not_dvd_of_isCoprime hrs.symm hp), one_mul, mul_one]
  · rw [mulChar_cSeq_of_two_le _ hs hn, map_mul,
      valChar_intCast_of_not_dvd (not_dvd_of_isCoprime (isCoprime_wSeq_left hrs (by lia)) hp),
      mul_one]

/-- At a power `N = p^k` (`k ≥ 1`) dividing `r`, `χ_ψ(c_n) = ψ(s) χ_ψ(r)` for `n ≥ 2`: `c_n` has
the square class of `r w_n`, and `w_n ≡ s^{2^{n-1} - 1} (mod r)` with an odd exponent. -/
theorem unitPartChar_cSeq_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hNr : (N : ℤ) ∣ r) (ψ : MulChar (ZMod N) ℤ) {n : ℕ}
    (hn : 2 ≤ n) : unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = ψ s * unitPartChar p ψ r := by
  have hpr : (p : ℤ) ∣ r := (dvd_pow_self (p : ℤ) hk).trans (mod_cast hN ▸ hNr)
  have hps := not_dvd_of_isCoprime hrs.symm hpr
  have hw : (wSeq r s n : ZMod N) = (s : ZMod N) ^ (2 ^ (n - 1) - 1) := by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr ((wSeq_modEq_left r s hn).of_dvd hNr)
  rw [mulChar_cSeq_of_two_le _ hs hn, map_mul, unitPartChar_intCast (m := wSeq r s n) hN
    (not_dvd_of_isCoprime (isCoprime_wSeq_left hrs (by lia)) hpr), hw, map_pow, mul_comm]
  rcases ψ.apply_eq_one_or_eq_neg_one (ZMod.isUnit_intCast_of_not_dvd hN hps) with h | h <;>
    simp [h, (odd_two_pow_sub_one (by lia : n - 1 ≠ 0)).neg_one_pow]

/-- At a prime `p ∣ s`, `v_p(c_n)` is even for `n ≥ 2`: `c_n` has the square class of `r w_n`,
which is prime to `s`. -/
theorem valChar_cSeq_of_dvd_right (hrs : IsCoprime r s) (hs : s ≠ 0) (hp : (p : ℤ) ∣ s) {n : ℕ}
    (hn : 2 ≤ n) : valChar p (cSeq ((r : ℚ) / s) n) = 1 := by
  rw [mulChar_cSeq_of_two_le _ hs hn, ← Int.cast_mul, valChar_intCast_of_not_dvd
    (not_dvd_of_isCoprime (hrs.mul_left (isCoprime_wSeq_right hrs (by lia))) hp)]

/-- At a power `N = p^k` (`k ≥ 1`) dividing `s`, `χ_ψ(c_n) = 1` for `n ≥ 2`: `c_n` has the
square class of `r w_n`, and `r w_n ≡ r^{2^{n-1}} (mod s)` is a square of a unit. -/
theorem unitPartChar_cSeq_of_dvd_right (hrs : IsCoprime r s) (hs : s ≠ 0) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hNs : (N : ℤ) ∣ s) (ψ : MulChar (ZMod N) ℤ) {n : ℕ}
    (hn : 2 ≤ n) : unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = 1 := by
  have hps : (p : ℤ) ∣ s := (dvd_pow_self (p : ℤ) hk).trans (mod_cast hN ▸ hNs)
  have hpr := not_dvd_of_isCoprime hrs hps
  have hw : (wSeq r s n : ZMod N) = (r : ZMod N) ^ (2 ^ (n - 1) - 1) := by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr ((wSeq_modEq_right r s hn).of_dvd hNs)
  have he : 2 ^ (n - 1) - 1 + 1 = 2 ^ (n - 2) * 2 := by
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_succ]
    congr 1
    lia
  rw [mulChar_cSeq_of_two_le _ hs hn, ← Int.cast_mul, unitPartChar_intCast hN
    (not_dvd_of_isCoprime (hrs.mul_left (isCoprime_wSeq_right hrs (by lia))) hps), Int.cast_mul,
    hw, ← pow_succ', he, pow_mul,
    ψ.apply_sq_of_isUnit ((ZMod.isUnit_intCast_of_not_dvd hN hpr).pow _)]

/-- For even `s` and a character `ψ` modulo a power `N` of `2` dividing `8`, `χ_ψ(c_n) = 1` for
`n ≥ 3`: `c_n` has the square class of `r w_n`, and `r w_n ≡ r² ≡ 1 (mod 8)`. -/
theorem unitPartChar_two_cSeq_of_even (hrs : IsCoprime r s) (hs : s ≠ 0) (hev : Even s)
    {N k : ℕ} (hN : N = 2 ^ k) (hk : k ≤ 3) (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 3 ≤ n) :
    unitPartChar 2 ψ (cSeq ((r : ℚ) / s) n) = 1 := by
  have hr : Odd r := Int.not_even_iff_odd.mp fun h ↦
    not_dvd_of_isCoprime (p := 2) hrs (even_iff_two_dvd.mp hev) (even_iff_two_dvd.mp h)
  have h8 : ((r * wSeq r s n : ℤ) : ZMod 8) = 1 := by
    push_cast
    rw [intCast_wSeq_zmod_eight_of_even hev hr hn, ← sq, ZMod.intCast_sq_eight_eq_one_of_odd hr]
  have h1 : ((r * wSeq r s n : ℤ) : ZMod N) = 1 := by
    have := congr(ZMod.castHom (hN ▸ pow_dvd_pow 2 hk : N ∣ 2 ^ 3) (ZMod N) $h8)
    rwa [map_intCast, map_one] at this
  have hodd : ¬((2 : ℕ) : ℤ) ∣ r * wSeq r s n := fun h ↦
    Int.not_even_iff_odd.mpr (hr.mul (odd_wSeq_of_even hev hr (by lia))) (even_iff_two_dvd.mpr h)
  rw [mulChar_cSeq_of_two_le _ hs (by lia), ← Int.cast_mul, unitPartChar_intCast hN hodd, h1,
    map_one]

end Primes

end QuadraticIterates
