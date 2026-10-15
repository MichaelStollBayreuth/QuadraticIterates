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
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.SquareClasses

/-!
# Characters at the primes of `r`, `s`, `r + s`, `r + 2s` and `r² + s²`

For `a = r/s` with `r, s` coprime, the values along `(c_n)` of the characters at a prime `p`
dividing `r` or `s`: the valuation parity `Rat.valChar p` and the characters
`Rat.unitPartChar p ψ` for `ψ` modulo a power of `p`. At `p ∣ r` they are constant from `n = 2`
on (with a twist by `ψ(-1)` at `n = 1`); at `p ∣ s` they are trivial from `n = 2` on (from `n = 3`
on for `p = 2` and `ψ` modulo `8`, `4` or `2`). At `p ∣ r + s` they have period two from
`n = 2` on; at an odd `p ∣ r + 2s` they are constant; at an odd `p ∣ r² + s²` they have period two.

## Main statements

* `QuadraticIterates.valChar_cSeq_of_dvd_left`, `QuadraticIterates.unitPartChar_cSeq_of_dvd_left`:
  `p ∣ r`.
* `QuadraticIterates.valChar_cSeq_of_dvd_right`, `QuadraticIterates.unitPartChar_cSeq_of_dvd_right`,
  `QuadraticIterates.unitPartChar_two_cSeq_of_even`: `p ∣ s`.
* `QuadraticIterates.valChar_cSeq_two_mul_of_dvd_add`,
  `QuadraticIterates.unitPartChar_cSeq_two_mul_of_dvd_add` and their odd-index companions:
  `p ∣ r + s`.
* `QuadraticIterates.unitPartChar_cSeq_of_dvd_add_two_mul`: `p ∣ r + 2s`.
* `QuadraticIterates.unitPartChar_cSeq_two_mul_of_dvd_sq_add_sq`,
  `QuadraticIterates.unitPartChar_cSeq_two_mul_add_one_of_dvd_sq_add_sq`: `p ∣ r² + s²`.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

section Primes

variable {r s : ℤ} {p : ℕ}

private lemma dvd_of_natCast_pow_dvd {N k : ℕ} (hN : N = p ^ k) (hk : k ≠ 0) {x : ℤ}
    (h : (N : ℤ) ∣ x) : (p : ℤ) ∣ x :=
  (dvd_pow_self (p : ℤ) hk).trans (mod_cast hN ▸ h)

variable [Fact p.Prime]

private lemma not_dvd_of_isCoprime {x y : ℤ} (h : IsCoprime x y) (hy : (p : ℤ) ∣ y) :
    ¬(p : ℤ) ∣ x :=
  fun hx ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (h.isUnit_of_dvd' hx hy)

private lemma not_dvd_mul {x y : ℤ} (hx : ¬(p : ℤ) ∣ x) (hy : ¬(p : ℤ) ∣ y) : ¬(p : ℤ) ∣ x * y :=
  (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_mul hx hy

private lemma isCoprime_add_left (hrs : IsCoprime r s) : IsCoprime (r + s) r := by
  simpa [add_comm] using hrs.symm.add_mul_left_left 1

private lemma isCoprime_add_right (hrs : IsCoprime r s) : IsCoprime (r + s) s := by
  simpa using hrs.add_mul_left_left 1

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
  have hpr : (p : ℤ) ∣ r := dvd_of_natCast_pow_dvd hN hk hNr
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
  have hps : (p : ℤ) ∣ s := dvd_of_natCast_pow_dvd hN hk hNs
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

/-! ### Primes of `r + s`, `r + 2s` and `r² + s²` -/

/-- At a prime `p ∣ r + s`, `c_n` is a `p`-adic unit for odd `n`. -/
theorem valChar_cSeq_two_mul_add_one_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hp : (p : ℤ) ∣ r + s) (k : ℕ) : valChar p (cSeq ((r : ℚ) / s) (2 * k + 1)) = 1 := by
  have hpr := not_dvd_of_isCoprime (isCoprime_add_left hrs).symm hp
  have hps := not_dvd_of_isCoprime (isCoprime_add_right hrs).symm hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mulChar_cSeq_one_eq_mul _ hs, valChar_neg_one, valChar_intCast_of_not_dvd hpr,
      valChar_intCast_of_not_dvd hps, mul_one, mul_one]
  · have hw : ¬(p : ℤ) ∣ wSeq r s (2 * k + 1) := fun h ↦ hps <| (Nat.prime_iff_prime_int.mp
      Fact.out).dvd_of_dvd_pow (((wSeq_two_mul_add_one_modEq hrs hk).of_dvd hp).dvd_iff.mp h)
    rw [mulChar_cSeq_of_two_le _ hs (by lia), map_mul, valChar_intCast_of_not_dvd hpr,
      valChar_intCast_of_not_dvd hw, mul_one]

/-- At a prime `p ∣ r + s`, `c_{2k}` has the `p`-adic valuation of `r + s` modulo `2`, for
`k ≥ 1`: `w_{2k} = (r + s) T` with `T` prime to `r + s`. -/
theorem valChar_cSeq_two_mul_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hp : (p : ℤ) ∣ r + s) {k : ℕ} (hk : 1 ≤ k) :
    valChar p (cSeq ((r : ℚ) / s) (2 * k)) = valChar p ((r + s : ℤ) : ℚ) := by
  have hpr := not_dvd_of_isCoprime (isCoprime_add_left hrs).symm hp
  have hps := not_dvd_of_isCoprime (isCoprime_add_right hrs).symm hp
  obtain ⟨T, hw, hT⟩ := exists_wSeq_two_mul_eq hrs hk
  have hpT : ¬(p : ℤ) ∣ T := fun h ↦ hps <| (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow
    ((hT.of_dvd hp).dvd_iff.mp h)
  rw [mulChar_cSeq_of_two_le _ hs (by lia), hw, Int.cast_mul, map_mul, map_mul,
    valChar_intCast_of_not_dvd hpr, valChar_intCast_of_not_dvd hpT, one_mul, mul_one]

/-- At a power `N = p^k` (`k ≥ 1`) dividing `r + s`, `χ_ψ(c_1) = 1`: `-rs ≡ s² (mod r + s)`. -/
theorem unitPartChar_cSeq_one_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hNrs : (N : ℤ) ∣ r + s) (ψ : MulChar (ZMod N) ℤ) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) 1) = 1 := by
  have hp := dvd_of_natCast_pow_dvd hN hk hNrs
  have hps := not_dvd_of_isCoprime (isCoprime_add_right hrs).symm hp
  have hpr := not_dvd_of_isCoprime (isCoprime_add_left hrs).symm hp
  have hc : ((-(r * s) : ℤ) : ZMod N) = ((s ^ 2 : ℤ) : ZMod N) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hNrs.trans ⟨s, by ring⟩)
  have hrs' : ¬(p : ℤ) ∣ -(r * s) := by simpa using not_dvd_mul hpr hps
  rw [mulChar_cSeq_one _ hs, show -((r : ℚ) * s) = ((-(r * s) : ℤ) : ℚ) by push_cast; ring,
    unitPartChar_intCast hN hrs', hc, Int.cast_pow,
    ψ.apply_sq_of_isUnit (ZMod.isUnit_intCast_of_not_dvd hN hps)]



/-- At a power `N = p^k` (`k ≥ 1`) dividing `r + s`, `χ_ψ(c_{2j+1}) = ψ(-1)` for `j ≥ 1`: there
`r w_{2j+1} ≡ -s^{2^{2j}} (mod r + s)`. -/
theorem unitPartChar_cSeq_two_mul_add_one_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hNrs : (N : ℤ) ∣ r + s) (ψ : MulChar (ZMod N) ℤ) {j : ℕ}
    (hj : 1 ≤ j) : unitPartChar p ψ (cSeq ((r : ℚ) / s) (2 * j + 1)) = ψ (-1) := by
  have hp := dvd_of_natCast_pow_dvd hN hk hNrs
  have hps := not_dvd_of_isCoprime (isCoprime_add_right hrs).symm hp
  have hpr := not_dvd_of_isCoprime (isCoprime_add_left hrs).symm hp
  have hpw : ¬(p : ℤ) ∣ wSeq r s (2 * j + 1) := fun h ↦ hps <|
    (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow
      (((wSeq_two_mul_add_one_modEq hrs hj).of_dvd hp).dvd_iff.mp h)
  have hc : ((r * wSeq r s (2 * j + 1) : ℤ) : ZMod N) =
      -1 * ((s ^ 2 ^ (2 * j - 1) : ℤ) : ZMod N) ^ 2 := by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr
      ((mul_wSeq_two_mul_add_one_modEq hrs hj).of_dvd hNrs)
  rw [mulChar_cSeq_of_two_le _ hs (by lia), ← Int.cast_mul,
    unitPartChar_intCast hN (not_dvd_mul hpr hpw), hc, map_mul,
    ψ.apply_sq_of_isUnit (ZMod.isUnit_intCast_of_not_dvd hN (fun h ↦ hps <|
      (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow h)), mul_one]

/-- At a power `N = p^k` (`k ≥ 1`) dividing `r + s`, `χ_ψ(c_{2j}) = ψ(-1) ψ(s) χ_ψ(r + s)` for
`j ≥ 1`: `w_{2j} = (r + s) T` with `T` congruent to an even power of `s` modulo `r + s`, and
`r ≡ -s`. -/
theorem unitPartChar_cSeq_two_mul_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hNrs : (N : ℤ) ∣ r + s) (ψ : MulChar (ZMod N) ℤ) {j : ℕ}
    (hj : 1 ≤ j) : unitPartChar p ψ (cSeq ((r : ℚ) / s) (2 * j)) =
      ψ (-1) * ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) := by
  have hp := dvd_of_natCast_pow_dvd hN hk hNrs
  have hps := not_dvd_of_isCoprime (isCoprime_add_right hrs).symm hp
  have hpr := not_dvd_of_isCoprime (isCoprime_add_left hrs).symm hp
  obtain ⟨T, hw, hT⟩ := exists_wSeq_two_mul_eq hrs hj
  have hpT : ¬(p : ℤ) ∣ T := fun h ↦ hps <| (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow
    ((hT.of_dvd hp).dvd_iff.mp h)
  have hr : (r : ZMod N) = -1 * s := by
    rw [neg_one_mul, eq_neg_iff_add_eq_zero, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hNrs
  have hTs : (T : ZMod N) = ((s : ZMod N) ^ (2 ^ (2 * j - 2) - 1)) ^ 2 := by
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr (hT.of_dvd hNrs), Int.cast_pow, ← pow_mul]
    congr 1
    have := Nat.one_le_two_pow (n := 2 * j - 2)
    rw [show 2 * j - 1 = 2 * j - 2 + 1 by lia, pow_succ]
    lia
  rw [mulChar_cSeq_of_two_le _ hs (by lia), hw, Int.cast_mul, map_mul, map_mul,
    unitPartChar_intCast hN hpr, unitPartChar_intCast hN hpT, hr, hTs, map_mul,
    ψ.apply_sq_of_isUnit ((ZMod.isUnit_intCast_of_not_dvd hN hps).pow _), mul_one]

private lemma isUnit_two_zmod {N k : ℕ} (hN : N = p ^ k) (hp2 : p ≠ 2) : IsUnit (2 : ZMod N) := by
  have := ZMod.isUnit_intCast_of_not_dvd hN (m := 2) fun h ↦ hp2 <|
    (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (mod_cast h)
  exact_mod_cast this

/-- At a power `N = p^k` (`k ≥ 1`) of an odd prime dividing `r + 2s`, `χ_ψ(c_n) = ψ(2)` for
`n ≥ 1`: modulo `N`, `a = -2`, whose sequence is constant `2`. -/
theorem unitPartChar_cSeq_of_dvd_add_two_mul (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k)
    (hk : k ≠ 0) (hp2 : p ≠ 2) (hdvd : (N : ℤ) ∣ r + 2 * s)
    (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 1 ≤ n) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = ψ 2 := by
  have hp := dvd_of_natCast_pow_dvd hN hk hdvd
  have hps : ¬(p : ℤ) ∣ s := fun h ↦
    not_dvd_of_isCoprime hrs h (by simpa using dvd_sub hp (h.mul_left 2))
  obtain ⟨σ, hσ⟩ := (ZMod.isUnit_intCast_of_not_dvd hN hps).exists_right_inv
  have h0 : ((r + 2 * s : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have ha : (r : ZMod N) * σ = -2 := by
    push_cast at h0
    linear_combination σ * h0 - 2 * hσ
  rw [unitPartChar_cSeq hN hk ψ hσ hn (by rw [ha, cSeq_neg_two hn]; exact isUnit_two_zmod hN hp2),
    ha, cSeq_neg_two hn]

/-- Modulo a power `N = p^k` (`k ≥ 1`) of a prime dividing `r² + s²`, `s` has an inverse `σ` and
the parameter `a = r σ` satisfies `a² = -1`. -/
private lemma exists_sq_eq_neg_one (hrs : IsCoprime r s) {N k : ℕ} (hN : N = p ^ k) (hk : k ≠ 0)
    (hdvd : (N : ℤ) ∣ r ^ 2 + s ^ 2) :
    ∃ σ : ZMod N, (s : ZMod N) * σ = 1 ∧ ((r : ZMod N) * σ) ^ 2 = -1 := by
  have hp := dvd_of_natCast_pow_dvd hN hk hdvd
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ not_dvd_of_isCoprime hrs h <|
    (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow
      (by simpa using dvd_sub hp (h.pow two_ne_zero) : (p : ℤ) ∣ r ^ 2)
  obtain ⟨σ, hσ⟩ := (ZMod.isUnit_intCast_of_not_dvd hN hps).exists_right_inv
  have h0 : ((r ^ 2 + s ^ 2 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  push_cast at h0
  exact ⟨σ, hσ, by linear_combination σ ^ 2 * h0 - (s * σ + 1) * hσ⟩

/-- At a power `N = p^k` (`k ≥ 1`) of an odd prime dividing `r² + s²`,
`χ_ψ(c_{2j+1}) = ψ(-rs)`: modulo `N` the sequence is `-a, a - 1, -a, a - 1, …` with `a² = -1`. -/
theorem unitPartChar_cSeq_two_mul_add_one_of_dvd_sq_add_sq (hrs : IsCoprime r s) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hdvd : (N : ℤ) ∣ r ^ 2 + s ^ 2) (ψ : MulChar (ZMod N) ℤ)
    (j : ℕ) : unitPartChar p ψ (cSeq ((r : ℚ) / s) (2 * j + 1)) = ψ (-(r * s)) := by
  obtain ⟨σ, hσ, ha⟩ := exists_sq_eq_neg_one hrs hN hk hdvd
  have hu : IsUnit (cSeq ((r : ZMod N) * σ) (2 * j + 1)) := by
    rw [cSeq_two_mul_add_one_of_sq_eq_neg_one ha]
    exact (IsUnit.of_mul_eq_one (-((r : ZMod N) * σ)) (by linear_combination -ha)).neg
  rw [unitPartChar_cSeq hN hk ψ hσ (by lia) hu, cSeq_two_mul_add_one_of_sq_eq_neg_one ha,
    neg_mul_eq_neg_mul, map_mul, ψ.apply_eq_of_mul_eq_one hσ, ← map_mul, neg_mul]

/-- At a power `N = p^k` (`k ≥ 1`) of an odd prime dividing `r² + s²`,
`χ_ψ(c_{2j}) = ψ((r - s)s)` for `j ≥ 1`. -/
theorem unitPartChar_cSeq_two_mul_of_dvd_sq_add_sq (hrs : IsCoprime r s) {N k : ℕ}
    (hN : N = p ^ k) (hk : k ≠ 0) (hp2 : p ≠ 2) (hdvd : (N : ℤ) ∣ r ^ 2 + s ^ 2)
    (ψ : MulChar (ZMod N) ℤ) {j : ℕ} (hj : 1 ≤ j) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) (2 * j)) = ψ ((r - s) * s) := by
  obtain ⟨σ, hσ, ha⟩ := exists_sq_eq_neg_one hrs hN hk hdvd
  obtain ⟨u, hu⟩ := (isUnit_two_zmod hN hp2).neg.exists_right_inv
  have hu' : IsUnit (cSeq ((r : ZMod N) * σ) (2 * j)) := by
    rw [cSeq_two_mul_of_sq_eq_neg_one ha hj]
    exact IsUnit.of_mul_eq_one (((r : ZMod N) * σ + 1) * u) (by linear_combination u * ha + hu)
  have he : (r : ZMod N) * σ - 1 = (r - s) * σ := by linear_combination hσ
  rw [unitPartChar_cSeq hN hk ψ hσ (by lia) hu', cSeq_two_mul_of_sq_eq_neg_one ha hj, he, map_mul,
    ψ.apply_eq_of_mul_eq_one hσ, ← map_mul]

end Primes

end QuadraticIterates
