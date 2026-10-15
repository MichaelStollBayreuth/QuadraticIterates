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

/-!
# Characters of `ℚ` on the terms `c_n`

For `a = r/s`, the term `c_1 = -r/s` has the square class of `-rs`, and `c_n`, `n ≥ 2`, that of
`r w_n`. For the character `χ_ψ = Rat.unitPartChar p ψ` attached to a character `ψ` modulo a power
`N` of a prime `p` not dividing `s`, `χ_ψ(c_n) = ψ(c̄_n)` whenever the term `c̄_n` of the sequence
of `r/s` in `ZMod N` is a unit (`QuadraticIterates.unitPartChar_cSeq`): every local computation
of `χ_ψ` along `(c_n)` happens in `ZMod N`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- `c_1 = -r/s = -rs/s²` has the square class of `-rs`. -/
theorem mulChar_cSeq_one (χ : MulChar ℚ ℤ) (hs : s ≠ 0) :
    χ (cSeq ((r : ℚ) / s) 1) = χ (-(r * s)) := by
  have hs' : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  rw [cSeq_one, ← χ.apply_div_sq (-(r * s)) hs']
  congr 1
  field

/-- For every character `χ` of `ℚ`, `χ(c_1) = χ(-1) χ(r) χ(s)`. -/
theorem mulChar_cSeq_one_eq_mul (χ : MulChar ℚ ℤ) (hs : s ≠ 0) :
    χ (cSeq ((r : ℚ) / s) 1) = χ (-1) * χ r * χ s := by
  rw [mulChar_cSeq_one χ hs, neg_eq_neg_one_mul, map_mul, map_mul, mul_assoc]

/-- For `n ≥ 2`, `c_n = r w_n / s^{2^{n-1}}` has the square class of `r w_n`, the exponent
`2^{n-1}` being even. -/
theorem mulChar_cSeq_of_two_le (χ : MulChar ℚ ℤ) (hs : s ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    χ (cSeq ((r : ℚ) / s) n) = χ (r * wSeq r s n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by lia⟩
  rw [cSeq_div_eq r hs (by lia), show m + 2 - 1 = m + 1 by lia, pow_succ, pow_mul]
  exact χ.apply_div_sq _ (pow_ne_zero _ (Int.cast_ne_zero.mpr hs))

/-- **Local evaluation**: let `ψ` be a character modulo a power `N = p^k` (`k ≥ 1`) of a prime
`p`, let `σ` invert `s` modulo `N`, and let `c̄` be the sequence of `r σ` in `ZMod N`. If `c̄_n` is
a unit, then `χ_ψ(c_n) = ψ(c̄_n)` for the character `χ_ψ = Rat.unitPartChar p ψ`: by the
reduction `r w_n = s^{2^{n-1}} c̄_n`, the integer `r w_n` is prime to `p`, and the powers of
`ψ(s) = ±1` cancel. -/
theorem unitPartChar_cSeq {p N k : ℕ} [Fact p.Prime] (hN : N = p ^ k) (hk : k ≠ 0)
    (ψ : MulChar (ZMod N) ℤ) {σ : ZMod N} (hσ : (s : ZMod N) * σ = 1) {n : ℕ} (hn : 1 ≤ n)
    (hu : IsUnit (cSeq ((r : ZMod N) * σ) n)) :
    Rat.unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = ψ (cSeq ((r : ZMod N) * σ) n) := by
  have hsu : IsUnit (s : ZMod N) := .of_mul_eq_one σ hσ
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ ZMod.not_isUnit_intCast_of_dvd hN hk h hsu
  have hred := intCast_mul_wSeq r hσ hn
  have hpw : ¬(p : ℤ) ∣ r * wSeq r s n := fun h ↦
    ZMod.not_isUnit_intCast_of_dvd hN hk h (by push_cast; rw [hred]; exact (hsu.pow _).mul hu)
  have hs : s ≠ 0 := fun h ↦ hps (h ▸ dvd_zero _)
  have hψs : ψ s ^ 2 = 1 := by
    rcases ψ.apply_eq_one_or_eq_neg_one hsu with h | h <;> simp [h]
  rw [cSeq_div_eq r hs hn, MulChar.apply_div, ← Int.cast_mul, ← Int.cast_pow,
    Rat.unitPartChar_intCast hN hpw, Rat.unitPartChar_intCast hN
      fun h ↦ hps ((Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow h),
    Int.cast_mul, hred, Int.cast_pow, map_mul, map_pow, mul_right_comm, ← mul_pow, ← sq,
    hψs, one_pow, one_mul]

end QuadraticIterates
