/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Non-squares have a prime with odd exponent

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Int

/-- A nonnegative integer that is not a square has a prime `p` with odd exponent: `s = p^k m` with
`k` odd and `p ∤ m`. -/
theorem exists_prime_pow_mul_of_not_isSquare {s : ℤ} (hs : 0 ≤ s) (h : ¬IsSquare s) :
    ∃ p k : ℕ, ∃ m : ℤ, p.Prime ∧ Odd k ∧ s = p ^ k * m ∧ ¬(p : ℤ) ∣ m := by
  obtain ⟨p, hp, hk⟩ : ∃ p : ℕ, p.Prime ∧ ¬Even (s.natAbs.factorization p) := by
    simpa [Int.isSquare_iff_nonneg_even_factorization, hs] using h
  refine ⟨p, _, (ordCompl[p] s.natAbs : ℕ), hp, Nat.not_even_iff_odd.mp hk, ?_, ?_⟩
  · rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self, Int.natCast_natAbs,
      abs_of_nonneg hs]
  · exact_mod_cast Nat.not_dvd_ordCompl hp
      (Int.natAbs_ne_zero.mpr <| by rintro rfl; exact h .zero)

end Int
