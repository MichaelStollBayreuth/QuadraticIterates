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

/-- A nonzero square is `4^k m` with `m ≡ 1 (mod 8)`; the integers not of this form are the
non-squares in `ℚ₂`. -/
theorem exists_eq_four_pow_mul_of_isSquare {x : ℤ} (hx : IsSquare x) (h0 : x ≠ 0) :
    ∃ k : ℕ, ∃ m : ℤ, x = 4 ^ k * m ∧ m % 8 = 1 := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨k, u, hu, ht⟩ := Nat.exists_eq_two_pow_mul_odd (n := t.natAbs) (by simpa using h0)
  refine ⟨k, u ^ 2, ?_, ?_⟩
  · rw [← Int.natAbs_mul_self' t, ht]
    push_cast
    rw [mul_mul_mul_comm, ← mul_pow]
    simp [sq]
  · lia [Int.eight_dvd_sq_sub_one_of_odd (k := (u : ℤ)) (mod_cast hu)]

end Int
