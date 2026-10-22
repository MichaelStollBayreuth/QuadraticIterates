/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Ring.Int.Parity

/-!
# Integer squares: residues modulo `4` and `8`, products of consecutive integers

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Int

/-- An integer `≡ 2` or `3 (mod 4)` is not a square. -/
theorem not_isSquare_of_two_le_emod_four {x : ℤ} (h : 2 ≤ x % 4) : ¬IsSquare x :=
  fun ⟨t, ht⟩ ↦ by lia [Int.sq_emod_four t]

theorem sq_emod_eight_eq_one_of_odd {x : ℤ} (hx : Odd x) : x ^ 2 % 8 = 1 := by
  lia [Int.eight_dvd_sq_sub_one_of_odd hx]

/-- An integer `≡ 5 (mod 8)` is not a square. -/
theorem not_isSquare_of_emod_eight_eq_five {x : ℤ} (h : x % 8 = 5) : ¬IsSquare x :=
  fun ⟨t, ht⟩ ↦ by
    rcases t.even_or_odd with ⟨k, rfl⟩ | ht'
    · lia
    · lia [sq_emod_eight_eq_one_of_odd ht']

/-- `a (a + 1)` is a square only for `a = 0, -1`: from `a (a + 1) = t²`,
`(2a + 1 - 2t)(2a + 1 + 2t) = 1`, so both factors are `±1` and `t = 0`. -/
theorem not_isSquare_mul_add_one {a : ℤ} (h₀ : a ≠ 0) (h₁ : a ≠ -1) : ¬IsSquare (a * (a + 1)) :=
  fun ⟨t, ht⟩ ↦ by
    have h : (2 * a + 1 - 2 * t).natAbs * (2 * a + 1 + 2 * t).natAbs = 1 := by
      rw [← natAbs_mul, show (2 * a + 1 - 2 * t) * (2 * a + 1 + 2 * t) = 1 by grobner]
      rfl
    lia [Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h]

end Int
