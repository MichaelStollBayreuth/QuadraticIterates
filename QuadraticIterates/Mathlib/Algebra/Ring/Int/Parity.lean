/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Ring.Int.Parity

/-!
# Squares modulo `4` and `8`

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Int

/-- An integer `≡ 2` or `3 (mod 4)` is not a square. -/
theorem not_isSquare_of_two_le_emod_four {x : ℤ} (h : 2 ≤ x % 4) : ¬IsSquare x :=
  fun ⟨t, ht⟩ ↦ by
    have := Int.sq_emod_four t
    rw [sq, ← ht] at this
    lia

theorem sq_emod_eight_eq_one_of_odd {x : ℤ} (hx : Odd x) : x ^ 2 % 8 = 1 := by
  rw [sq, Int.mul_emod]
  rcases (by lia [Int.odd_iff.mp hx] : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7) with
    h | h | h | h <;> simp [h]

end Int
