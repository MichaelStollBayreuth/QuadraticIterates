/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The quadratic character modulo `p` at `-1` and at its square roots

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace ZMod

theorem quadraticChar_neg_one_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr fun h ↦ exists_sq_eq_neg_one_iff.mp h hp

theorem quadraticChar_neg_one_of_mod_four_eq_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    quadraticChar (ZMod p) (-1) = 1 :=
  (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (exists_sq_eq_neg_one_iff.mpr (by lia))

/-- For `p ≡ 5 (mod 8)`, a square root of `-1` modulo `p` is not a square: by Euler's criterion
its quadratic character is `t^((p - 1)/2) = (t²)^((p - 1)/4) = (-1)^((p - 1)/4)`. -/
theorem quadraticChar_eq_neg_one_of_sq_eq_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 8 = 5)
    {t : ZMod p} (ht : t ^ 2 = -1) : quadraticChar (ZMod p) t = -1 := by
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; lia
  have hc := quadraticChar_eq_pow_of_char_ne_two' h2 t
  rw [ZMod.card, show p / 2 = 2 * (2 * (p / 8) + 1) by lia, pow_mul, ht,
    Odd.neg_one_pow ⟨_, rfl⟩] at hc
  refine (quadraticChar_dichotomy fun h ↦ by simp [h] at ht).resolve_left fun h ↦
    Ring.neg_one_ne_one_of_char_ne_two h2 ?_
  rw [← hc, h, Int.cast_one]

end ZMod
