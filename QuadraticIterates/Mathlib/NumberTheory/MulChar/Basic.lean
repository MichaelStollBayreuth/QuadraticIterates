/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Multiplicative characters with values in `ℤ`

A multiplicative character with values in `ℤ` takes the values `±1` at units, so it is quadratic
(`MulChar.isQuadratic_int`); on a commutative group with zero it is invariant under inversion and
trivial on nonzero squares. A character with values in an ordered ring is never `-1` at a square
(`MulChar.apply_ne_neg_one_of_isSquare`), which is how characters detect non-squares.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace MulChar

section CommMonoid

variable {M : Type*} [CommMonoid M]

/-- A multiplicative character with values in `ℤ` takes the values `±1` at units. -/
lemma apply_eq_one_or_eq_neg_one (χ : MulChar M ℤ) {x : M} (hx : IsUnit x) :
    χ x = 1 ∨ χ x = -1 :=
  Int.isUnit_iff.mp (hx.map χ)

lemma isQuadratic_int (χ : MulChar M ℤ) : χ.IsQuadratic := fun x ↦ by
  by_cases hx : IsUnit x
  · exact .inr (χ.apply_eq_one_or_eq_neg_one hx)
  · exact .inl (χ.map_nonunit hx)

/-- A square never has the value `-1` under a character into an ordered ring, since
`χ (y * y) = χ y * χ y ≥ 0`. -/
lemma apply_ne_neg_one_of_isSquare {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (χ : MulChar M R) {x : M} (hx : IsSquare x) : χ x ≠ -1 := by
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul]
  exact (neg_one_lt_zero.trans_le (mul_self_nonneg _)).ne'

end CommMonoid

section CommGroupWithZero

variable {K : Type*} [CommGroupWithZero K] (χ : MulChar K ℤ)

@[simp] lemma apply_inv (x : K) : χ x⁻¹ = χ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact Int.eq_of_mul_eq_one (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])

lemma apply_div (x y : K) : χ (x / y) = χ x * χ y := by
  rw [div_eq_mul_inv, map_mul, apply_inv]

lemma apply_sq {x : K} (hx : x ≠ 0) : χ (x ^ 2) = 1 := by
  rcases χ.apply_eq_one_or_eq_neg_one hx.isUnit with h | h <;> simp [map_pow, h]

lemma apply_mul_sq (x : K) {y : K} (hy : y ≠ 0) : χ (x * y ^ 2) = χ x := by
  rw [map_mul, apply_sq χ hy, mul_one]

lemma apply_div_sq (x : K) {y : K} (hy : y ≠ 0) : χ (x / y ^ 2) = χ x := by
  rw [apply_div, apply_sq χ hy, mul_one]

end CommGroupWithZero

end MulChar
