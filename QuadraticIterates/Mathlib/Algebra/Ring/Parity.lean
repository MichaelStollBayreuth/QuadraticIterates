/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Ring.Parity

/-!
# Squares up to a nonzero square factor

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

theorem isSquare_mul_sq_iff₀ {α : Type*} [CommGroupWithZero α] {a b : α} (hb : b ≠ 0) :
    IsSquare (a * b ^ 2) ↔ IsSquare a :=
  ⟨fun h ↦ mul_div_cancel_right₀ a (pow_ne_zero 2 hb) ▸ h.div (.sq b), fun h ↦ h.mul (.sq b)⟩
