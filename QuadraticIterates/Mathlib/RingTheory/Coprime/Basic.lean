/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Coprime.Basic

/-!
# A sum and one of its summands

In a commutative ring, if `x` and `y` are coprime, then so are `x + y` and `y`, `y + x` and `y`, and
in the second argument `x` and `y + x`, `x` and `x + y` (`IsCoprime.add_self_left`,
`IsCoprime.self_add_left`, `IsCoprime.add_self_right`, `IsCoprime.self_add_right`, named like
`Nat.coprime_add_self_left`): the cases `z = 1` of `IsCoprime.add_mul_left_left` and its variants.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IsCoprime

variable {R : Type*} [CommRing R] {x y : R}

theorem add_self_left (h : IsCoprime x y) : IsCoprime (x + y) y := by
  simpa using h.add_mul_left_left 1

theorem self_add_left (h : IsCoprime x y) : IsCoprime (y + x) y := by
  simpa using h.mul_add_left_left 1

theorem add_self_right (h : IsCoprime x y) : IsCoprime x (y + x) := by
  simpa using h.add_mul_left_right 1

theorem self_add_right (h : IsCoprime x y) : IsCoprime x (x + y) := by
  simpa using h.mul_add_left_right 1

end IsCoprime
