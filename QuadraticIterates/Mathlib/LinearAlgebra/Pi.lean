/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Injectivity of extension by zero

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Function.ExtendByZero

theorem linearMap_injective (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M]
    {ι η : Type*} {s : ι → η} (hs : Injective s) :
    Injective (linearMap R M s) :=
  extend_injective hs (0 : η → M)

end Function.ExtendByZero
