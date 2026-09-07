/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Ring.Int.Defs

/-!
# The cast of a sign

An integer `ε` with `ε² = 1` keeps this property under the cast into any ring.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

lemma Int.cast_sq_eq_one_of_sq_eq_one {S : Type*} [Ring S] {ε : ℤ} (hε : ε ^ 2 = 1) :
    (ε : S) ^ 2 = 1 := by
  rw [← Int.cast_pow, hε, Int.cast_one]

end
