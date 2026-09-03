/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.Order.Units

/-!
# The sign of a nonzero integer is a square root of `1`

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- The sign of a nonzero integer is a unit of `ℤ`, hence squares to `1`. -/
theorem Int.sign_sq_of_ne_zero {a : ℤ} (ha : a ≠ 0) : a.sign ^ 2 = 1 :=
  isUnit_sq (isUnit_iff_natAbs_eq.mpr (natAbs_sign_of_ne_zero ha))
