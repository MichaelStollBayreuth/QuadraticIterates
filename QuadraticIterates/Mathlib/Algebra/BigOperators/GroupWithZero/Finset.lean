/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Products of integer powers of a fixed base

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- A product of powers of a fixed nonzero base with integer exponents collapses to a single
power. -/
theorem Finset.prod_zpow_eq_zpow_sum₀ {ι G₀ : Type*} [CommGroupWithZero G₀] {x : G₀} (hx : x ≠ 0)
    (s : Finset ι) (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [prod_cons, sum_cons, ih, zpow_add₀ hx]
