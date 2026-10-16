/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Big-operator lemmas

An `𝔽₂`-linear combination is the sum over the support of its coefficient function
(`Finset.sum_zmod_two_smul_eq_sum_filter`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Finset

/-- An `𝔽₂`-linear combination is the sum over the support of the coefficient function. -/
theorem sum_zmod_two_smul_eq_sum_filter {ι M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {s : Finset ι} (m : ι → M) (g : ι → ZMod 2) :
    ∑ i ∈ s, g i • m i = ∑ i ∈ s with g i = 1, m i := by
  rw [sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases (show g i = 0 ∨ g i = 1 by generalize g i = z; decide +revert) with h | h <;> simp [h]

end Finset
