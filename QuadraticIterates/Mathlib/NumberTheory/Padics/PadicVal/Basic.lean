/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The `p`-adic valuation of a finite product of rationals

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace padicValRat

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuation of a finite product of nonzero rationals is the sum of the
valuations. -/
protected theorem prod {ι : Type*} {s : Finset ι} {f : ι → ℚ} (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValRat.mul (hf a (by simp))
      (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (by simp [hi])),
      ih fun i hi ↦ hf i (by simp [hi])]

end padicValRat
