/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Linear independence of two families with the same span

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- Two finite families with the same index type and the same span are simultaneously linearly
independent or not. -/
theorem linearIndependent_iff_of_span_range_eq {R M : Type*} [Semiring R] [OrzechProperty R]
    [Nontrivial R] [AddCommMonoid M] [Module R M] {ι : Type*} [Finite ι] {v w : ι → M}
    (h : Submodule.span R (Set.range v) = Submodule.span R (Set.range w)) :
    LinearIndependent R v ↔ LinearIndependent R w := by
  have := Fintype.ofFinite ι
  simp only [linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  rw [h]
