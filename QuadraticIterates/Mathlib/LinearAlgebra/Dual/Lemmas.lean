/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear forms with prescribed values on a linearly independent family

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Module

/-- A linear form takes prescribed values on a linearly independent family; compare
`Module.exists_dual_forall_apply_eq_one`, where all values are `1`. -/
theorem exists_dual_forall_apply_eq {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s : Set ι} {v : ι → V} (hli : LinearIndepOn K v s) (g : ι → K) :
    ∃ f : Dual K V, ∀ i ∈ s, f (v i) = g i := by
  let b := Basis.span hli.linearIndependent
  obtain ⟨F, hF⟩ := LinearMap.exists_extend (b.constr K fun i ↦ g i)
  refine ⟨F, fun i hi ↦ ?_⟩
  have := congr($hF (b ⟨i, hi⟩))
  rwa [LinearMap.comp_apply, Basis.constr_basis, Submodule.subtype_apply, Basis.coe_span_apply]
    at this

end Module
