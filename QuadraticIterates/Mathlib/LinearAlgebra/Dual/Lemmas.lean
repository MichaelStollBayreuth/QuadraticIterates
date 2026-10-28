/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear forms with prescribed values

On a linearly independent family, any values can be prescribed; on an arbitrary family, exactly
the values that satisfy the linear relations of the family. The latter rests on
`LinearMap.exists_comp_eq_of_ker_le`: a linear map of vector spaces factors through any linear map
whose kernel lies in its own.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace LinearMap

/-- A linear map `B` factors through a linear map `A` of vector spaces as soon as the kernel of `A`
lies in the kernel of `B`. -/
theorem exists_comp_eq_of_ker_le {K V W U : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U] (A : W →ₗ[K] V) (B : W →ₗ[K] U)
    (h : ker A ≤ ker B) :
    ∃ F : V →ₗ[K] U, F ∘ₗ A = B := by
  obtain ⟨F, hF⟩ := exists_extend ((ker A).liftQ B h ∘ₗ A.quotKerEquivRange.symm.toLinearMap)
  exact ⟨F, ext fun w ↦ by simpa using congr($hF ⟨A w, mem_range_self A w⟩)⟩

end LinearMap

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

/-- A linear form with prescribed values `g i` on a family `v i` exists iff every linear relation
among the `v i` holds for the `g i` as well; compare `Module.exists_dual_forall_apply_eq`, for a
linearly independent family. -/
theorem exists_dual_forall_apply_eq_iff {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : ι → V) (g : ι → K) :
    (∃ f : Dual K V, ∀ i, f (v i) = g i) ↔
      ∀ c : ι →₀ K, Finsupp.linearCombination K v c = 0 → Finsupp.linearCombination K g c = 0 := by
  refine ⟨fun ⟨f, hf⟩ c hc ↦ ?_, fun h ↦ ?_⟩
  · have := congr(f $hc)
    rw [map_zero, Finsupp.apply_linearCombination] at this
    exact funext hf ▸ this
  · obtain ⟨F, hF⟩ := LinearMap.exists_comp_eq_of_ker_le _ _ fun c hc ↦ h c hc
    exact ⟨F, fun i ↦ by simpa using congr($hF (Finsupp.single i 1))⟩

end Module
