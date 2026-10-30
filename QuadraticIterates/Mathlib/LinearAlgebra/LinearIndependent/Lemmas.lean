/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

import Mathlib.Data.ZMod.Basic

/-!
# Linear independence over `ZMod 2`

Over `ZMod 2`, a family is linearly independent iff no nonempty finite subfamily sums to `0`.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- Over `ZMod 2`, a family is linearly independent iff no nonempty finite subfamily sums to `0`:
the only nonzero coefficient is `1`. -/
theorem linearIndependent_zmod_two_iff {ι M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {v : ι → M} :
    LinearIndependent (ZMod 2) v ↔ ∀ s : Finset ι, s.Nonempty → ∑ i ∈ s, v i ≠ 0 := by
  classical
  rw [linearIndependent_iff']
  refine ⟨fun h s ⟨i, hi⟩ hs ↦ one_ne_zero (h s 1 (by simpa using hs) i hi),
    fun h s g hg i hi ↦ by_contra fun hgi ↦ h (s.filter (g · ≠ 0)) ⟨i, by simp [hi, hgi]⟩ ?_⟩
  refine (Finset.sum_filter _ _).trans (Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) hg)
  split_ifs with hj
  · rw [(by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hj, one_smul]
  · rw [not_not.mp hj, zero_smul]
