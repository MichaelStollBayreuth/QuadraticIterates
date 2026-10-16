/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Galois.TwoIndependent

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import QuadraticIterates.Galois.Criterion
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic

/-!
# The criterion with characters

A sequence `v 1, v 2, …` in a commutative monoid is 2-independent as soon as for every `n ≥ 1`
some character `φ_n` with values in `ℤ` is `-1` at `v n` and `1` at all later terms
(Proposition 2.3 of the draft); in a field the converse holds, by duality in `Kˣ/(Kˣ)²`. With
Stoll's criterion this characterizes the parameters `a ∈ ℚ` whose arboreal Galois representation
is surjective.

## Main definitions

* `QuadraticIterates.mulCharOfDual f`: the character `x ↦ (-1)^{f [x]}` of a field attached to a
  linear form `f` on its square classes.

## Main statements

* `QuadraticIterates.twoIndependent_of_forall_hasCharPattern`: characters `φ_n` for all `n ≥ 1`
  make a sequence 2-independent.
* `QuadraticIterates.hasCharPattern_of_twoIndependent`: the converse, in a field.
* `QuadraticIterates.tfae_forall_nonempty_mulEquiv`: for `a ∈ ℚ`, `Ω_n ≅ [C₂]ⁿ` for all `n` iff
  `(c_n)_{n ≥ 1}` is 2-independent iff `a` has `φ_n` for every `n ≥ 1`.
-/

@[expose] public section

namespace QuadraticIterates

section mulCharOfDual

variable {K : Type*} [Field K] [DecidableEq K]

/-- The quadratic character `x ↦ (-1)^{f [x]}` of a field `K` attached to a linear form `f` on the
square classes `Kˣ/(Kˣ)²`, with value `0` at `0`. -/
noncomputable def mulCharOfDual (f : Module.Dual (ZMod 2) (SquareClasses K)) : MulChar K ℤ where
  toFun x := if x = 0 then 0 else if f (sqClass x) = 0 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp only [mul_eq_zero, hx, hy, or_self, ite_false, sqClass_mul hx hy, map_add]
    generalize f (sqClass x) = a, f (sqClass y) = b
    revert a b
    decide
  map_nonunit' x hx := by
    rw [isUnit_iff_ne_zero, not_not] at hx
    simp [hx]

lemma mulCharOfDual_apply (f : Module.Dual (ZMod 2) (SquareClasses K)) {x : K} (hx : x ≠ 0) :
    mulCharOfDual f x = if f (sqClass x) = 0 then 1 else -1 :=
  ite_eq_right hx

end mulCharOfDual

/-- Proposition 2.3 of the draft: if for every `n ≥ 1` some character is `-1` at `v n` and `1` at
all later terms, then `v 1, v 2, …` are 2-independent. For a finite nonempty set of indices with
least element `n`, that character is `-1` at the product, which is therefore not a square. -/
theorem twoIndependent_of_forall_hasCharPattern {M : Type*} [CommMonoid M] {v : ℕ → M}
    (h : ∀ n ≥ 1, HasCharPattern v n (Pi.mulSingle n (-1))) :
    TwoIndependent fun m ↦ v (m + 1) := fun S hS hsq ↦ by
  obtain ⟨χ, hχ⟩ := h (S.min' hS + 1) le_add_self
  refine χ.apply_ne_neg_one_of_isSquare hsq ?_
  rw [map_prod, Finset.prod_congr rfl fun i hi ↦ hχ (i + 1) (by simpa using S.min'_le i hi)]
  simp [Pi.mulSingle_apply, Finset.min'_mem]

/-- The converse of `QuadraticIterates.twoIndependent_of_forall_hasCharPattern`: if `v 1, v 2, …`
are 2-independent, then for every `n ≥ 1` some character is `-1` at `v n` and `1` at all later
terms. The class of `v n` lies outside the span of the classes of the later terms, and a linear
form separating it gives the character (`QuadraticIterates.mulCharOfDual`). -/
theorem hasCharPattern_of_twoIndependent {K : Type*} [Field K] {v : ℕ → K}
    (h : TwoIndependent fun m ↦ v (m + 1)) {n : ℕ} (hn : 1 ≤ n) :
    HasCharPattern v n (Pi.mulSingle n (-1)) := by
  classical
  obtain ⟨f, hf, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (((twoIndependent_iff_linearIndependent _).mp h).notMem_span_image
      (s := {m | n ≤ m}) (x := n - 1) (by simp; lia)) inferInstance
  refine ⟨mulCharOfDual f, fun m hm ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by lia⟩
  rw [mulCharOfDual_apply f (h.ne_zero j)]
  rcases hm.eq_or_lt with hm | hm
  · obtain rfl : j = n - 1 := by lia
    rw [Nat.sub_add_cancel hn] at hf ⊢
    simp [hf]
  · have hj : f (sqClass (v (j + 1))) = 0 := by
      have := Submodule.mem_map_of_mem (f := f) (Submodule.subset_span (R := ZMod 2)
        (Set.mem_image_of_mem (fun i ↦ sqClass (v (i + 1))) (show j ∈ {m | n ≤ m} by simp; lia)))
      rwa [hfV, Submodule.mem_bot] at this
    simp [hj, hm.ne']

/-- **The criterion with characters**: for `a ∈ ℚ`, the arboreal Galois representation of `X² + a`
is surjective (`Ω_n ≅ [C₂]ⁿ` for all `n`) iff `(c_n)_{n ≥ 1}` is 2-independent iff for every
`n ≥ 1` some character `φ_n` is `-1` at `c_n` and `1` at all later terms. -/
theorem tfae_forall_nonempty_mulEquiv (a : ℚ) :
    [∀ n, Nonempty (GaloisGroup a n ≃* WreathPower n),
      TwoIndependent fun n : ℕ ↦ cSeq a (n + 1),
      ∀ n ≥ 1, HasCharPattern (cSeq a) n (Pi.mulSingle n (-1))].TFAE := by
  tfae_have 1 ↔ 2 := forall_nonempty_mulEquiv_iff_twoIndependent a
  tfae_have 3 → 2 := twoIndependent_of_forall_hasCharPattern
  tfae_have 2 → 3 := fun h _ hn ↦ hasCharPattern_of_twoIndependent h hn
  tfae_finish

/-- If `a ∈ ℚ` has `φ_n` for every `n ≥ 1`, then `Ω_n ≅ [C₂]ⁿ` for all `n`
(`QuadraticIterates.tfae_forall_nonempty_mulEquiv`). -/
theorem forall_nonempty_mulEquiv_of_forall_hasCharPattern {a : ℚ}
    (h : ∀ n ≥ 1, HasCharPattern (cSeq a) n (Pi.mulSingle n (-1))) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_iff_twoIndependent a).mpr (twoIndependent_of_forall_hasCharPattern h) n

end QuadraticIterates
