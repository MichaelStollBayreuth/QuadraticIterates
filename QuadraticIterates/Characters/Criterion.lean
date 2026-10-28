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
import QuadraticIterates.Galois.Criterion
import QuadraticIterates.Mathlib.LinearAlgebra.Dual.Lemmas
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic

/-!
# The criterion with characters

A sequence `v 1, v 2, …` in a commutative monoid is 2-independent as soon as for every `n ≥ 1`
some character `φ_n` with values in `ℤ` is `-1` at `v n` and `1` at all later terms; in a field
the converse holds, by duality in `Kˣ/(Kˣ)²`. With Stoll's criterion
(`QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent`) this characterizes the
parameters `a ∈ ℚ` whose arboreal Galois representation is surjective.

## Main definitions

* `QuadraticIterates.mulCharOfDual f`: the character `x ↦ (-1)^{f [x]}` of a field attached to a
  linear form `f` on its square classes.

## Main statements

* `QuadraticIterates.twoIndependent_of_forall_hasCharPattern`: characters `φ_n` for all `n ≥ 1`
  make a sequence 2-independent.
* `QuadraticIterates.hasCharPattern_one_of_twoIndependent`: in a field, a 2-independent sequence
  realizes every sign pattern; `QuadraticIterates.hasCharPattern_of_twoIndependent`, the converse,
  is a special case.
* `QuadraticIterates.tfae_forall_nonempty_mulEquiv`: for `a ∈ ℚ`, the Galois groups `Ω_n` of the
  iterates of `X² + a` satisfy `Ω_n ≅ [C₂]ⁿ` for all `n` iff `(c_n)_{n ≥ 1}` is 2-independent iff
  `a` has `φ_n` for every `n ≥ 1`.
* `QuadraticIterates.hasCharPattern_one_of_forall_nonempty_mulEquiv`: if `Ω_n ≅ [C₂]ⁿ` for all `n`,
  then every sign pattern along `(c_n)_{n ≥ 1}` is the pattern of a character.
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
    decide +revert
  map_nonunit' x hx := by
    rw [isUnit_iff_ne_zero, not_not] at hx
    simp [hx]

lemma mulCharOfDual_apply (f : Module.Dual (ZMod 2) (SquareClasses K)) {x : K} (hx : x ≠ 0) :
    mulCharOfDual f x = if f (sqClass x) = 0 then 1 else -1 :=
  ite_eq_right hx

end mulCharOfDual

/-- If for every `n ≥ 1` some character is `-1` at `v n` and `1` at all later terms, then
`v 1, v 2, …` are 2-independent. For a finite nonempty set of indices with least element `n`, that
character is `-1` at the product, which is therefore not a square. -/
theorem twoIndependent_of_forall_hasCharPattern {M : Type*} [CommMonoid M] {v : ℕ → M}
    (h : ∀ n ≥ 1, HasCharPattern v n (Pi.mulSingle n (-1))) :
    TwoIndependent fun m ↦ v (m + 1) := fun S hS hsq ↦ by
  obtain ⟨χ, hχ⟩ := h (S.min' hS + 1) le_add_self
  refine χ.apply_ne_neg_one_of_isSquare hsq ?_
  rw [map_prod, Finset.prod_congr rfl fun i hi ↦ hχ (i + 1) (by simpa using S.min'_le i hi)]
  simp [Pi.mulSingle_apply, Finset.min'_mem]

/-- A 2-independent sequence `v 1, v 2, …` in a field realizes every sign pattern from `1` on:
the classes of its terms in `Kˣ/(Kˣ)²` are linearly independent, so a linear form takes
prescribed values on them (`Module.exists_dual_forall_apply_eq`), and
`QuadraticIterates.mulCharOfDual` turns it into a character. -/
theorem hasCharPattern_one_of_twoIndependent {K : Type*} [Field K] {v : ℕ → K}
    (h : TwoIndependent fun m ↦ v (m + 1)) {ε : ℕ → ℤ} (hε : ∀ m ≥ 1, ε m = 1 ∨ ε m = -1) :
    HasCharPattern v 1 ε := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq
    (linearIndepOn_univ_iff.mpr ((twoIndependent_iff_linearIndependent _).mp h))
    fun m ↦ if ε (m + 1) = 1 then 0 else 1
  refine ⟨mulCharOfDual f, fun m hm ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [mulCharOfDual_apply f (h.ne_zero j), hf j trivial]
  rcases hε (j + 1) hm with h1 | h1 <;> simp [h1]

/-- The converse of `QuadraticIterates.twoIndependent_of_forall_hasCharPattern`: if `v 1, v 2, …`
are 2-independent, then for every `n ≥ 1` some character is `-1` at `v n` and `1` at all later
terms (`QuadraticIterates.hasCharPattern_one_of_twoIndependent`). -/
theorem hasCharPattern_of_twoIndependent {K : Type*} [Field K] {v : ℕ → K}
    (h : TwoIndependent fun m ↦ v (m + 1)) {n : ℕ} (hn : 1 ≤ n) :
    HasCharPattern v n (Pi.mulSingle n (-1)) :=
  (hasCharPattern_one_of_twoIndependent h fun m _ ↦ by
    rcases eq_or_ne m n with rfl | hm <;> simp [*]).mono hn

/-- **The criterion with characters**: for `a ∈ ℚ`, the arboreal Galois representation of `X² + a`
is surjective (`Ω_n ≅ [C₂]ⁿ` for the Galois groups `Ω_n` of all iterates) iff `(c_n)_{n ≥ 1}` is
2-independent iff for every `n ≥ 1` some character `φ_n` is `-1` at `c_n` and `1` at all later
terms. -/
theorem tfae_forall_nonempty_mulEquiv (a : ℚ) :
    [∀ n, Nonempty (GaloisGroup a n ≃* WreathPower n),
      TwoIndependent fun n : ℕ ↦ cSeq a (n + 1),
      ∀ n ≥ 1, HasCharPattern (cSeq a) n (Pi.mulSingle n (-1))].TFAE := by
  tfae_have 1 ↔ 2 := forall_nonempty_mulEquiv_iff_twoIndependent a
  tfae_have 3 → 2 := twoIndependent_of_forall_hasCharPattern
  tfae_have 2 → 3 := fun h _ hn ↦ hasCharPattern_of_twoIndependent h hn
  tfae_finish

/-- **Prescribed signs**: if the Galois groups `Ω_n` of the iterates of `X² + a` satisfy
`Ω_n ≅ [C₂]ⁿ` for all `n`, then every sign pattern along `c_1, c_2, …` is the pattern of a
character (`QuadraticIterates.hasCharPattern_one_of_twoIndependent`). -/
theorem hasCharPattern_one_of_forall_nonempty_mulEquiv {a : ℚ}
    (h : ∀ n, Nonempty (GaloisGroup a n ≃* WreathPower n)) {ε : ℕ → ℤ}
    (hε : ∀ m ≥ 1, ε m = 1 ∨ ε m = -1) :
    HasCharPattern (cSeq a) 1 ε :=
  hasCharPattern_one_of_twoIndependent ((forall_nonempty_mulEquiv_iff_twoIndependent a).mp h) hε

/-- If `a ∈ ℚ` has `φ_n` for every `n ≥ 1` (a character that is `-1` at `c_n` and `1` at all
later terms), then the Galois groups `Ω_n` of the iterates of `X² + a` satisfy `Ω_n ≅ [C₂]ⁿ` for
all `n` (`QuadraticIterates.tfae_forall_nonempty_mulEquiv`). -/
theorem forall_nonempty_mulEquiv_of_forall_hasCharPattern {a : ℚ}
    (h : ∀ n ≥ 1, HasCharPattern (cSeq a) n (Pi.mulSingle n (-1))) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_iff_twoIndependent a).mpr (twoIndependent_of_forall_hasCharPattern h) n

/-- The form of `QuadraticIterates.forall_nonempty_mulEquiv_of_forall_hasCharPattern` used in the
applications: `φ₁` (the pattern `Pi.mulSingle 1 (-1)` along `c_n` from `1` on) comes separately
from the `φ_n` with `n ≥ 2`. -/
theorem forall_nonempty_mulEquiv_of_hasCharPattern_of_forall_hasCharPattern {a : ℚ}
    (h₁ : HasCharPattern (cSeq a) 1 (Pi.mulSingle 1 (-1)))
    (h : ∀ n ≥ 2, HasCharPattern (cSeq a) n (Pi.mulSingle n (-1))) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  forall_nonempty_mulEquiv_of_forall_hasCharPattern (fun n hn ↦ hn.eq_or_lt.elim (· ▸ h₁) (h n)) n

end QuadraticIterates
