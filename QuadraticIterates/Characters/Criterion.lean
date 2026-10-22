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
* `QuadraticIterates.hasCharPattern_of_twoIndependent`: the converse, in a field.
* `QuadraticIterates.tfae_forall_nonempty_mulEquiv`: for `a ∈ ℚ`, the Galois groups `Ω_n` of the
  iterates of `X² + a` satisfy `Ω_n ≅ [C₂]ⁿ` for all `n` iff `(c_n)_{n ≥ 1}` is 2-independent iff
  `a` has `φ_n` for every `n ≥ 1`.
* `QuadraticIterates.forall_nonempty_mulEquiv_of_forall_exists_mulChar`: `φ₀` and `φ₁` (the
  patterns `-1` and `Pi.mulSingle 1 (-1)`) and, for every `n ≥ 2`, a character that changes sign
  after `c_n` give `Ω_n ≅ [C₂]ⁿ` for all `n`.
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

/-- The converse of `QuadraticIterates.twoIndependent_of_forall_hasCharPattern`: if `v 1, v 2, …`
are 2-independent, then for every `n ≥ 1` some character is `-1` at `v n` and `1` at all later
terms. The class of `v n` lies outside the span of the classes of the later terms, and a linear
form separating it gives the character (`QuadraticIterates.mulCharOfDual`). -/
theorem hasCharPattern_of_twoIndependent {K : Type*} [Field K] {v : ℕ → K}
    (h : TwoIndependent fun m ↦ v (m + 1)) {n : ℕ} (hn : 1 ≤ n) :
    HasCharPattern v n (Pi.mulSingle n (-1)) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨f, hf, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (((twoIndependent_iff_linearIndependent _).mp h).notMem_span_image
      (s := {m | k < m}) (x := k) (by simp)) inferInstance
  refine ⟨mulCharOfDual f, fun m hm ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (hn.trans hm)
  rw [mulCharOfDual_apply f (h.ne_zero j)]
  rcases hm.eq_or_lt with hm | hm
  · obtain rfl : k = j := by lia
    simp [hf]
  · have hj : f (sqClass (v (j + 1))) = 0 :=
      LinearMap.le_ker_iff_map.mpr hfV (Submodule.subset_span ⟨j, (by lia : k < j), rfl⟩)
    simp [hj, Pi.mulSingle_eq_of_ne hm.ne']

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

/-- If `a ∈ ℚ` has `φ₀` and `φ₁` (the patterns `-1` and `Pi.mulSingle 1 (-1)` along `c_n` from
`1` on), and for every `n ≥ 2` some character `ψ` with `ψ(c_n) ≠ 0` takes the value `-ψ(c_n)` at
all later terms, then the Galois groups `Ω_n` of the iterates of `X² + a` satisfy
`Ω_n ≅ [C₂]ⁿ` for all `n`: `ψ` or `φ₀ ψ` is `-1` at `c_n` and `1` at all later terms
(`QuadraticIterates.hasCharPattern_mulSingle_of_neg_of_forall_lt`). -/
theorem forall_nonempty_mulEquiv_of_forall_exists_mulChar {a : ℚ}
    (h₀ : HasCharPattern (cSeq a) 1 (-1)) (h₁ : HasCharPattern (cSeq a) 1 (Pi.mulSingle 1 (-1)))
    (h : ∀ n ≥ 2, ∃ ψ : MulChar ℚ ℤ, ψ (cSeq a n) ≠ 0 ∧ ∀ m > n, ψ (cSeq a m) = -ψ (cSeq a n))
    (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  refine forall_nonempty_mulEquiv_of_hasCharPattern_of_forall_hasCharPattern h₁ (fun n hn ↦ ?_) n
  obtain ⟨ψ, hψ, hψn⟩ := h n hn
  exact hasCharPattern_mulSingle_of_neg_of_forall_lt (h₀.mono (by lia)) hψ hψn

end QuadraticIterates
