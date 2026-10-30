/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Divisors
public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Galois.TwoIndependent

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
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
* `QuadraticIterates.hasCharPattern_one_iff_forall_isSquare`: in a field, a sign pattern is realized
  iff it multiplies to `1` along every square product.
* `QuadraticIterates.hasCharPattern_one_iff_of_prod_divisors`,
  `QuadraticIterates.twoIndependent_iff_of_prod_divisors`: patterns and 2-independence transfer
  along `v n = ∏_{d ∣ n} u d` by Möbius inversion.
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

/-- For signs `ε n = ±1`, the product of the `ε n` over `S` is `1` iff the number of `n ∈ S` with
`ε n = -1` is even, i.e. iff the corresponding sum in `ZMod 2` vanishes. -/
private lemma prod_eq_one_iff_sum_eq_zero {S : Finset ℕ} {ε : ℕ → ℤ}
    (hε : ∀ n ∈ S, ε n = 1 ∨ ε n = -1) :
    ∏ n ∈ S, ε n = 1 ↔ ∑ n ∈ S, (if ε n = 1 then 0 else 1 : ZMod 2) = 0 := by
  rw [Finset.prod_congr rfl fun n hn ↦ show ε n = if ε n = 1 then 1 else -1 by
    rcases hε n hn with h | h <;> simp [h]]
  simp [Finset.prod_ite, Finset.sum_ite, ZMod.natCast_eq_zero_iff_even,
    neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)]

/-- The linear form on square classes behind
`QuadraticIterates.hasCharPattern_one_iff_forall_isSquare`: the values `0` at `[v n]` for
`ε n = 1` and `1` for `ε n = -1` respect all relations among the `[v n]`, which are the square
products. -/
private lemma exists_dual_of_forall_isSquare {K : Type*} [Field K] [DecidableEq K] {v : ℕ → K}
    (hv : ∀ n ≥ 1, v n ≠ 0) {ε : ℕ → ℤ} (hε : ∀ n ≥ 1, ε n = 1 ∨ ε n = -1)
    (h : ∀ S : Finset ℕ, 0 ∉ S → IsSquare (∏ n ∈ S, v n) → ∏ n ∈ S, ε n = 1) :
    ∃ f : Module.Dual (ZMod 2) (SquareClasses K),
      ∀ n, f (sqClass (v (n + 1))) = if ε (n + 1) = 1 then 0 else 1 := by
  refine (Module.exists_dual_forall_apply_eq_iff _ _).mpr fun c hc ↦ ?_
  have h1 {n : ℕ} (hn : n ∈ c.support) : c n = 1 :=
    (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ (Finsupp.mem_support_iff.mp hn)
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_congr rfl fun n hn ↦ by rw [h1 hn, one_smul]] at hc ⊢
  have := h (c.support.map (addRightEmbedding 1)) (by simp) <| by
    rw [Finset.prod_map]
    exact (isSquare_prod_iff_sum_sqClass_eq_zero fun n _ ↦ hv _ le_add_self).mpr hc
  rw [Finset.prod_map] at this
  exact (prod_eq_one_iff_sum_eq_zero fun n _ ↦ hε _ le_add_self).mp this

/-- **Duality**: in a field, a sequence of nonzero terms realizes a sign pattern from `1` on iff
the pattern multiplies to `1` along every finite set of indices with a square product. -/
theorem hasCharPattern_one_iff_forall_isSquare {K : Type*} [Field K] {v : ℕ → K}
    (hv : ∀ n ≥ 1, v n ≠ 0) {ε : ℕ → ℤ} (hε : ∀ n ≥ 1, ε n = 1 ∨ ε n = -1) :
    HasCharPattern v 1 ε ↔
      ∀ S : Finset ℕ, 0 ∉ S → IsSquare (∏ n ∈ S, v n) → ∏ n ∈ S, ε n = 1 := by
  classical
  refine ⟨fun h S hS hsq ↦ h.prod_eq_one_of_isSquare hε
    (fun n hn ↦ Nat.one_le_iff_ne_zero.mpr fun h ↦ hS (h ▸ hn)) hsq, fun h ↦ ?_⟩
  obtain ⟨f, hf⟩ := exists_dual_of_forall_isSquare hv hε h
  refine ⟨mulCharOfDual f, fun m hm ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [mulCharOfDual_apply f (hv _ hm), hf j]
  rcases hε (j + 1) hm with h1 | h1 <;> simp [h1]

open scoped ArithmeticFunction.Moebius in
/-- **Möbius transfer of patterns**: if `v n = ∏_{d ∣ n} u d` and `ε n = ∏_{d ∣ n} β d`, then
`v` realizes `ε` iff `u` realizes `β` (both from `1` on), by the uniqueness of Möbius inversion
for the values `χ (u d) = ±1`. -/
theorem hasCharPattern_one_iff_of_prod_divisors {K : Type*} [Field K] {u v : ℕ → K}
    (hu : ∀ n ≥ 1, u n ≠ 0) (huv : ∀ n ≥ 1, ∏ d ∈ n.divisors, u d = v n) {β ε : ℕ → ℤ}
    (hβ : ∀ n ≥ 1, β n = 1 ∨ β n = -1) (hβε : ∀ n ≥ 1, ∏ d ∈ n.divisors, β d = ε n) :
    HasCharPattern v 1 ε ↔ HasCharPattern u 1 β := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ, fun n hn ↦ ?_⟩, fun ⟨χ, hχ⟩ ↦ ⟨χ, fun n hn ↦ ?_⟩⟩
  · have hε (n : ℕ) (hn : 0 < n) : (ε n : ℚ) ≠ 0 := by
      rw [← hβε n hn, Int.cast_prod]
      exact Finset.prod_ne_zero_iff.mpr fun d hd ↦ by
        rcases hβ d (Nat.pos_of_mem_divisors hd) with h | h <;> simp [h]
    have key (F : ℕ → ℤ) (hF : ∀ n > 0, F n ≠ 0) (hFε : ∀ n > 0, ∏ d ∈ n.divisors, F d = ε n) :
        (F n : ℚ) = ∏ x ∈ n.divisorsAntidiagonal, (ε x.2 : ℚ) ^ μ x.1 :=
      ((ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
        (fun n hn ↦ Int.cast_ne_zero.mpr (hF n hn)) hε).mp
        (fun n hn ↦ by rw [← Int.cast_prod, hFε n hn]) n hn).symm
    refine Int.cast_injective (α := ℚ) <|
      (key (fun d ↦ χ (u d)) (fun d hd ↦ ?_) fun d hd ↦ ?_).trans
        (key β (fun d hd ↦ by rcases hβ d hd with h | h <;> simp [h]) hβε).symm
    · rcases χ.apply_eq_one_or_eq_neg_one (hu d hd).isUnit with h | h <;> simp [h]
    · rw [← map_prod, huv d hd, hχ d hd]
  · rw [← huv n hn, map_prod, Finset.prod_congr rfl fun d hd ↦ hχ d (Nat.pos_of_mem_divisors hd),
      hβε n hn]

open scoped ArithmeticFunction.Moebius in
/-- Every sign pattern `ε` is the divisor product `ε n = ∏_{d ∣ n} β d` of a sign pattern `β`,
its Möbius transform in `ℤˣ`. -/
private lemma exists_prod_divisors_eq {ε : ℕ → ℤ} (hε : ∀ n ≥ 1, ε n = 1 ∨ ε n = -1) :
    ∃ β : ℕ → ℤ, (∀ n ≥ 1, β n = 1 ∨ β n = -1) ∧ ∀ n ≥ 1, ∏ d ∈ n.divisors, β d = ε n := by
  let e : ℕ → ℤˣ := fun n ↦ if ε n = 1 then 1 else -1
  let b : ℕ → ℤˣ := fun n ↦ ∏ x ∈ n.divisorsAntidiagonal, e x.2 ^ μ x.1
  have h := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq (f := b) (g := e)).mpr
    fun _ _ ↦ rfl
  refine ⟨fun n ↦ b n, fun n _ ↦ (Int.units_eq_one_or (b n)).imp (fun h ↦ by simp [h])
    fun h ↦ by simp [h], fun n hn ↦ ?_⟩
  rw [← Units.coe_prod, h n hn]
  rcases hε n hn with h1 | h1 <;> simp [e, h1]

/-- **Möbius transfer of 2-independence**: if `v n = ∏_{d ∣ n} u d`, then `v 1, v 2, …` are
2-independent iff `u 1, u 2, …` are. Both say that every sign pattern is realized from `1` on,
and patterns transfer (`QuadraticIterates.hasCharPattern_one_iff_of_prod_divisors`). -/
theorem twoIndependent_iff_of_prod_divisors {K : Type*} [Field K] {u v : ℕ → K}
    (hu : ∀ n ≥ 1, u n ≠ 0) (huv : ∀ n ≥ 1, ∏ d ∈ n.divisors, u d = v n) :
    TwoIndependent (fun n ↦ v (n + 1)) ↔ TwoIndependent (fun n ↦ u (n + 1)) := by
  have key (w : ℕ → K) : TwoIndependent (fun n ↦ w (n + 1)) ↔
      ∀ ε : ℕ → ℤ, (∀ n ≥ 1, ε n = 1 ∨ ε n = -1) → HasCharPattern w 1 ε :=
    ⟨fun h _ hε ↦ hasCharPattern_one_of_twoIndependent h hε, fun h ↦
      twoIndependent_of_forall_hasCharPattern fun n hn ↦ (h _ fun m _ ↦ by
        rcases eq_or_ne m n with rfl | hm <;> simp [*]).mono hn⟩
  rw [key, key]
  refine ⟨fun h β hβ ↦ (hasCharPattern_one_iff_of_prod_divisors hu huv hβ fun _ _ ↦ rfl).mp
    (h _ fun n _ ↦ Finset.prod_induction _ (fun x ↦ x = 1 ∨ x = -1) (fun x y hx hy ↦ ?_) (.inl rfl)
      fun d hd ↦ hβ d (Nat.pos_of_mem_divisors hd)), fun h ε hε ↦ ?_⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  · obtain ⟨β, hβ, hβε⟩ := exists_prod_divisors_eq hε
    exact (hasCharPattern_one_iff_of_prod_divisors hu huv hβ hβε).mpr (h β hβ)

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
