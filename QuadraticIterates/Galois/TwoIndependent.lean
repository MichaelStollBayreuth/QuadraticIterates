/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Mathlib.FieldTheory.Multiquadratic

import QuadraticIterates.Mathlib.Data.Fintype.Basic

/-!
# 2-independent families

A family in a commutative monoid is *2-independent* if no product of finitely many, but at least
one, of its members is a square. For a family of nonzero elements of a field `L` this says that
their classes in the `𝔽₂`-vector space `Lˣ/(Lˣ)²` are linearly independent.

## Main definitions

* `QuadraticIterates.TwoIndependent v`: no nonempty finite subfamily of `v` has a square product.

## Main statements

* `QuadraticIterates.twoIndependent_iff_linearIndependent`: for a family in a field,
  2-independence is linear independence of the square classes.
* `QuadraticIterates.twoIndependent_snoc_iff`: when a family extended by one member is
  2-independent.
* `QuadraticIterates.twoIndependent_iff_forall_fin`: a sequence is 2-independent iff all its
  initial segments are.
-/

@[expose] public section

namespace QuadraticIterates

section TwoIndependent

variable {ι M : Type*}

/-- A family of elements of a commutative monoid is *2-independent* if no nonempty subfamily has
a square product. For nonzero rationals this says that the classes in `ℚ*/(ℚ*)²` are
`𝔽₂`-linearly independent (`QuadraticIterates.twoIndependent_iff_linearIndependent`). -/
def TwoIndependent [CommMonoid M] (v : ι → M) : Prop :=
  ∀ S : Finset ι, S.Nonempty → ¬IsSquare (∏ i ∈ S, v i)

/-- No member of a 2-independent family is a square (the singleton subfamilies). -/
lemma TwoIndependent.not_isSquare [CommMonoid M] {v : ι → M} (h : TwoIndependent v) (i : ι) :
    ¬IsSquare (v i) := by
  simpa using h {i} (Finset.singleton_nonempty i)

/-- The members of a 2-independent family are nonzero, `0` being a square. -/
lemma TwoIndependent.ne_zero [CommMonoidWithZero M] {v : ι → M} (h : TwoIndependent v) (i : ι) :
    v i ≠ 0 :=
  fun hi ↦ h.not_isSquare i (hi ▸ IsSquare.zero)

/-- A 2-independent family stays 2-independent along an injective reindexing. -/
theorem TwoIndependent.comp [CommMonoid M] {κ : Type*} {v : ι → M} (h : TwoIndependent v)
    (f : κ → ι) (hf : Function.Injective f) : TwoIndependent (v ∘ f) := fun S hS ↦ by
  simpa using h (S.map ⟨f, hf⟩) hS.map

/-- A sequence is 2-independent iff all its initial segments are: a finite set of indices lies in
some `{0, …, n - 1}`. -/
theorem twoIndependent_iff_forall_fin [CommMonoid M] {v : ℕ → M} :
    TwoIndependent v ↔ ∀ n, TwoIndependent fun i : Fin n ↦ v i := by
  refine ⟨fun h n ↦ h.comp _ Fin.val_injective, fun h S hS ↦ ?_⟩
  obtain ⟨n, hn⟩ := S.exists_nat_subset_range
  have hlt (m : ℕ) (hm : m ∈ S) : m < n := Finset.mem_range.mp (hn hm)
  have hprod := Finset.prod_map (S.attachFin hlt) Fin.valEmbedding v
  rw [Finset.map_valEmbedding_attachFin] at hprod
  simpa [hprod] using
    h n (S.attachFin hlt) (Finset.map_nonempty.mp (by rwa [Finset.map_valEmbedding_attachFin]))

theorem twoIndependent_fin_two_iff [CommMonoid M] {v : Fin 2 → M} :
    TwoIndependent v ↔ ¬IsSquare (v 0) ∧ ¬IsSquare (v 1) ∧ ¬IsSquare (v 0 * v 1) := by
  refine ⟨fun h ↦ ⟨h.not_isSquare 0, h.not_isSquare 1, by
    simpa [Fin.prod_univ_two] using h Finset.univ Finset.univ_nonempty⟩,
    fun ⟨h₀, h₁, h₀₁⟩ S hS ↦ ?_⟩
  rcases (by revert S; decide : ∀ S : Finset (Fin 2), S.Nonempty → S = {0} ∨ S = {1} ∨
    S = Finset.univ) S hS with rfl | rfl | rfl
  · simpa using h₀
  · simpa using h₁
  · simpa [Fin.prod_univ_two] using h₀₁

theorem TwoIndependent.of_snoc [CommMonoid M] {n : ℕ} {v : Fin n → M} {c : M}
    (h : TwoIndependent (Fin.snoc v c)) :
    TwoIndependent v := fun S hS ↦ by
  simpa [Fin.snoc_castSucc, Finset.prod_map S Fin.castSuccEmb (Fin.snoc v c)] using
    h (S.map Fin.castSuccEmb) hS.map

theorem twoIndependent_snoc_iff [CommMonoid M] {n : ℕ} (v : Fin n → M) (c : M) :
    TwoIndependent (Fin.snoc v c) ↔
      TwoIndependent v ∧ ∀ S : Finset (Fin n), ¬IsSquare (c * ∏ i ∈ S, v i) := by
  have hprod (S : Finset (Fin n)) :
      ∏ i ∈ S.map Fin.castSuccEmb, Fin.snoc v c i = ∏ i ∈ S, v i := by
    simp [Fin.snoc_castSucc]
  refine ⟨fun h ↦ ⟨h.of_snoc, fun S ↦ ?_⟩, fun ⟨hv, hc⟩ T hT ↦ ?_⟩
  · simpa [Finset.prod_insert, hprod S, Fin.snoc_last] using
      h (insert (Fin.last n) (S.map Fin.castSuccEmb)) (Finset.insert_nonempty _ _)
  · obtain ⟨S, rfl | rfl⟩ := Fin.exists_eq_map_castSuccEmb_or_insert_last T
    · exact hprod S ▸ hv S (Finset.map_nonempty.mp hT)
    · simpa [Finset.prod_insert, Fin.snoc_last, hprod] using hc S

private theorem twoIndependent_iff_linearIndependent_of_finite [Finite ι] {L : Type*} [Field L]
    [DecidableEq L] (v : ι → L) :
    TwoIndependent v ↔ LinearIndependent (ZMod 2) fun i ↦ sqClass (v i) := by
  have := Fintype.ofFinite ι
  refine ⟨fun h ↦ (rootRelations_eq_bot_iff v).mp ((Submodule.eq_bot_iff _).mpr fun ε hε ↦ ?_),
    fun H S hS hsq ↦ ?_⟩
  · by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact h {j | ε j = 1} ⟨i, by simpa using (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hi⟩
      ((mem_rootRelations h.ne_zero).mp hε)
  · classical
    have hv0 (i : ι) : v i ≠ 0 := fun hvi ↦ H.ne_zero i (by rw [hvi, sqClass_zero])
    have hmem : (fun j ↦ if j ∈ S then (1 : ZMod 2) else 0) ∈ rootRelations v :=
      (mem_rootRelations hv0).mpr (by simpa using hsq)
    obtain ⟨i, hiS⟩ := hS
    have h0 := (Submodule.mem_bot (ZMod 2)).mp (((rootRelations_eq_bot_iff v).mpr H).le hmem)
    simpa [hiS] using congrFun h0 i

/-- A family is 2-independent iff all its finite subfamilies are. -/
theorem twoIndependent_iff_forall_finset [CommMonoid M] {v : ι → M} :
    TwoIndependent v ↔ ∀ s : Finset ι, TwoIndependent fun i : s ↦ v i := by
  refine ⟨fun h s ↦ h.comp _ Subtype.val_injective, fun h S hS ↦ ?_⟩
  simpa [Finset.prod_attach] using h S Finset.univ (by simpa using hS)

/-- A family in a field `L` is 2-independent iff the family of its classes in `Lˣ/(Lˣ)²` is
`𝔽₂`-linearly independent. -/
theorem twoIndependent_iff_linearIndependent {L : Type*} [Field L] [DecidableEq L] (v : ι → L) :
    TwoIndependent v ↔ LinearIndependent (ZMod 2) fun i ↦ sqClass (v i) := by
  rw [twoIndependent_iff_forall_finset, linearIndependent_iff_finset_linearIndependent]
  exact congr(∀ s, $(twoIndependent_iff_linearIndependent_of_finite _))

/-- Square roots of a 2-independent family of radicands `r : ι → L` generate an extension of the
full degree `2^|ι|`: there are no relations in `finrank_adjoin_range_eq_two_pow_sub`. -/
theorem TwoIndependent.finrank_adjoin_range_eq_two_pow [Fintype ι] {L : Type*} [Field L]
    [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E] {r : ι → L} (hr : TwoIndependent r)
    {x : ι → E} (hx : ∀ i, x i ^ 2 = algebraMap L E (r i)) :
    Module.finrank L (IntermediateField.adjoin L (Set.range x)) = 2 ^ Fintype.card ι := by
  classical
  rw [finrank_adjoin_range_eq_two_pow_sub hx hr.ne_zero, (rootRelations_eq_bot_iff _).mpr
    ((twoIndependent_iff_linearIndependent _).mp hr), finrank_bot, Nat.sub_zero]

end TwoIndependent

end QuadraticIterates
