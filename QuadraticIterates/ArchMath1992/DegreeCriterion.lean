/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates
public import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup

import QuadraticIterates.ArchMath1992.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Polynomial.Roots
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The degree criterion `[K_{n+1} : K_n] = 2^{2^n}`

For a rational parameter `a`, `K_{n+1}` is generated over `K_n` by square roots of the shifted
roots `β - a` of `f_n`, so `[K_{n+1} : K_n] = 2^{2^n - d}` with `d` the `𝔽₂`-dimension of the
space of multiplicative relations among them. When `f_n` is irreducible and `c_{n+1} ≠ 0`, that
space vanishes exactly when `c_{n+1} = ∏_β (β - a)` is not a square in `K_n` (Lemma 1.6), and
when `Ω_n ≅ [C₂]ⁿ` the rationals that are squares in `K_n` are determined by `c_1, …, c_n`
(Lemma 1.5).

## Main definitions

* `rootShift a n β`: the shifted root `β - a` of `f_n`, as an element of `K_n`.

## Main statements

* `QuadraticIterates.relfinrank_succ_eq_pow`:
  `[K_{n+1} : K_n] = 2^{2^n - dim rootRelations (rootShift a n)}`.
* `QuadraticIterates.prod_rootShift_eq_cSeq`, `QuadraticIterates.isSquare_algebraMap_cSeq`: the norm
  identity `∏_β (β - a) = c_{n+1}` in `K_n`; hence `c_1, …, c_n` are squares in `K_n`.
* `QuadraticIterates.relfinrank_succ_eq_two_pow_iff` (Lemma 1.6): for irreducible `f_n` and
  `c_{n+1} ≠ 0`, `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}` is not a square in `K_n`, through
  `QuadraticIterates.rootRelations_rootShift_eq_bot_iff`.
* `QuadraticIterates.not_isSquare_algebraMap_iff_twoIndependent_snoc` (Lemma 1.5): if `Ω_n ≅ [C₂]ⁿ`
  and `c_1, …, c_n` are 2-independent, a rational `c` is a non-square in `K_n` iff `c_1, …, c_n, c`
  are 2-independent.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℚ)

/-! ### The shifted roots `β - a` and their relation space -/

/-- The shifted root `β - a` of `f_n`, as an element of `K_n`: these are the radicands whose
square roots generate `K_{n+1}` over `K_n`. -/
noncomputable def rootShift (n : ℕ) (β : fℚ[a, n].rootSet (AlgebraicClosure ℚ)) :
    ↥(splittingField a n) :=
  ⟨(β : AlgebraicClosure ℚ) - a,
    sub_mem (IntermediateField.subset_adjoin ℚ _ β.2) (SubfieldClass.ratCast_mem _ a)⟩

@[simp] lemma coe_rootShift (n : ℕ) (β : fℚ[a, n].rootSet (AlgebraicClosure ℚ)) :
    (rootShift a n β : AlgebraicClosure ℚ) = (β : AlgebraicClosure ℚ) - a := rfl

variable {a}

/-- The shifted roots are nonzero when `c_{n+1} = ± f_n(a) ≠ 0`. -/
lemma rootShift_ne_zero {n : ℕ} (hc : cSeq a (n + 1) ≠ 0)
    (β : fℚ[a, n].rootSet (AlgebraicClosure ℚ)) : rootShift a n β ≠ 0 :=
  fun h ↦ sub_ratCast_ne_zero_of_mem_rootSet hc β.2 (congrArg Subtype.val h)

/-- For irreducible `f_n` with `c_{n+1} ≠ 0`, the relative degree `[K_{n+1} : K_n]` equals
`2 ^ (2^n - d)`, where `d` is the `𝔽₂`-dimension of the multiquadratic relations among the shifted
roots `β - a` of `f_n`. -/
theorem relfinrank_succ_eq_pow [DecidableEq (AlgebraicClosure ℚ)] {n : ℕ}
    (hirr : Irreducible fℚ[a, n]) (hc : cSeq a (n + 1) ≠ 0) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = 2 ^ (2 ^ n - Module.finrank (ZMod 2) (rootRelations (rootShift a n))) := by
  choose g hg using exists_sq_eq_sub a
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg, Set.image_eq_range,
    finrank_adjoin_range_eq_two_pow_sub (r := rootShift a n) (hg ·) (rootShift_ne_zero hc),
    card_rootSet_iteratedPoly hirr]

/-- Every element of `Ω_n` acts on the shifted roots `β - a ∈ K_n` through a ring automorphism of
`K_n`: the restriction of any extension of it to `ℚ̄`. -/
lemma exists_ringEquiv_rootShift_smul (n : ℕ) (σ : GaloisGroup a n) :
    ∃ φ : ↥(splittingField a n) ≃+* ↥(splittingField a n),
      ∀ β, φ (rootShift a n β) = rootShift a n (σ • β) := by
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective fℚ[a, n] (AlgebraicClosure ℚ) σ
  refine ⟨(ϕ.restrictNormal (splittingField a n)).toRingEquiv, fun β ↦ Subtype.ext ?_⟩
  simp [AlgEquiv.restrictNormal_apply]

/-! ### The norm identity `∏ (β - a) = c_{n+1}` -/

variable (a) in
/-- The norm identity `∏ (α - a) = c_{n+1}` over the roots `α` of `f_n` (with multiplicity), by
evaluating the monic split `f_n` at `a`. -/
lemma prod_aroots_sub_eq_cSeq (n : ℕ) :
    ((fℚ[a, n].aroots (AlgebraicClosure ℚ)).map (· - (a : AlgebraicClosure ℚ))).prod
      = ((cSeq a (n + 1) : ℚ) : AlgebraicClosure ℚ) := by
  have hcard : (fℚ[a, n].aroots (AlgebraicClosure ℚ)).card = 2 ^ n :=
    IsAlgClosed.card_aroots_eq_natDegree.trans (natDegree_iteratedPoly _ n)
  rw [cSeq_succ_eq_neg_one_pow_mul_eval, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    ← aeval_ratCast_iteratedPoly,
    (IsAlgClosed.splits _).aeval_eq_prod_aroots_of_monic (monic_iteratedPoly _ n),
    ← hcard, ← Multiset.card_map ((a : AlgebraicClosure ℚ) - ·), ← Multiset.prod_map_neg]
  simp

/-- The norm identity over the root set: `∏_β (β - a) = c_{n+1}` for the `2^n` distinct roots `β`
of an irreducible `f_n` in `ℚ̄`. -/
lemma prod_rootSet_sub_eq_cSeq {n : ℕ} (hirr : Irreducible fℚ[a, n]) :
    ∏ β : fℚ[a, n].rootSet (AlgebraicClosure ℚ), ((β : AlgebraicClosure ℚ) - a)
      = ((cSeq a (n + 1) : ℚ) : AlgebraicClosure ℚ) :=
  (prod_rootSet_eq_prod_aroots (nodup_roots hirr.separable.map)
    (· - (a : AlgebraicClosure ℚ))).trans (prod_aroots_sub_eq_cSeq a n)

lemma prod_rootShift_eq_cSeq {n : ℕ} (hirr : Irreducible fℚ[a, n]) :
    ∏ β, rootShift a n β = algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1)) := by
  refine (algebraMap ↥(splittingField a n) (AlgebraicClosure ℚ)).injective ?_
  simpa using prod_rootSet_sub_eq_cSeq hirr

/-- `c_1, …, c_n` are squares in `K_n`: `c_{k+1} = ∏_β (β - a)` over the roots `β` of `f_k` with
multiplicity, and each `β - a` is the square of a root of `f_{k+1}`, which lies in
`K_{k+1} ⊆ K_n`. -/
lemma isSquare_algebraMap_cSeq {k n : ℕ} (hkn : k < n) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (k + 1))) := by
  choose g hg using exists_sq_eq_sub a
  refine (IntermediateField.isSquare_algebraMap_iff _ _).mpr
    ⟨((fℚ[a, k].aroots (AlgebraicClosure ℚ)).map g).prod, multiset_prod_mem _ fun x hx ↦ ?_, ?_⟩
  · obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
    exact splittingField_mono a hkn (IntermediateField.subset_adjoin ℚ _
      (mem_rootSet_succ_of_sq_eq_sub a (mem_rootSet.mpr (mem_aroots.mp hβ)) (hg β)))
  · rw [← Multiset.prod_map_pow, Multiset.map_congr rfl fun β _ ↦ hg β, prod_aroots_sub_eq_cSeq,
      eq_ratCast]

/-! ### Lemma 1.6: the degree criterion -/

/-- For irreducible `f_n` with `c_{n+1} ≠ 0`, the relation space of the shifted roots vanishes iff
`c_{n+1}` is not a square in `K_n`: if it is nonzero, it contains the all-ones vector, `Ω_n` being
a 2-group acting transitively on the roots (`one_mem_rootRelations_of_ne_bot`), and the all-ones
vector is a relation iff `∏_β (β - a) = c_{n+1}` is a square. -/
lemma rootRelations_rootShift_eq_bot_iff [DecidableEq (AlgebraicClosure ℚ)] {n : ℕ}
    (hirr : Irreducible fℚ[a, n]) (hc : cSeq a (n + 1) ≠ 0) :
    rootRelations (rootShift a n) = ⊥ ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1))) := by
  have hrne := rootShift_ne_zero hc
  have : Nonempty ↥(fℚ[a, n].rootSet (AlgebraicClosure ℚ)) :=
    Fintype.card_pos_iff.mp (card_rootSet_iteratedPoly hirr ▸ Nat.two_pow_pos n)
  have := Gal.galAction_isPretransitive fℚ[a, n] (AlgebraicClosure ℚ) hirr
  rw [← prod_rootShift_eq_cSeq hirr, ← one_mem_rootRelations_iff hrne, ← not_iff_not, not_not]
  refine ⟨one_mem_rootRelations_of_ne_bot (isPGroup_galoisGroup a n) hrne
    (exists_ringEquiv_rootShift_smul n), fun hmem hbot ↦ one_ne_zero (α := ZMod 2) ?_⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact congrFun hmem (Classical.arbitrary _)

/-- Lemma 1.6: for irreducible `f_n` with `c_{n+1} ≠ 0` (as when `f_{n+1}` is irreducible,
`QuadraticIterates.cSeq_succ_ne_zero_of_irreducible`), `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}` is
not a square in `K_n`, by `QuadraticIterates.relfinrank_succ_eq_pow` and
`QuadraticIterates.rootRelations_rootShift_eq_bot_iff`. -/
theorem relfinrank_succ_eq_two_pow_iff {n : ℕ} (hirr : Irreducible fℚ[a, n])
    (hc : cSeq a (n + 1) ≠ 0) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1))) := by
  classical
  rw [← rootRelations_rootShift_eq_bot_iff hirr hc, ← Submodule.finrank_eq_zero,
    relfinrank_succ_eq_pow hirr hc, Nat.pow_right_inj one_lt_two]
  have := (finrank_rootRelations_le (rootShift a n)).trans_eq (card_rootSet_iteratedPoly hirr)
  lia

/-! ### Lemma 1.5: the Kummer extension criterion -/

/-- If `Ω_n ≅ [C₂]ⁿ`, then `Gal(K_n/ℚ)` has exactly `2^n` characters to `C₂`
(`IteratedWreathProduct.card_monoidHom_multiplicative_zmod_two`), which bounds the degree of the
subfields of `K_n` generated by square roots of rationals. -/
lemma card_monoidHom_eq_two_pow {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Nat.card ((↥(splittingField a n) ≃ₐ[ℚ] ↥(splittingField a n)) →* Multiplicative (ZMod 2))
      = 2 ^ n :=
  (Nat.card_congr ((AlgEquiv.autCongr (IsSplittingField.algEquiv _ fℚ[a, n])).trans
    hiso.some).monoidHomCongrLeftEquiv).trans
    (IteratedWreathProduct.card_monoidHom_multiplicative_zmod_two n)

/-- If `Ω_n ≅ [C₂]ⁿ` and the `c_i` are 2-independent with square roots `x i` in `K_n`, then the
image of `c : ℚ` in `K_n` is a square iff it is the square of some
`z ∈ IntermediateField.adjoin ℚ (Set.range x)`: that field has the maximal degree `2^n` of a
subfield of `K_n` generated by square roots of rationals. -/
theorem isSquare_algebraMap_iff_exists_sq_eq {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)))
    {x : Fin n → ↥(splittingField a n)}
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1))) (c : ℚ) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ z ∈ IntermediateField.adjoin ℚ (Set.range x),
        z ^ 2 = algebraMap ℚ ↥(splittingField a n) c := by
  refine ⟨fun hsq ↦ ?_, fun ⟨z, _, hz⟩ ↦ hz ▸ IsSquare.sq z⟩
  obtain ⟨w, hw⟩ := hsq.exists_sq
  exact ⟨w, IntermediateField.mem_adjoin_of_sq_eq_algebraMap_of_card_le
    (Set.forall_mem_range.mpr fun i ↦ ⟨_, hx i⟩) ((card_monoidHom_eq_two_pow hiso).trans
      (by rw [hindep.finrank_adjoin_range_eq_two_pow hx, Fintype.card_fin])).le hw.symm, hw.symm⟩

/-- If `Ω_n ≅ [C₂]ⁿ` and `c_1, …, c_n` are 2-independent, then a rational `c` is a square in `K_n`
iff `c` times a subproduct of `c_1, …, c_n` is a rational square: the `√c_i` generate the maximal
subfield of `K_n` generated by square roots of rationals, and squares descend along it
(`IntermediateField.exists_mem_adjoin_sq_eq_algebraMap_iff`). -/
lemma isSquare_algebraMap_iff_exists_mul_prod {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1))) (c : ℚ) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ S : Finset (Fin n), IsSquare (c * ∏ i ∈ S, cSeq a ((i : ℕ) + 1)) := by
  choose x hx using fun i : Fin n ↦ (isSquare_algebraMap_cSeq i.2).exists_sq
  rw [isSquare_algebraMap_iff_exists_sq_eq hiso hindep (fun i ↦ (hx i).symm) c,
    ← Set.image_univ, ← Finset.coe_univ,
    IntermediateField.exists_mem_adjoin_sq_eq_algebraMap_iff (fun i _ ↦ (hx i).symm)
      (fun i _ ↦ hindep.ne_zero i) c]
  exact exists_congr fun S ↦ and_iff_right (Finset.subset_univ S)

/-- Lemma 1.5: if `Ω_n ≅ [C₂]ⁿ` and `c_1, …, c_n` are 2-independent, then `c ∈ ℚ` is a
non-square in `K_n` iff `c_1, …, c_n, c` are 2-independent (for `c = 0` both sides fail). -/
theorem not_isSquare_algebraMap_iff_twoIndependent_snoc {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1))) {c : ℚ} :
    ¬IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      TwoIndependent (Fin.snoc (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)) c) := by
  rw [twoIndependent_snoc_iff, and_iff_right hindep,
    isSquare_algebraMap_iff_exists_mul_prod hiso hindep c, not_exists]

end

end QuadraticIterates

end
