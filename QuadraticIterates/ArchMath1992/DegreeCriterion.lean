/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates
public import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup

import Mathlib.Data.FunLike.Fintype
import Mathlib.Data.Rat.Sqrt
import QuadraticIterates.ArchMath1992.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Polynomial.Roots
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The relative degree `[K_{n+1} : K_n]`

`K_{n+1}` is generated over `K_n` by square roots of the shifted roots `β - a` of `f_n`
(`rootShift`), so its relative degree is `2` to the power of `2^n` minus the dimension of the
`𝔽₂`-space of multiplicative relations among them (`relfinrank_succ_eq_pow`). The relation space is
trivial exactly when `c_{n+1}` is not a square in `K_n`, which is Lemma 1.6 (`degree_criterion`);
Lemma 1.5 (`kummer_extension_criterion`) then says which rationals stay non-squares in `K_n`.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

/-! ### The relative degree `[K_{n+1} : K_n]` -/

/-- The shifted root `β - a` of `f_n`, as an element of `K_n`: these are the radicands whose
square roots generate `K_{n+1}` over `K_n`. -/
noncomputable def rootShift (a : ℤ) (n : ℕ) (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :
    ↥(splittingField a n) :=
  ⟨(β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ),
    sub_mem (IntermediateField.subset_adjoin ℚ _ β.2) (IntermediateField.intCast_mem _ a)⟩

@[simp] lemma coe_rootShift (n : ℕ) (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :
    (rootShift a n β : AlgebraicClosure ℚ)
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := rfl

lemma rootShift_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ}
    (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) : rootShift a n β ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff, coe_rootShift]
  simpa using sub_intCast_ne_zero_of_mem_rootSet a ha β.2

/-- The relative degree `[K_{n+1} : K_n]` equals `2 ^ (2^n - d)`, where `d` is the `𝔽₂`-dimension
of the multiquadratic relations among the shifted roots `β - a` of `f_n`. -/
theorem relfinrank_succ_eq_pow [DecidableEq (AlgebraicClosure ℚ)] (ha : ¬IsSquare (-a : ℚ))
    (n : ℕ) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = 2 ^ (2 ^ n - Module.finrank (ZMod 2) (rootRelations (rootShift a n))) := by
  classical
  choose g hg using exists_sq_eq_sub a
  set x : ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) → AlgebraicClosure ℚ := fun β ↦ g β
  have hx (β) :
      x β ^ 2 = algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (rootShift a n β) :=
    hg β.1
  have hset : g '' ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
      = Set.range x := Set.image_eq_range g _
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg, hset,
    multiquadratic_degree_family hx (rootShift_ne_zero a ha),
    card_rootSet_iteratedPoly a (irreducible_iteratedPoly a ha n)]

/-- Every element of `Ω_n` acts on the shifted roots `β - a ∈ K_n` through a ring automorphism of
`K_n`: the restriction of any extension of it to `ℚ̄`. -/
lemma exists_ringEquiv_rootShift_smul (n : ℕ) (σ : GaloisGroup a n) :
    ∃ φ : ↥(splittingField a n) ≃+* ↥(splittingField a n),
      ∀ β, φ (rootShift a n β) = rootShift a n (σ • β) := by
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective fℚ[a, n] (AlgebraicClosure ℚ) σ
  refine ⟨(ϕ.restrictNormal (splittingField a n)).toRingEquiv, fun β ↦ Subtype.ext ?_⟩
  have hcomm : ((ϕ.restrictNormal (splittingField a n)).toRingEquiv (rootShift a n β) :
      AlgebraicClosure ℚ) = ϕ (rootShift a n β) :=
    AlgEquiv.restrictNormal_commutes ϕ (splittingField a n) (rootShift a n β)
  rw [hcomm, coe_rootShift, coe_rootShift, map_sub, map_intCast, Gal.restrict_smul]

lemma isPretransitive_galoisGroup (n : ℕ) (hirr : Irreducible (fℚ[a, n])) :
    MulAction.IsPretransitive (GaloisGroup a n)
      ↑((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
  Gal.galAction_isPretransitive (fℚ[a, n]) (AlgebraicClosure ℚ) hirr

/-- The norm identity `∏ (α - a) = c_{n+1}` over the roots `α` of `f_n` (with multiplicity), by
evaluating the monic split `f_n` at `a`. -/
lemma prod_aroots_sub_eq_cSeq (n : ℕ) :
    ((fℚ[a, n].aroots (AlgebraicClosure ℚ)).map (· - (a : AlgebraicClosure ℚ))).prod
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
  have hsplits : (fℚ[a, n].map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits :=
    IsAlgClosed.splits _
  have hcard : (fℚ[a, n].aroots (AlgebraicClosure ℚ)).card = 2 ^ n := by
    rw [aroots_def, ← hsplits.natDegree_eq_card_roots, (monic_iteratedPoly _ n).natDegree_map,
      natDegree_iteratedPoly]
  rw [cSeq_succ_eq_neg_one_pow_mul_eval, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ← aeval_intCast_iteratedPoly, hsplits.aeval_eq_prod_aroots_of_monic (monic_iteratedPoly _ n),
    ← hcard, ← Multiset.card_map (fun α ↦ (a : AlgebraicClosure ℚ) - α), ← Multiset.prod_map_neg,
    Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun _ _ ↦ (neg_sub _ _).symm)

/-- The norm identity over the root set: `∏_β (β - a) = c_{n+1}` for the `2^n` distinct roots `β`
of `f_n` in `ℚ̄`. -/
lemma prod_rootSet_sub_eq_cSeq (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    ∏ β : fℚ[a, n].rootSet (AlgebraicClosure ℚ), ((β : AlgebraicClosure ℚ) - a)
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
  rw [prod_rootSet_eq_prod_aroots (nodup_roots (irreducible_iteratedPoly a ha n).separable.map)
    (· - (a : AlgebraicClosure ℚ))]
  exact prod_aroots_sub_eq_cSeq a n

/-- The product of the shifted roots `β - a` of `f_n` is `c_{n+1}`, as elements of `K_n`. -/
lemma prod_rootShift_eq_cSeq (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    ∏ β, rootShift a n β = algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ) := by
  refine (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective ?_
  simpa [map_prod] using prod_rootSet_sub_eq_cSeq a ha n

end

section

variable (a : ℤ)

/-! ### The degree criterion and the Kummer extension criterion -/

/-- Lemma 1.6: `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}` is not a square in `K_n`. The relation
space of the shifted roots is nonzero iff it contains the all-ones vector, `Ω_n` being a 2-group
acting transitively on the roots, and that vector is a relation iff `∏ (β - a) = c_{n+1}` is a
square in `K_n`. -/
theorem degree_criterion (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) := by
  classical
  have hirr := irreducible_iteratedPoly a ha n
  have hrne := rootShift_ne_zero a ha (n := n)
  have hcard := card_rootSet_iteratedPoly a hirr
  have : Nonempty ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have hdle : Module.finrank (ZMod 2) (rootRelations (rootShift a n)) ≤ 2 ^ n := by
    rw [← hcard]
    exact rootRelations_finrank_le _
  have : MulAction.IsPretransitive (GaloisGroup a n)
      ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
    isPretransitive_galoisGroup a n hirr
  have hrfd : (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n
      ↔ Module.finrank (ZMod 2) (rootRelations (rootShift a n)) = 0 := by
    rw [relfinrank_succ_eq_pow a ha n, Nat.pow_right_inj one_lt_two]
    lia
  have hallne : 1 ∈ rootRelations (rootShift a n) ↔ rootRelations (rootShift a n) ≠ ⊥ := by
    refine ⟨fun hmem hbot ↦ one_ne_zero (α := ZMod 2) ?_,
      fun hbot ↦ rootRelations_all_ones (isPGroup_galoisGroup a n) hrne ?_ hbot⟩
    · rw [hbot, Submodule.mem_bot] at hmem
      exact congrFun hmem (Classical.arbitrary _)
    · exact exists_ringEquiv_rootShift_smul a n
  have hallsq : 1 ∈ rootRelations (rootShift a n)
      ↔ IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) :=
    (all_ones_mem_rootRelations hrne).trans
      (by rw [prod_rootShift_eq_cSeq a ha n])
  rw [hrfd, Submodule.finrank_eq_zero, ← not_iff_not]
  simpa using hallne.symm.trans hallsq

lemma finrank_eq_of_nonempty_mulEquiv {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1) := by
  rw [← card_galoisGroup_eq_finrank a n, Nat.card_congr hiso.some.toEquiv, card_wreathPower]

lemma finrank_adjoin_range_eq_two_pow {n : ℕ}
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)))
    {x : Fin n → ↥(splittingField a n)}
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) = 2 ^ n := by
  classical
  rw [multiquadratic_degree_family hx hindep.ne_zero, (rootRelations_eq_bot_iff _).mpr
    ((twoIndependent_iff_linearIndependent _).mp hindep), finrank_bot, Fintype.card_fin,
    Nat.sub_zero]

lemma card_monoidHom_eq_two_pow {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Nat.card (((splittingField a n) ≃ₐ[ℚ] (splittingField a n)) →*
      Multiplicative (ZMod 2)) = 2 ^ n := by
  refine (Nat.card_congr ?_).trans (wreath_max_elem_ab n)
  exact ((AlgEquiv.autCongr (IsSplittingField.algEquiv _ (fℚ[a, n]))).trans
    hiso.some).monoidHomCongrLeftEquiv

lemma finrank_adjoin_le_two_pow {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (t : Finset ↥(splittingField a n))
    (ht : ∀ y ∈ t, ∃ q : ℚ, y ^ 2 = algebraMap ℚ ↥(splittingField a n) q) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (t : Set ↥(splittingField a n))) ≤ 2 ^ n := by
  set M := IntermediateField.adjoin ℚ (t : Set ↥(splittingField a n))
  have hgalM : IsGalois ℚ ↥M := IntermediateField.isGalois_adjoin_of_sq_eq_algebraMap ht
  rw [← IsGalois.card_aut_eq_finrank ℚ ↥M, ← Nat.card_monoidHom_multiplicative_zmod_two
    (IntermediateField.algEquiv_adjoin_sq_eq_one ht)]
  have hfin : Finite ((↥(splittingField a n) ≃ₐ[ℚ] ↥(splittingField a n)) →*
      Multiplicative (ZMod 2)) := DFunLike.finite _
  refine le_trans (Nat.card_le_card_of_injective
    (fun φ ↦ φ.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := splittingField a n) ↥M)) ?_)
    (card_monoidHom_eq_two_pow a hiso).le
  intro φ₁ φ₂ hφ
  ext x
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (splittingField a n) x
  exact DFunLike.congr_fun hφ g

/-- If `Ω_n ≅ [C_2]^n` and the `c_i` are 2-independent with square roots `x i` in `K_n`, then the
image of `c : ℚ` in `K_n` is a square iff it is the square of some
`z ∈ IntermediateField.adjoin ℚ (Set.range x)`. -/
theorem isSquare_algebraMap_iff_exists_sq_eq {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)))
    {x : Fin n → ↥(splittingField a n)}
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ))
    (c : ℚ) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ z ∈ IntermediateField.adjoin ℚ (Set.range x),
        z ^ 2 = algebraMap ℚ ↥(splittingField a n) c := by
  classical
  refine ⟨fun hsq ↦ ?_, fun ⟨z, hzmem, hz2⟩ ↦ (isSquare_iff_exists_sq _).mpr ⟨z, hz2.symm⟩⟩
  obtain ⟨w, hw2⟩ := hsq.exists_sq
  replace hw2 := hw2.symm
  suffices hwM : w ∈ IntermediateField.adjoin ℚ (Set.range x) from ⟨w, hwM, hw2⟩
  by_contra hwnotM
  have hinsdeg : Module.finrank ℚ
      (IntermediateField.adjoin ℚ (insert w (Set.range x))) = 2 ^ (n + 1) := by
    rw [IntermediateField.finrank_adjoin_insert_of_not_isSquare hw2
      (IntermediateField.not_isSquare_algebraMap_of_sqrt_notMem hw2 hwnotM),
      finrank_adjoin_range_eq_two_pow a hindep hx, pow_succ']
  have hle : Module.finrank ℚ
      (IntermediateField.adjoin ℚ (insert w (Set.range x))) ≤ 2 ^ n := by
    have h := finrank_adjoin_le_two_pow a hiso (insert w (Finset.univ.image x)) (fun y hy ↦ by
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact ⟨c, hw2⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hys
        exact ⟨_, hx i⟩)
    rwa [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ] at h
  rw [hinsdeg] at hle
  exact absurd hle (by simp [pow_succ])

/-- `c_1, …, c_n` are squares in `K_n`: `c_{k+1} = ∏_β (β - a)` over the roots `β` of `f_k`, and
each `β - a` is the square of a root of `f_{k+1}`, which lies in `K_{k+1} ⊆ K_n`. -/
lemma isSquare_algebraMap_cSeq (ha : ¬IsSquare (-a : ℚ)) {k n : ℕ} (hkn : k < n) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (k + 1) : ℚ)) := by
  choose g hg using exists_sq_eq_sub a
  refine (IntermediateField.isSquare_algebraMap_iff _ _).mpr
    ⟨∏ β : fℚ[a, k].rootSet (AlgebraicClosure ℚ), g β, prod_mem fun β _ ↦ splittingField_mono a hkn
      (IntermediateField.subset_adjoin ℚ _ (mem_rootSet_succ_of_sq_eq_sub a β.2 (hg β))), ?_⟩
  rw [← Finset.prod_pow, map_intCast, ← prod_rootSet_sub_eq_cSeq a ha k]
  exact Finset.prod_congr rfl fun β _ ↦ hg β

lemma isSquare_algebraMap_iff_exists_mul_prod {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ))) (c : ℚ) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ S : Finset (Fin n), IsSquare (c * ∏ i ∈ S, (cSeq a ((i : ℕ) + 1) : ℚ)) := by
  classical
  have hmax := finrank_eq_of_nonempty_mulEquiv a hiso
  have hroot (i : Fin n) :
      IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact absurd i.2 (by simp)
    · have hnsq : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_finrank_eq a hnpos hmax
      exact isSquare_algebraMap_cSeq a hnsq i.2
  choose x hx using hroot
  have hx2 (i) : x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ) := by
    rw [sq]
    exact (hx i).symm
  rw [isSquare_algebraMap_iff_exists_sq_eq a hiso hindep hx2 c, ← Set.image_univ,
    ← Finset.coe_univ,
    IntermediateField.square_descent (fun i _ ↦ hx2 i) (fun i _ ↦ hindep.ne_zero i) c]
  exact exists_congr fun S ↦ and_iff_right (Finset.subset_univ S)

lemma twoIndependent_snoc_iff {n : ℕ} {v : Fin n → ℚ} (hv : TwoIndependent v) (c : ℚ) :
    TwoIndependent (Fin.snoc v c) ↔
      ∀ S : Finset (Fin n), ¬IsSquare (c * ∏ i ∈ S, v i) := by
  have hprod_no (S : Finset (Fin n)) :
      ∏ i ∈ S.map Fin.castSuccEmb, Fin.snoc v c i = ∏ i ∈ S, v i := by
    simp [Fin.snoc_castSucc]
  have hprod_yes (S : Finset (Fin n)) :
      ∏ i ∈ insert (Fin.last n) (S.map Fin.castSuccEmb), Fin.snoc v c i
        = c * ∏ i ∈ S, v i := by
    simp [Fin.snoc_last, hprod_no S]
  have hdecomp (T : Finset (Fin (n + 1))) :
      ∃ S : Finset (Fin n),
        (Fin.last n ∉ T → T = S.map Fin.castSuccEmb) ∧
        (Fin.last n ∈ T → T = insert (Fin.last n) (S.map Fin.castSuccEmb)) := by
    refine ⟨Finset.univ.filter (fun i : Fin n ↦ i.castSucc ∈ T), ?_, ?_⟩ <;>
      · intro hlast
        ext x
        rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl <;> simp [hlast]
  refine ⟨fun hsnocsq S ↦ ?_, fun hcS T hT ↦ ?_⟩
  · simpa [hprod_yes S] using
      hsnocsq (insert (Fin.last n) (S.map Fin.castSuccEmb)) (Finset.insert_nonempty _ _)
  · obtain ⟨S, hno, hyes⟩ := hdecomp T
    by_cases hlast : Fin.last n ∈ T
    · rw [hyes hlast, hprod_yes S]
      exact hcS S
    · rw [hno hlast, hprod_no S]
      exact hv S ((Finset.map_nonempty (f := Fin.castSuccEmb)).mp (hno hlast ▸ hT))

/-- Lemma 1.5: if `Ω_n ≅ [C_2]^n` and `c_1, …, c_n` are 2-independent, then `c ∈ ℚ` is a
non-square in `K_n` iff `c_1, …, c_n, c` are 2-independent (for `c = 0` both sides fail). -/
theorem kummer_extension_criterion {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ))) (c : ℚ) :
    ¬IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      TwoIndependent (Fin.snoc (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) c) := by
  rw [twoIndependent_snoc_iff hindep c,
    isSquare_algebraMap_iff_exists_mul_prod a hiso hindep c, not_exists]

end

end QuadraticIterates
