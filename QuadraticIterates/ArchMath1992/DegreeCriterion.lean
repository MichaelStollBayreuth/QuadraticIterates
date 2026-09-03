/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates

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

lemma rootShift_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n)
    (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) : rootShift a n β ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff, coe_rootShift]
  simpa using sub_intCast_ne_zero_of_mem_rootSet a ha hn β.2

/-- The relative degree `[K_{n+1} : K_n]` equals `2 ^ (2^n - d)`, where `d` is the `𝔽₂`-dimension
of the multiquadratic relations among the shifted roots `β - a` of `f_n`. -/
theorem relfinrank_succ_eq_pow [DecidableEq (AlgebraicClosure ℚ)] {n : ℕ} (hn : 1 ≤ n)
    (hirr : Irreducible (fℚ[a, n])) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = 2 ^ (2 ^ n - Module.finrank (ZMod 2) (rootRelations (rootShift a n))) := by
  classical
  have hnsq : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_irreducible a hn hirr
  choose g hg using exists_sq_eq_sub a
  set x : ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) → AlgebraicClosure ℚ := fun β ↦ g β
  have hx (β) :
      x β ^ 2 = algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (rootShift a n β) :=
    hg β.1
  have hset : g '' ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
      = Set.range x := Set.image_eq_range g _
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg, hset,
    multiquadratic_degree_family hx (rootShift_ne_zero a hnsq hn),
    card_rootSet_iteratedPoly a hirr]

lemma exists_ringEquiv_radicand_smul {n : ℕ}
    [Fact (map (algebraMap ℚ (AlgebraicClosure ℚ)) (fℚ[a, n])).Splits]
    (r : ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
        → ↥(splittingField a n))
    (hr : ∀ β, (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β))
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) (σ : GaloisGroup a n) :
    ∃ φ : (↥(splittingField a n)) ≃+* (↥(splittingField a n)), ∀ β, φ (r β) = r (σ • β) := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective (fℚ[a, n]) (AlgebraicClosure ℚ) σ
  refine ⟨(ϕ.restrictNormal (splittingField a n)).toRingEquiv, fun β ↦ ?_⟩
  apply (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hσβ : (((Gal.restrict (fℚ[a, n]) (AlgebraicClosure ℚ)) ϕ • β :
      ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))) :
        AlgebraicClosure ℚ) = ϕ (β : AlgebraicClosure ℚ) :=
    Gal.restrict_smul ϕ β
  have hcomm : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      ((ϕ.restrictNormal (splittingField a n)).toRingEquiv (r β))
      = ϕ (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β)) :=
    AlgEquiv.restrictNormal_commutes ϕ (splittingField a n) (r β)
  rw [hcomm, hr β, hr _, hσβ, map_sub, map_intCast]

lemma isPretransitive_galoisGroup (n : ℕ)
    (hirr : Irreducible (fℚ[a, n]))
    [Fact (map (algebraMap ℚ (AlgebraicClosure ℚ)) (fℚ[a, n])).Splits] :
    MulAction.IsPretransitive (GaloisGroup a n)
      ↑((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
  Gal.galAction_isPretransitive (fℚ[a, n]) (AlgebraicClosure ℚ) hirr

lemma prod_aroots_sub_eq_cSeq (n : ℕ) :
    (Multiset.map (fun α ↦ α - (a : AlgebraicClosure ℚ))
        ((fℚ[a, n]).aroots (AlgebraicClosure ℚ))).prod
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
  set F := fℚ[a, n] with hF
  have hmonic : F.Monic := monic_iteratedPoly _ n
  have hsplits : (F.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits := IsAlgClosed.splits _
  have hcard : (F.aroots (AlgebraicClosure ℚ)).card = 2 ^ n := by
    rw [aroots_def, ← hsplits.natDegree_eq_card_roots, hmonic.natDegree_map, hF,
      natDegree_iteratedPoly]
  calc (Multiset.map (fun α ↦ α - (a : AlgebraicClosure ℚ))
          (F.aroots (AlgebraicClosure ℚ))).prod
      = (((F.aroots (AlgebraicClosure ℚ)).map
          (fun α ↦ (a : AlgebraicClosure ℚ) - α)).map (fun x ↦ -x)).prod := by
        rw [Multiset.map_map]
        exact congrArg _ (Multiset.map_congr rfl fun α _ ↦ by simp)
    _ = (-1 : AlgebraicClosure ℚ) ^ (F.aroots (AlgebraicClosure ℚ)).card
          * ((F.aroots (AlgebraicClosure ℚ)).map
              (fun α ↦ (a : AlgebraicClosure ℚ) - α)).prod := by
        rw [Multiset.prod_map_neg, Multiset.card_map]
    _ = (-1 : AlgebraicClosure ℚ) ^ 2 ^ n
          * (aeval (a : AlgebraicClosure ℚ)) F := by
        rw [hcard, ← hsplits.aeval_eq_prod_aroots_of_monic hmonic (a : AlgebraicClosure ℚ)]
    _ = (-1 : AlgebraicClosure ℚ) ^ 2 ^ n
          * (((iteratedPoly a n).eval a : ℤ) : AlgebraicClosure ℚ) := by
        rw [hF, aeval_intCast_iteratedPoly]
    _ = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
        rw [cSeq_succ_eq_neg_one_pow_mul_eval a n]
        push_cast
        ring

lemma prod_radicand_eq_cSeq {n : ℕ} (hirr : Irreducible (fℚ[a, n]))
    (r : ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
        → ↥(splittingField a n))
    (hr : ∀ β, (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β))
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) :
    ∏ β, r β = algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ) := by
  classical
  apply (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hnodup : ((fℚ[a, n]).aroots (AlgebraicClosure ℚ)).Nodup := nodup_roots hirr.separable.map
  have hleft : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (∏ β, r β)
      = ∏ β : ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)),
          ((β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun β _ ↦ hr β
  have hright : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      (algebraMap ℚ (↥(splittingField a n)) (cSeq a (n + 1) : ℚ))
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
    simp
  rw [hleft, prod_rootSet_eq_prod_aroots hnodup (· - (a : AlgebraicClosure ℚ)), hright]
  exact prod_aroots_sub_eq_cSeq a n

end

section

variable (a : ℤ)

/-! ### The degree criterion and the Kummer extension criterion -/

/-- If `-a` is not a rational square, `K_1 = ℚ(√(-a))` has degree `2` over `ℚ`. -/
lemma finrank_splittingField_one (hsq : ¬IsSquare (-a : ℚ)) :
    Module.finrank ℚ ↥(splittingField a 1) = 2 := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ))) two_pos
  have hβsq : β ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (-a : ℚ) := by rw [hβ, map_neg]
  have hpoly := iteratedPoly_one (a : ℚ)
  have hβroot : β ∈ (fℚ[a, 1]).rootSet (AlgebraicClosure ℚ) := by
    rw [mem_rootSet', hpoly]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_add, Polynomial.map_pow, map_X, map_C]
      exact X_pow_add_C_ne_zero two_pos _
    · simp [map_add, map_pow, aeval_X, hβ]
  have hadjeq : splittingField a 1 = IntermediateField.adjoin ℚ {β} := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr fun x hx ↦ ?_
      rw [mem_rootSet', hpoly] at hx
      obtain ⟨-, hx2⟩ := hx
      simp only [map_add, map_pow, aeval_X, aeval_C] at hx2
      have hβmem : β ∈ IntermediateField.adjoin ℚ ({β} : Set (AlgebraicClosure ℚ)) :=
        IntermediateField.subset_adjoin ℚ _ rfl
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp
        (show x ^ 2 = β ^ 2 by linear_combination hx2 - hβ) with rfl | rfl
      · exact hβmem
      · exact neg_mem hβmem
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x rfl
      exact IntermediateField.subset_adjoin ℚ _ hβroot
  rw [hadjeq, IntermediateField.finrank_adjoin_sqrt_eq hβsq, if_neg hsq]

lemma degree_criterion_zero :
    (splittingField a 0).relfinrank (splittingField a 1) = 2 ^ 2 ^ 0 ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a 0) (cSeq a (0 + 1) : ℚ)) := by
  have hK0bot := splittingField_zero_eq_bot a
  have hrf : (splittingField a 0).relfinrank (splittingField a 1)
      = Module.finrank ℚ ↥(splittingField a 1) := by
    rw [hK0bot, IntermediateField.relfinrank_bot_left]
  have hsq_iff : IsSquare (algebraMap ℚ ↥(splittingField a 0) (cSeq a (0 + 1) : ℚ))
      ↔ IsSquare (-a : ℚ) := by
    rw [hK0bot, show (cSeq a (0 + 1) : ℚ) = -(a : ℚ) by norm_num]
    exact IntermediateField.isSquare_algebraMap_bot_iff _
  rw [hrf, hsq_iff]
  by_cases hsq : IsSquare (-a : ℚ)
  · rw [splittingField_one_eq_bot_of_isSquare a hsq, IntermediateField.finrank_bot]
    simp [hsq]
  · simp only [hsq, not_false_iff, iff_true, pow_zero, pow_one]
    exact finrank_splittingField_one a hsq

/-- Lemma 1.6: if `f_n` is irreducible over `ℚ`, then `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}`
is not a square in `K_n`. -/
theorem degree_criterion {n : ℕ} (hirr : Irreducible (fℚ[a, n])) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact degree_criterion_zero a
  · have hna : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_irreducible a hn hirr
    have hrne := rootShift_ne_zero a hna hn
    have : Fact (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (fℚ[a, n])).Splits := ⟨IsAlgClosed.splits _⟩
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
      rw [relfinrank_succ_eq_pow a hn hirr, Nat.pow_right_inj one_lt_two]
      lia
    have hallne : 1 ∈ rootRelations (rootShift a n) ↔ rootRelations (rootShift a n) ≠ ⊥ := by
      refine ⟨fun hmem hbot ↦ one_ne_zero (α := ZMod 2) ?_,
        fun hbot ↦ rootRelations_all_ones (isPGroup_galoisGroup a n) hrne ?_ hbot⟩
      · rw [hbot, Submodule.mem_bot] at hmem
        exact congrFun hmem (Classical.arbitrary _)
      · exact exists_ringEquiv_radicand_smul a (rootShift a n) fun _ ↦ rfl
    have hallsq : 1 ∈ rootRelations (rootShift a n)
        ↔ IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) :=
      (all_ones_mem_rootRelations hrne).trans
        (by rw [prod_radicand_eq_cSeq a hirr (rootShift a n) fun _ ↦ rfl])
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

lemma isSquare_algebraMap_cSeq (n : ℕ) (hnsq : ¬IsSquare (-a : ℚ)) (m : ℕ) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a m : ℚ)) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  have hmono : splittingField a (k + 1) ≤ splittingField a n := splittingField_mono a hmn
  have hinj := (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hsqrt (β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ))) :
      ∃ γ : ↥(splittingField a n),
        (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) γ) ^ 2
          = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := by
    obtain ⟨δ, hδ⟩ := exists_sq_eq_sub a β
    have hroot : δ ∈ (fℚ[a, k + 1]).rootSet (AlgebraicClosure ℚ) :=
      (mem_rootSet_iteratedPoly_succ a k δ).mpr (by simp [hδ, sub_add_cancel, β.2])
    exact ⟨⟨δ, hmono (IntermediateField.subset_adjoin ℚ _ hroot)⟩, hδ⟩
  choose w hw using hsqrt
  have hnodup : ((fℚ[a, k]).aroots (AlgebraicClosure ℚ)).Nodup :=
    nodup_roots (irreducible_iteratedPoly a hnsq k).separable.map
  refine ⟨∏ β, w β, hinj ?_⟩
  have hlhs : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      ((algebraMap ℚ (↥(splittingField a n))) (cSeq a (k + 1) : ℚ))
      = (cSeq a (k + 1) : AlgebraicClosure ℚ) := by
    simp
  rw [hlhs, map_mul, map_prod]
  have hsplit : (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
        * (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
      = ∏ β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ)),
          ((β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ ↦ by rw [← sq, hw β]
  rw [hsplit, prod_rootSet_eq_prod_aroots hnodup (· - (a : AlgebraicClosure ℚ))]
  exact (prod_aroots_sub_eq_cSeq a k).symm

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
      simpa using isSquare_algebraMap_cSeq a n hnsq ((i : ℕ) + 1) (by lia)
        (by have := i.2; lia)
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
