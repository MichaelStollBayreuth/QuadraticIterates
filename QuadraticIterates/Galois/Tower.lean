/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Relrank
public import QuadraticIterates.Galois.Iterates

import QuadraticIterates.Mathlib.FieldTheory.Multiquadratic
import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup
import QuadraticIterates.Mathlib.GroupTheory.Card
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The tower of splitting fields and Odoni's embedding

For a rational parameter `a`, `K_{n+1}` is generated over `K_n` by square roots of the `α - a`,
`α` a root of `f_n`, so `[K_{n+1} : K_n] ≤ 2^{2^n}`; every element of `Ω_n` has `2`-power order,
so `Ω_n` embeds into `[C₂]ⁿ` (Odoni). Comparing orders gives Lemma 1.4 of [Stoll 1992].

## Main statements

* `QuadraticIterates.splittingField_succ_eq_sup_adjoin`, `QuadraticIterates.relfinrank_succ_le`:
  `K_{n+1} = K_n(√(α - a) : α root of f_n)`, hence `[K_{n+1} : K_n] ≤ 2^{2^n}`.
* `QuadraticIterates.exists_injective_monoidHom_wreathPower`: `Ω_n` embeds into `[C₂]ⁿ`; hence
  `Ω_n ≅ [C₂]ⁿ` iff `[K_n : ℚ] = 2^{2^n - 1}`
  (`QuadraticIterates.nonempty_mulEquiv_iff_finrank_eq`).
* `QuadraticIterates.nonempty_mulEquiv_succ_iff` (Lemma 1.4 of [Stoll 1992]): `Ω_{n+1} ≅ [C₂]^{n+1}`
  iff `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}`.

## References

* M. Stoll, *Galois groups over ℚ of some iterated polynomials*, Arch. Math. **59** (1992),
  239-244.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-! ### The iterates over `ℚ` -/

section

variable (a : ℚ)

lemma ncard_rootSet_iteratedPoly_le (n : ℕ) :
    (fℚ[a, n].rootSet (AlgebraicClosure ℚ)).ncard ≤ 2 ^ n :=
  (ncard_rootSet_le _ _).trans_eq (natDegree_iteratedPoly _ n)

lemma mem_rootSet_iteratedPoly_succ (n : ℕ) (β : AlgebraicClosure ℚ) :
    β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ) ↔
    β ^ 2 + (a : AlgebraicClosure ℚ) ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ) := by
  rw [mem_rootSet_of_ne (monic_iteratedPoly (a : ℚ) _).ne_zero,
    mem_rootSet_of_ne (monic_iteratedPoly (a : ℚ) _).ne_zero, iteratedPoly_succ_comp, aeval_comp]
  simp

lemma mem_rootSet_succ_of_sq_eq_sub {n : ℕ} {α β : AlgebraicClosure ℚ}
    (hα : α ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ)) (hβ : β ^ 2 = α - a) :
    β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ) :=
  (mem_rootSet_iteratedPoly_succ a n β).mpr (by rwa [hβ, sub_add_cancel])

/-! ### The tower of splitting fields `K_n ⊆ K_{n+1}` -/

/-- Every element of `ℚ̄` has a square root after subtracting `a`; the square roots of the
`α - a` for `α` a root of `f_n` are what generates `K_{n+1}` over `K_n`. -/
lemma exists_sq_eq_sub (α : AlgebraicClosure ℚ) :
    ∃ β : AlgebraicClosure ℚ, β ^ 2 = α - (a : AlgebraicClosure ℚ) :=
  IsAlgClosed.exists_pow_nat_eq _ two_pos

/-- `K_n ⊆ K_{n+1}`: a root `α` of `f_n` is `β² + a` for a root `β` of `f_{n+1}`. -/
lemma splittingField_le_succ (n : ℕ) : splittingField a n ≤ splittingField a (n + 1) := by
  refine IntermediateField.adjoin_le_iff.mpr fun α hα ↦ ?_
  obtain ⟨β, hβ⟩ := exists_sq_eq_sub a α
  rw [← sub_add_cancel α (a : AlgebraicClosure ℚ), ← hβ]
  exact add_mem (pow_mem (IntermediateField.subset_adjoin ℚ _
    (mem_rootSet_succ_of_sq_eq_sub a hα hβ)) 2) (SubfieldClass.ratCast_mem _ a)

lemma splittingField_mono {m n : ℕ} (hmn : m ≤ n) : splittingField a m ≤ splittingField a n :=
  monotone_nat_of_le_succ (splittingField_le_succ a) hmn

/-- `K_0 = ℚ`: the only root of `f_0 = X` is `0`. -/
@[simp] lemma splittingField_zero_eq_bot : splittingField a 0 = ⊥ := by
  refine IntermediateField.adjoin_eq_bot_iff.mpr fun x hx ↦ ?_
  obtain rfl : x = 0 := by simpa [mem_rootSet] using hx
  exact zero_mem _

/-- For `a = 0`, `f_n = X^{2^n}` has only the root `0`, so `K_n = ℚ`. -/
@[simp] lemma splittingField_zero_left (n : ℕ) : splittingField 0 n = ⊥ := by
  simp [rootSet_X_pow (Nat.two_pow_pos n).ne']

/-- `K_{n+1} = K_n(√(α - a) : α root of f_n)`, for any choice `g` of square roots: a root `β` of
`f_{n+1}` is `± g(β² + a)`, and `g α` is a root of `f_{n+1}` for every root `α` of `f_n`. -/
theorem splittingField_succ_eq_sup_adjoin (n : ℕ) (g : AlgebraicClosure ℚ → AlgebraicClosure ℚ)
    (hg : ∀ α, g α ^ 2 = α - (a : AlgebraicClosure ℚ)) :
    splittingField a (n + 1) = splittingField a n ⊔
      IntermediateField.adjoin ℚ (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ))) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr fun β hβ ↦ ?_)
    (sup_le (splittingField_le_succ a n) (IntermediateField.adjoin_le_iff.mpr ?_))
  · have hgmem : g (β ^ 2 + a) ∈ splittingField a n ⊔
        IntermediateField.adjoin ℚ (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ))) :=
      IsConcreteLE.le_iff.mp le_sup_right (IntermediateField.subset_adjoin ℚ _
        ⟨_, (mem_rootSet_iteratedPoly_succ a n β).mp hβ, rfl⟩)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show β ^ 2 = g (β ^ 2 + a) ^ 2 by
      rw [hg, add_sub_cancel_right]) with h | h
    · exact h ▸ hgmem
    · exact h ▸ neg_mem hgmem
  · intro x ⟨α, hα, hx⟩
    exact hx ▸ IntermediateField.subset_adjoin ℚ _ (mem_rootSet_succ_of_sq_eq_sub a hα (hg α))

/-- The square of a root of `f_{n+1}` lies in `K_n`: `K_n ⊆ K_{n+1}` is a `2`-Kummer extension. -/
lemma sq_mem_splittingField_of_mem_rootSet_succ {n : ℕ} {β : AlgebraicClosure ℚ}
    (hβ : β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ)) : β ^ 2 ∈ splittingField a n := by
  rw [← add_sub_cancel_right (β ^ 2) (a : AlgebraicClosure ℚ)]
  exact sub_mem
    (IntermediateField.subset_adjoin ℚ _ ((mem_rootSet_iteratedPoly_succ a n β).mp hβ))
    (SubfieldClass.ratCast_mem _ a)

/-- The relative degree `[K_{n+1} : K_n]` is the degree of the multiquadratic extension of `K_n`
generated by a choice `g` of square roots of the `α - a`, `α` a root of `f_n`. -/
theorem relfinrank_succ_eq_finrank_adjoin (n : ℕ) (g : AlgebraicClosure ℚ → AlgebraicClosure ℚ)
    (hg : ∀ α, g α ^ 2 = α - (a : AlgebraicClosure ℚ)) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = Module.finrank ↥(splittingField a n)
          ↥(IntermediateField.adjoin ↥(splittingField a n)
            (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ)))) := by
  rw [splittingField_succ_eq_sup_adjoin a n g hg,
    ← IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.relfinrank_eq_finrank_of_le
      (by rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact le_sup_left)]
  rfl

/-- `[K_{n+1} : K_n] ≤ 2^{2^n}`: `K_{n+1}` is generated over `K_n` by at most `2^n` square
roots. -/
theorem relfinrank_succ_le (n : ℕ) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) ≤ 2 ^ 2 ^ n := by
  choose g hg using exists_sq_eq_sub a
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg]
  refine (IntermediateField.finrank_adjoin_sqrt_le_two_pow_ncard ((rootSet_finite _ _).image g)
    ?_).trans (Nat.pow_le_pow_right two_pos
      ((Set.ncard_image_le (rootSet_finite _ _)).trans (ncard_rootSet_iteratedPoly_le a n)))
  intro x ⟨α, hα, hx⟩
  exact ⟨⟨α - a, sub_mem (IntermediateField.subset_adjoin ℚ _ hα)
    (SubfieldClass.ratCast_mem _ a)⟩, hx ▸ hg α⟩

/-! ### Odoni's embedding `Ω_n ↪ [C₂]ⁿ` -/

theorem pow_two_pow_apply_root (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {m : ℕ} {γ : AlgebraicClosure ℚ} (hγ : γ ∈ fℚ[a, m].rootSet (AlgebraicClosure ℚ)) :
    (φ ^ 2 ^ m) γ = γ := by
  induction m generalizing γ with
  | zero =>
    obtain rfl : γ = 0 := by simpa [mem_rootSet] using hγ
    simp
  | succ k ih =>
    have hsq : ((φ ^ 2 ^ k) γ) ^ 2 = γ ^ 2 := add_right_cancel (by
      simpa only [map_add, map_pow, map_ratCast] using
        ih ((mem_rootSet_iteratedPoly_succ a k γ).mp hγ))
    rw [pow_succ, pow_mul, sq, AlgEquiv.mul_apply]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> simp only [h, map_neg, neg_neg]

theorem isPGroup_galoisGroup (n : ℕ) : IsPGroup 2 (GaloisGroup a n) := by
  set F := fℚ[a, n]
  refine isPGroup_iff_pow_pow_eq_one.mpr fun σ ↦ ⟨n, ?_⟩
  obtain ⟨φ, rfl⟩ := Gal.restrict_surjective F (AlgebraicClosure ℚ) σ
  apply Gal.galActionHom_injective F (AlgebraicClosure ℚ)
  rw [map_one, ← map_pow]
  exact Equiv.ext fun β ↦ Subtype.ext <|
    (Gal.galActionHom_restrict F (AlgebraicClosure ℚ) (φ ^ 2 ^ n) β).trans
      (pow_two_pow_apply_root a φ β.2)

/-- Odoni's embedding theorem: `Ω_n` embeds into `[C₂]ⁿ`, being a `2`-group acting faithfully on
the at most `2 ^ n` roots of `f_n`. -/
theorem exists_injective_monoidHom_wreathPower (n : ℕ) :
    ∃ φ : GaloisGroup a n →* WreathPower n, Function.Injective φ :=
  (isPGroup_galoisGroup a n).exists_injective_monoidHom_iteratedWreathProduct
    (Gal.galActionHom_injective fℚ[a, n] (AlgebraicClosure ℚ))
    ((Nat.card_coe_set_eq _).trans_le (ncard_rootSet_iteratedPoly_le a n))
    (Multiplicative (ZMod 2)) (Nat.card_zmod 2)

/-! ### Lemma 1.4 of [Stoll 1992]: maximality of `Ω_{n+1}` from `Ω_n` and `[K_{n+1} : K_n]` -/

/-- `#Ω_n = [K_n : ℚ]`, since `K_n` is a Galois splitting field of `f_n` over `ℚ`. -/
lemma card_galoisGroup_eq_finrank (n : ℕ) :
    Nat.card (GaloisGroup a n) = Module.finrank ℚ ↥(splittingField a n) :=
  (Nat.card_congr (AlgEquiv.autCongr (IsSplittingField.algEquiv _ fℚ[a, n]).symm).toEquiv).trans
    (IsGalois.card_aut_eq_finrank ℚ _)

/-- `Ω_n ≅ [C₂]ⁿ` iff `K_n` has the maximal possible degree `2^{2^n - 1}` over `ℚ`, since `Ω_n`
embeds into `[C₂]ⁿ` (`QuadraticIterates.exists_injective_monoidHom_wreathPower`) and
`#Ω_n = [K_n : ℚ]`. -/
theorem nonempty_mulEquiv_iff_finrank_eq (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1) := by
  obtain ⟨φ, hφ⟩ := exists_injective_monoidHom_wreathPower a n
  rw [φ.nonempty_mulEquiv_iff_card_eq hφ, card_galoisGroup_eq_finrank, card_wreathPower]

/-- Lemma 1.4 of [Stoll 1992]: `Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and
`[K_{n+1} : K_n] = 2^{2^n}`. Both `#Ω_n ≤ #[C₂]ⁿ` (by
`QuadraticIterates.exists_injective_monoidHom_wreathPower`) and `[K_{n+1} : K_n] ≤ 2^{2^n}`, and the
products of the two sides agree iff both factors do. -/
theorem nonempty_mulEquiv_succ_iff (n : ℕ) :
    Nonempty (GaloisGroup a (n + 1) ≃* WreathPower (n + 1)) ↔
      Nonempty (GaloisGroup a n ≃* WreathPower n) ∧
        (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n := by
  obtain ⟨φn, hφn⟩ := exists_injective_monoidHom_wreathPower a n
  obtain ⟨φn1, hφn1⟩ := exists_injective_monoidHom_wreathPower a (n + 1)
  rw [φn1.nonempty_mulEquiv_iff_card_eq hφn1, φn.nonempty_mulEquiv_iff_card_eq hφn,
    card_wreathPower_succ, card_galoisGroup_eq_finrank a (n + 1),
    ← IntermediateField.finrank_bot_mul_relfinrank (splittingField_le_succ a n),
    ← card_galoisGroup_eq_finrank]
  exact mul_eq_mul_iff_eq_and_eq_of_pos
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_injective φn hφn)) (relfinrank_succ_le a n)
    Nat.card_pos (Nat.two_pow_pos _)

end

end QuadraticIterates
