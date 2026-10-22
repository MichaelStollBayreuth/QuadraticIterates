/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import QuadraticIterates.Mathlib.Algebra.GCDMonoid.Basic
import QuadraticIterates.Mathlib.Data.Multiset

/-!
# Unique factorization lemmas

An automorphism that fixes an element up to associates permutes its normalized factors, and an
involutive one pairs them up when the element has no nontrivial invariant divisor
(`exists_normalizedFactors_eq_add_map`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

/-- If `σ` is a multiplicative automorphism of a normalization UFD and `σ p` is associated to
`p`, then `normalize ∘ σ` permutes the multiset of normalized factors of `p`. -/
lemma normalizedFactors_map_mulEquiv_eq (σ : α ≃* α) {p : α} (hp0 : p ≠ 0)
    (hassoc : Associated (σ p) p) :
    (normalizedFactors p).map (fun q ↦ normalize (σ q)) = normalizedFactors p := by
  have hirr : ∀ q ∈ (normalizedFactors p).map σ, Irreducible q :=
    Multiset.forall_mem_map_iff.mpr fun q hq ↦
      (MulEquiv.irreducible_iff σ).mpr (irreducible_of_normalized_factor q hq)
  have hprod : Associated ((normalizedFactors p).map σ).prod p := by
    rw [← map_multiset_prod]
    exact ((prod_normalizedFactors hp0).map σ.toMonoidHom).trans hassoc
  calc (normalizedFactors p).map (fun q ↦ normalize (σ q))
      = ((normalizedFactors p).map σ).map normalize := (Multiset.map_map normalize σ _).symm
    _ = normalizedFactors ((normalizedFactors p).map σ).prod :=
        (normalizedFactors_prod_eq _ hirr).symm
    _ = normalizedFactors p := hprod.normalizedFactors_eq

/-- If `σ` is an involutive multiplicative automorphism of a normalization UFD, `σ p` is
associated to `p`, `p` is not irreducible, and every divisor of `p` that is `σ`-invariant up to
associates is trivial, then the normalized factors of `p` pair up under `normalize ∘ σ`. -/
theorem exists_normalizedFactors_eq_add_map (σ : α ≃* α) (hσ : Function.Involutive σ) {p : α}
    (hp0 : p ≠ 0) (hσp : Associated (σ p) p) (hp : ¬Irreducible p)
    (h : ∀ d : α, d ∣ p → Associated (σ d) d → IsUnit d ∨ Associated d p) :
    ∃ N : Multiset α, normalizedFactors p = N + N.map fun q ↦ normalize (σ q) := by
  refine Multiset.exists_add_map_of_involutive (fun q ↦ normalize (σ q)) _ (fun q hq ↦ ?_)
    (normalizedFactors_map_mulEquiv_eq σ hp0 hσp) fun q hq hfix ↦ ?_
  · rw [normalize_map_normalize, hσ q, normalize_normalized_factor q hq]
  · have hirr := irreducible_of_normalized_factor q hq
    have hσq : Associated (σ q) q := (normalize_associated (σ q)).symm.trans (by rw [hfix])
    exact (h q (dvd_of_mem_normalizedFactors hq) hσq).elim hirr.not_isUnit
      fun hap ↦ hp (hap.irreducible hirr)
