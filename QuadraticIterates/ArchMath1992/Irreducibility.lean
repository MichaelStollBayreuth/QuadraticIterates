/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates

import QuadraticIterates.Mathlib.Algebra.Polynomial.Eval
import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.Multiset
import QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Irreducibility of the iterates over `ℚ`

An even polynomial in `ℚ[X]` that is reducible but has no nontrivial even divisor factors as
`g · g(-X)` (`even_reducible_factorization`); applied to `f_n`, this shows that a factorization of
`f_n` would make `c_n` a square (Lemma 1.2, `irreducible_iteratedPoly_of_not_isSquare_cSeq`). Since
no `c_n` is a square when `-a` is not one, every `f_n` is irreducible (Corollary 1.3,
`irreducible_iteratedPoly`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

/-- If `-a` is not a rational square then `a ≠ 0`, since `-0` is. -/
lemma ne_zero_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ 0 := by
  rintro rfl; exact ha (by simp)

private lemma ne_neg_one_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ -1 := by
  rintro rfl; exact ha (by norm_num)

/-! ### Even factorizations and non-square `c_n` -/

private lemma abs_le_sq_add_of_abs_le_abs {a d : ℤ} (ha : a ≠ -1) (h : |a| ≤ |d|) :
    |a| ≤ d ^ 2 + a := by
  rcases le_or_gt 0 a with ha0 | ha0
  · rw [abs_of_nonneg ha0]
    exact le_add_of_nonneg_left (sq_nonneg d)
  · rw [abs_of_neg ha0] at h ⊢
    have ha2 : a ≤ -2 := by lia
    nlinarith [sq_abs d, mul_le_mul h h (by lia) (abs_nonneg d)]

private lemma not_isSquare_sq_add_of_abs_le_abs {a d : ℤ} (ha0 : a ≠ 0) (ha1 : a ≠ -1)
    (h : |a| ≤ |d|) : ¬IsSquare (d ^ 2 + a) := by
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · rw [abs_of_neg ha] at h
    have ha2 : a ≤ -2 := by lia
    exact Int.not_isSquare_of_sq_lt_of_lt_sq (e := |d| - 1) (by nlinarith [sq_abs d])
      (by nlinarith [sq_abs d])
  · rw [abs_of_pos ha] at h
    exact Int.not_isSquare_of_sq_lt_of_lt_sq (e := |d|) (by nlinarith [sq_abs d])
      (by nlinarith [sq_abs d])

/-- `|c_n| ≥ |a|` for all `n ≥ 1` (the observation in the proof of Corollary 1.3). -/
theorem abs_le_abs_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : |a| ≤ |cSeq a n| := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [cSeq_succ a hk]
    exact (abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg a ha) ih).trans
      (le_abs_self _)

/-- `c_n ≥ |a|` for all `n ≥ 2`. -/
theorem abs_le_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : |a| ≤ cSeq a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rw [cSeq_succ a (by lia)]
  exact abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg a ha)
    (abs_le_abs_cSeq a ha (by lia))

/-- Lemma 1.1 a): `c_n > 0` for all `n ≥ 2`. -/
theorem cSeq_pos (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : 0 < cSeq a n :=
  (abs_pos.mpr (ne_zero_of_not_isSquare_neg a ha)).trans_le (abs_le_cSeq a ha hn)

/-- No `c_n` (`n ≥ 1`) is a rational square: `c_{n+1} = c_n² + a` lies strictly between two
consecutive squares because `|c_n| ≥ |a|`, and `c_1 = -a` is not a square by assumption. -/
theorem not_isSquare_cSeq (ha : ¬IsSquare (-a : ℚ)) {k : ℕ} (hk : 1 ≤ k) :
    ¬IsSquare (cSeq a k : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : k ≠ 0)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa [← Rat.isSquare_intCast_iff] using ha
  · rw [cSeq_succ a hj]
    exact not_isSquare_sq_add_of_abs_le_abs (ne_zero_of_not_isSquare_neg a ha)
      (ne_neg_one_of_not_isSquare_neg a ha) (abs_le_abs_cSeq a ha hj)

lemma map_iteratedPoly_comp_neg_X (k : ℕ) : (fℚ[a, k + 1]).comp (-X) = fℚ[a, k + 1] := by
  rw [iteratedPoly_succ_comp, comp_assoc, X_sq_add_C_comp_neg_X]

/-- A monic `p` associated to `g * g(-X)` with `g` monic equals `(-1)^(deg g) · g · g(-X)`. -/
private theorem monic_eq_of_associated_mul_comp_neg_X {g p : ℚ[X]}
    (hgMonic : g.Monic) (hpMonic : p.Monic) (hassoc : Associated p (g * g.comp (-X))) :
    p = C ((-1 : ℚ) ^ g.natDegree) * (g * g.comp (-X)) := by
  have hwMonic : (C ((-1 : ℚ) ^ g.natDegree) * (g * g.comp (-X))).Monic := by
    have h1 : C ((-1 : ℚ) ^ g.natDegree) * (g * g.comp (-X))
        = g * ((-1 : ℚ[X]) ^ g.natDegree * g.comp (-X)) := by
      rw [map_pow, map_neg, map_one]
      ring
    rw [h1]
    exact hgMonic.mul (Monic.neg_one_pow_natDegree_mul_comp_neg_X hgMonic)
  apply eq_of_monic_of_associated hpMonic hwMonic
  rw [mul_comm (C ((-1 : ℚ) ^ g.natDegree))]
  exact hassoc.trans (associated_mul_unit_left _ _
    (isUnit_C.mpr (isUnit_one.neg.pow g.natDegree))).symm

/-- For a nonzero reducible even `p` with no nontrivial even divisors, the map
`q ↦ normalize (q(-X))` is a fixed-point-free involution on the normalized factors of `p`,
hence pairs them up. -/
private theorem exists_normalizedFactors_involution_split {p : ℚ[X]} (hp0 : p ≠ 0)
    (heven : p.comp (-X) = p) (hpirr : ¬ Irreducible p)
    (hnoeven : ∀ d : ℚ[X], d ∣ p → Associated (d.comp (-X)) d → IsUnit d ∨ Associated d p) :
    ∃ N : Multiset ℚ[X], UniqueFactorizationMonoid.normalizedFactors p
      = N + N.map (fun q ↦ normalize (q.comp (-X))) := by
  set σ : ℚ[X] ≃ₐ[ℚ] ℚ[X] := algEquivAevalNegX
  have hσapp (q : ℚ[X]) : σ q = q.comp (-X) := by
    rw [algEquivAevalNegX_apply, ← comp_eq_aeval]
  set M := UniqueFactorizationMonoid.normalizedFactors p
  set τ : ℚ[X] → ℚ[X] := fun q ↦ normalize (q.comp (-X)) with hτdef
  have hτinv (q : ℚ[X]) (hq : q ∈ M) : τ (τ q) = q := by
    have hqnorm : normalize q = q :=
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff' hp0).mp hq).2.1
    calc τ (τ q) = τ (q.comp (-X)) := normalize_normalize_comp_neg_X _
      _ = normalize q := congrArg normalize (comp_neg_X_comp_neg_X q)
      _ = q := hqnorm
  have hinvM : M.map τ = M := by
    have hτσ (q : ℚ[X]) : τ q = normalize (σ.toRingEquiv.toMulEquiv q) := by
      simp only [hτdef]
      rw [← hσapp q]
      rfl
    rw [Multiset.map_congr rfl fun q _ ↦ hτσ q]
    exact normalizedFactors_map_mulEquiv_eq σ.toRingEquiv.toMulEquiv hp0
      (by rw [show σ.toRingEquiv.toMulEquiv p = p from (hσapp p).trans heven]; exact .refl p)
  have hfixM (q : ℚ[X]) (hq : q ∈ M) : τ q ≠ q := by
    intro hfix
    have hirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hassoc : Associated (q.comp (-X)) q := by
      have h1 := (normalize_associated (q.comp (-X))).symm
      rwa [show normalize (q.comp (-X)) = τ q from rfl, hfix] at h1
    rcases hnoeven q (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq) hassoc
      with hu | hap
    · exact hirr.not_isUnit hu
    · exact hpirr (hap.irreducible hirr)
  exact Multiset.exists_add_map_of_involutive τ M hτinv hinvM hfixM

/-- A reducible monic even polynomial with no nontrivial even divisors factors as
`(-1) ^ (deg g) · p = g · g(-X)`: its irreducible factors pair up under `X ↦ -X`. -/
theorem even_reducible_factorization {p : ℚ[X]} (hmonic : p.Monic)
    (heven : p.comp (-X) = p) (hpirr : ¬ Irreducible p)
    (hnoeven : ∀ d : ℚ[X], d ∣ p → Associated (d.comp (-X)) d → IsUnit d ∨ Associated d p) :
    ∃ g : ℚ[X], 2 * g.natDegree = p.natDegree ∧
      C ((-1 : ℚ) ^ g.natDegree) * p = g * g.comp (-X) := by
  have hp0 : p ≠ 0 := hmonic.ne_zero
  obtain ⟨N, hN⟩ := exists_normalizedFactors_involution_split hp0 heven hpirr hnoeven
  set τ : ℚ[X] → ℚ[X] := fun q ↦ normalize (q.comp (-X)) with hτdef
  set g := N.prod with hgdef
  have hNsub (q : ℚ[X]) (hq : q ∈ N) : q ∈ UniqueFactorizationMonoid.normalizedFactors p :=
    hN ▸ Multiset.mem_add.mpr (.inl hq)
  have hgMonic : g.Monic := by
    rw [hgdef, ← Multiset.map_id N]
    exact monic_multiset_prod_of_monic _ _ fun q hq ↦
      ((Polynomial.mem_normalizedFactors_iff hp0).mp (hNsub q hq)).2.1
  have hNcompprod : (N.map (fun q ↦ q.comp (-X))).prod = g.comp (-X) := by
    rw [← multiset_prod_comp, hgdef]
  have hNmapτ : Associated (N.map τ).prod (g.comp (-X)) := by
    have heq : (N.map τ).prod = normalize ((N.map (fun q ↦ q.comp (-X))).prod) := by
      simpa [Multiset.map_map, hτdef, coe_normalizeHom] using
        (map_multiset_prod (normalizeHom (α := ℚ[X])) (N.map (fun q ↦ q.comp (-X)))).symm
    rw [heq, hNcompprod]
    exact normalize_associated _
  have hassoc_p : Associated p (g * g.comp (-X)) := by
    have hMprod : Associated (g * (N.map τ).prod) p := by
      have hprodeq : (UniqueFactorizationMonoid.normalizedFactors p).prod
          = g * (N.map τ).prod := by
        rw [hN, Multiset.prod_add, hgdef]
      exact hprodeq ▸ UniqueFactorizationMonoid.prod_normalizedFactors hp0
    exact hMprod.symm.trans (Associated.mul_left g hNmapτ)
  have hpw : p = C ((-1 : ℚ) ^ g.natDegree) * (g * g.comp (-X)) :=
    monic_eq_of_associated_mul_comp_neg_X hgMonic hmonic hassoc_p
  refine ⟨g, ?_, ?_⟩
  · rw [hpw, natDegree_C_mul (neg_one_pow_ne_zero g.natDegree),
      natDegree_mul hgMonic.ne_zero (by rw [Ne, comp_neg_X_eq_zero_iff]; exact hgMonic.ne_zero),
      natDegree_comp]
    simp
    ring
  · rw [hpw, ← mul_assoc, ← map_mul, show (-1 : ℚ) ^ g.natDegree * (-1 : ℚ) ^ g.natDegree = 1 by
        rw [← mul_pow, neg_mul_neg, one_mul, one_pow],
      map_one, one_mul]

end

section

variable (a : ℤ)

/-! ### Irreducibility of the iterates -/

/-- If `f_{j+1}` factors over `ℚ` as `C ((-1)^{deg g}) * f_{j+1} = g * g(-X)` with
`deg f_{j+1} = 2 · deg g`, then evaluation at `0` exhibits `c_{j+1}` as a square in `ℚ`. -/
private lemma isSquare_cSeq_of_even_factorization {j : ℕ} {g : ℚ[X]}
    (hgdeg : 2 * g.natDegree = (fℚ[a, j + 1]).natDegree)
    (hgeq : C ((-1 : ℚ) ^ g.natDegree) * fℚ[a, j + 1] = g * g.comp (-X)) :
    IsSquare (cSeq a (j + 1) : ℚ) := by
  have hgnd : g.natDegree = 2 ^ j := by
    rw [natDegree_iteratedPoly, pow_succ'] at hgdeg
    lia
  have heval := congrArg (eval 0) hgeq
  simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_zero] at heval
  exact ⟨g.eval 0, by rwa [intCast_cSeq_succ_eq_neg_one_pow_mul_eval_zero, ← hgnd]⟩

/-- Lemma 1.2: if none of `c_1, …, c_n` is a square in `ℚ`, then `f_n` is irreducible over `ℚ`. -/
theorem irreducible_iteratedPoly_of_not_isSquare_cSeq {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ k ≥ 1, k ≤ n → ¬IsSquare (cSeq a k : ℚ)) :
    Irreducible (fℚ[a, n]) := by
  classical
  by_contra hcon
  have hex : ∃ k, 1 ≤ k ∧ k ≤ n ∧ ¬ Irreducible (fℚ[a, k]) := ⟨n, hn, le_rfl, hcon⟩
  obtain ⟨j, hjfind⟩ : ∃ j, Nat.find hex = j + 1 :=
    ⟨Nat.find hex - 1, by have := (Nat.find_spec hex).1; lia⟩
  obtain ⟨hj1, hjn, hjred⟩ := hjfind ▸ Nat.find_spec hex
  have hFj_irr : Irreducible (fℚ[a, j]) := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using irreducible_X (R := ℚ)
    · by_contra hc
      exact Nat.find_min hex (hjfind ▸ Nat.lt_succ_self j) ⟨hjpos, by lia, hc⟩
  have hval0 : (fℚ[a, j + 1]).eval 0 ≠ 0 := fun hzero ↦ h (j + 1) (by lia) (by lia)
    (by rw [intCast_cSeq_succ_eq_neg_one_pow_mul_eval_zero, hzero, mul_zero]; exact .zero)
  have hnoeven : ∀ d : ℚ[X], d ∣ fℚ[a, j + 1] → Associated (d.comp (-X)) d →
      IsUnit d ∨ Associated d (fℚ[a, j + 1]) := by
    rw [iteratedPoly_succ_comp]
    exact fun _ ↦ hFj_irr.isUnit_or_associated_of_dvd_comp_of_associated_comp_neg_X
      (by rwa [eval_zero_iteratedPoly_succ] at hval0)
  obtain ⟨g, hgdeg, hgeq⟩ := even_reducible_factorization
    (monic_iteratedPoly (a : ℚ) (j + 1)) (map_iteratedPoly_comp_neg_X a j) hjred hnoeven
  exact h (j + 1) (by lia) (by lia) (isSquare_cSeq_of_even_factorization a hgdeg hgeq)

/-- Corollary 1.3: all `f_n` (`n ≥ 1`) are irreducible over `ℚ`. -/
theorem irreducible_iteratedPoly_of_pos (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    Irreducible (fℚ[a, n]) :=
  irreducible_iteratedPoly_of_not_isSquare_cSeq a hn fun _ hk1 _ ↦ not_isSquare_cSeq a ha hk1

/-- All `f_n` (including `f_0 = X`) are irreducible over `ℚ` when `-a` is not a square in `ℚ`;
this extends `irreducible_iteratedPoly_of_pos` to `n = 0`. -/
theorem irreducible_iteratedPoly (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) : Irreducible (fℚ[a, n]) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using irreducible_X (R := ℚ)
  · exact irreducible_iteratedPoly_of_pos a ha hn

/-- If `-a = r ^ 2` in `ℚ`, then `f_n = f_{n-1} ^ 2 + a = (f_{n-1} - r) * (f_{n-1} + r)` factors
nontrivially, so irreducibility of any `f_n` with `n ≥ 1` implies that `-a` is not a square.
This recovers the standing assumption of the paper from the irreducibility hypothesis of
Lemma 1.6. -/
theorem not_isSquare_neg_of_irreducible {n : ℕ} (hn : 1 ≤ n) (hirr : Irreducible (fℚ[a, n])) :
    ¬IsSquare (-a : ℚ) := by
  intro ⟨r, hr⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  have hfac : fℚ[a, m + 1] = (fℚ[a, m] - C r) * (fℚ[a, m] + C r) := by
    rw [iteratedPoly_succ, show (a : ℚ) = -(r * r) by linear_combination -hr, map_neg, map_mul]
    ring
  have hdeg : (fℚ[a, m]).natDegree = 2 ^ m := natDegree_iteratedPoly _ m
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · exact not_isUnit_of_natDegree_pos _ (by rw [natDegree_sub_C, hdeg]; positivity) hu
  · exact not_isUnit_of_natDegree_pos _ (by rw [natDegree_add_C, hdeg]; positivity) hu

lemma sub_intCast_ne_zero_of_mem_rootSet (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n)
    {β : AlgebraicClosure ℚ} (hβ : β ∈ (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :
    β - (a : AlgebraicClosure ℚ) ≠ 0 := by
  intro hzero
  have hβa : β = (a : AlgebraicClosure ℚ) := sub_eq_zero.mp hzero
  have hroot : (aeval (a : AlgebraicClosure ℚ)) (fℚ[a, n]) = 0 :=
    hβa ▸ aeval_eq_zero_of_mem_rootSet hβ
  rw [aeval_intCast_iteratedPoly] at hroot
  have hevalZ : (iteratedPoly a n).eval a = 0 := mod_cast hroot
  have hpos : 0 < cSeq a (n + 1) := cSeq_pos a ha (by lia)
  rw [cSeq_succ_eq_neg_one_pow_mul_eval a n, hevalZ, mul_zero] at hpos
  exact absurd hpos (lt_irrefl 0)

lemma splittingField_one_eq_bot_of_isSquare (ha : IsSquare (-a : ℚ)) : splittingField a 1 = ⊥ := by
  obtain ⟨b, hb⟩ := ha
  refine IntermediateField.adjoin_eq_bot_iff.mpr fun β hβ ↦ ?_
  have haeval : (aeval β) (X ^ 2 + C (a : ℚ)) = 0 := by
    simpa [iteratedPoly_one] using aeval_eq_zero_of_mem_rootSet hβ
  have hsq : β ^ 2 = (algebraMap ℚ (AlgebraicClosure ℚ) b) ^ 2 := by
    have hneg : β ^ 2 = -(algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) := by
      simp only [map_add, map_pow, aeval_X, aeval_C] at haeval
      linear_combination haeval
    rw [hneg, ← map_neg, hb, map_mul, sq]
  rw [SetLike.mem_coe, IntermediateField.mem_bot]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact ⟨b, h.symm⟩
  · exact ⟨-b, by rw [map_neg]; exact h.symm⟩

lemma relfinrank_le_two_pow {m n : ℕ} (hmn : m ≤ n) :
    (splittingField a m).relfinrank (splittingField a n) ≤ 2 ^ (2 ^ n - 2 ^ m) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [IntermediateField.relfinrank_self]
  | succ k hk ih =>
    rw [← IntermediateField.relfinrank_mul_relfinrank (splittingField_mono a hk)
      (splittingField_le_succ a k)]
    refine (Nat.mul_le_mul ih (relfinrank_succ_le a k)).trans ?_
    rw [← pow_add, ← Nat.sub_add_comm (Nat.pow_le_pow_right Nat.zero_lt_two hk), pow_succ, mul_two]

lemma not_isSquare_neg_of_finrank_eq {n : ℕ} (hn : 1 ≤ n)
    (hmax : Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1)) :
    ¬IsSquare (-a : ℚ) := by
  intro ha
  have hbot : splittingField a 1 = ⊥ := splittingField_one_eq_bot_of_isSquare a ha
  have hle : splittingField a 1 ≤ splittingField a n := splittingField_mono a hn
  have htower := IntermediateField.finrank_bot_mul_relfinrank hle
  rw [hbot, IntermediateField.finrank_bot, one_mul] at htower
  have hbound : (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).relfinrank (splittingField a n)
      ≤ 2 ^ (2 ^ n - 2) := by
    have hb := relfinrank_le_two_pow a hn
    rw [hbot] at hb
    simpa [pow_one] using hb
  rw [htower, hmax] at hbound
  have hexp : 2 ^ n - 1 ≤ 2 ^ n - 2 := (Nat.pow_le_pow_iff_right one_lt_two).mp hbound
  have h2n : 2 ≤ 2 ^ n := by
    simpa [pow_one] using Nat.pow_le_pow_right two_pos hn
  lia

lemma card_rootSet_iteratedPoly {n : ℕ} (hirr : Irreducible (fℚ[a, n])) :
    Fintype.card ↑((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
      = 2 ^ n := by
  simpa [natDegree_iteratedPoly] using
    card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _)

end

end QuadraticIterates
