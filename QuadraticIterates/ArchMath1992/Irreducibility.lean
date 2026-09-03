/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates

import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Squares

/-!
# Irreducibility of the iterates over `ℚ`

If none of `c_1, …, c_n` is a rational square, then `f_n` is irreducible over `ℚ` (Lemma 1.2,
`irreducible_iteratedPoly_of_not_isSquare_cSeq`): `f_{n+1} = f_n ∘ (X² + a)` is even and, `f_n`
being irreducible, has no nontrivial even divisor, so a factorization of it would have the shape
`g · g(-X) = ± f_{n+1}` (`Polynomial.Monic.exists_mul_comp_neg_X_eq_of_not_irreducible`) and
exhibit `c_{n+1} = ± f_{n+1}(0)` as a square. Since `|c_n| ≥ |a|` places `c_{n+1} = c_n² + a`
strictly between consecutive squares, no `c_n` is a square when `-a` is not one, and every `f_n`
is irreducible (Corollary 1.3, `irreducible_iteratedPoly`); conversely, irreducibility of a single
`f_n` with `n ≥ 1` already forces `-a` to be a non-square (`not_isSquare_neg_of_irreducible`). The
consequences for the roots of `f_n` needed by the degree criterion
(`sub_intCast_ne_zero_of_mem_rootSet`, `card_rootSet_iteratedPoly`) close the file.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

/-! ### The numbers `c_n`: size, positivity and non-squareness -/

/-- If `-a` is not a rational square then `a ≠ 0`, since `-0` is. -/
lemma ne_zero_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ 0 := fun h ↦ ha (by simp [h])

private lemma ne_neg_one_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ -1 :=
  fun h ↦ ha (by simp [h])

private lemma abs_le_sq_add_of_abs_le_abs {b d : ℤ} (hb : b ≠ -1) (h : |b| ≤ |d|) :
    |b| ≤ d ^ 2 + b := by
  rcases abs_cases b with ⟨he, -⟩ | ⟨he, hb0⟩ <;> rw [he] at h ⊢
  · nlinarith [sq_nonneg d]
  · nlinarith [sq_abs d, mul_le_mul h h (by lia) (abs_nonneg d), (by lia : b ≤ -2)]

private lemma not_isSquare_sq_add_of_abs_le_abs {b d : ℤ} (hb0 : b ≠ 0) (hb1 : b ≠ -1)
    (h : |b| ≤ |d|) : ¬IsSquare (d ^ 2 + b) := by
  rcases lt_or_gt_of_ne hb0 with hb | hb
  · rw [abs_of_neg hb] at h
    have hb2 : b ≤ -2 := by lia
    refine Int.not_isSquare_of_sq_lt_of_lt_sq (|d| - 1) ?_ ?_ <;> nlinarith [sq_abs d]
  · rw [abs_of_pos hb] at h
    refine Int.not_isSquare_of_sq_lt_of_lt_sq |d| ?_ ?_ <;> nlinarith [sq_abs d]

/-- `|c_n| ≥ |a|` for all `n ≥ 1` (the observation in the proof of Corollary 1.3). -/
theorem abs_le_abs_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : |a| ≤ |cSeq a n| := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    exact cSeq_succ a hk ▸
      (abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg a ha) ih).trans (le_abs_self _)

/-- `c_n ≥ |a|` for all `n ≥ 2`. -/
theorem abs_le_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : |a| ≤ cSeq a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rw [cSeq_succ a (by lia)]
  exact abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg a ha)
    (abs_le_abs_cSeq a ha (by lia))

/-- Lemma 1.1 a): `c_n > 0` for all `n ≥ 2`. -/
theorem cSeq_pos (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : 0 < cSeq a n :=
  (abs_pos.mpr (ne_zero_of_not_isSquare_neg a ha)).trans_le (abs_le_cSeq a ha hn)

/-- `c_n ≠ 0` for `n ≥ 1`, since `|c_n| ≥ |a| > 0`. -/
theorem cSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : cSeq a n ≠ 0 := fun h ↦
  ne_zero_of_not_isSquare_neg a ha (by simpa [h] using abs_le_abs_cSeq a ha hn)

/-- No `c_n` (`n ≥ 1`) is a rational square: `c_{n+1} = c_n² + a` lies strictly between two
consecutive squares because `|c_n| ≥ |a|`, and `c_1 = -a` is not a square by assumption. -/
theorem not_isSquare_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    ¬IsSquare (cSeq a n : ℚ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using ha
  · rw [Rat.isSquare_intCast_iff, cSeq_succ a hm]
    exact not_isSquare_sq_add_of_abs_le_abs (ne_zero_of_not_isSquare_neg a ha)
      (ne_neg_one_of_not_isSquare_neg a ha) (abs_le_abs_cSeq a ha hm)

/-! ### Irreducibility of the iterates -/

/-- If `f_{j+1}` factors over `ℚ` as `g * g(-X) = C ((-1)^{deg g}) * f_{j+1}` with
`deg f_{j+1} = 2 · deg g`, then evaluation at `0` exhibits `c_{j+1}` as a square in `ℚ`. -/
private lemma isSquare_cSeq_of_even_factorization {j : ℕ} {g : ℚ[X]}
    (hgdeg : 2 * g.natDegree = fℚ[a, j + 1].natDegree)
    (hgeq : g * g.comp (-X) = C ((-1 : ℚ) ^ g.natDegree) * fℚ[a, j + 1]) :
    IsSquare (cSeq a (j + 1) : ℚ) := by
  have hgnd : g.natDegree = 2 ^ j := by grind [natDegree_iteratedPoly]
  have heval := congrArg (eval 0) hgeq
  simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_zero] at heval
  exact ⟨g.eval 0, by rw [intCast_cSeq_succ_eq_neg_one_pow_mul_eval_zero, ← hgnd]; exact heval.symm⟩

/-- Lemma 1.2: if none of `c_1, …, c_n` is a square in `ℚ`, then `f_n` is irreducible over `ℚ`.
By induction: `f_{n+1} = f_n ∘ (X² + a)` is even and, `f_n` being irreducible, has no nontrivial
even divisor, so if it were reducible, `c_{n+1}` would be a square. -/
theorem irreducible_iteratedPoly_of_not_isSquare_cSeq {n : ℕ}
    (h : ∀ k ≥ 1, k ≤ n → ¬IsSquare (cSeq a k : ℚ)) : Irreducible fℚ[a, n] := by
  induction n with
  | zero => simpa using irreducible_X (R := ℚ)
  | succ n ih =>
    have hn := h (n + 1) n.succ_pos le_rfl
    have hF0 : fℚ[a, n].eval (a : ℚ) ≠ 0 := fun h0 ↦ hn (by
      simp [intCast_cSeq_succ_eq_neg_one_pow_mul_eval_zero, eval_zero_iteratedPoly_succ, h0])
    have hirr := ih fun k hk hkn ↦ h k hk (hkn.trans n.le_succ)
    by_contra hred
    obtain ⟨g, hgdeg, hgeq⟩ :=
      (monic_iteratedPoly (a : ℚ) (n + 1)).exists_mul_comp_neg_X_eq_of_not_irreducible
        (iteratedPoly_succ_comp_neg_X (a : ℚ) n) hred fun _ ↦ by
          rw [iteratedPoly_succ_comp]
          exact hirr.isUnit_or_associated_of_dvd_comp_of_associated_comp_neg_X hF0
    exact hn (isSquare_cSeq_of_even_factorization a hgdeg hgeq)

/-- Corollary 1.3: all `f_n` are irreducible over `ℚ` (including `f_0 = X`). -/
theorem irreducible_iteratedPoly (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) : Irreducible fℚ[a, n] :=
  irreducible_iteratedPoly_of_not_isSquare_cSeq a fun _ hk _ ↦ not_isSquare_cSeq a ha hk

/-- If `-a = r ^ 2` in `ℚ`, then `f_n = f_{n-1} ^ 2 + a = (f_{n-1} - r) * (f_{n-1} + r)` factors
nontrivially, so irreducibility of any `f_n` with `n ≥ 1` implies that `-a` is not a square.
This recovers the standing assumption of the paper from the irreducibility hypothesis of
Lemma 1.6. -/
theorem not_isSquare_neg_of_irreducible {n : ℕ} (hn : 1 ≤ n) (hirr : Irreducible fℚ[a, n]) :
    ¬IsSquare (-a : ℚ) := by
  intro ⟨r, hr⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  have hfac : fℚ[a, m + 1] = (fℚ[a, m] - C r) * (fℚ[a, m] + C r) := by
    rw [iteratedPoly_succ, neg_eq_iff_eq_neg.mp hr, map_neg, map_mul]
    ring
  refine (hirr.isUnit_or_isUnit hfac).elim ?_ ?_ <;>
    exact not_isUnit_of_natDegree_pos _ (by simp [natDegree_iteratedPoly])

/-! ### Consequences for the roots of `f_n` -/

/-- `a` is not a root of `f_n`, because `f_n(a) = ± c_{n+1} ≠ 0`: the shifted roots `β - a` of
`f_n`, whose square roots generate `K_{n+1}` over `K_n`, are nonzero. -/
lemma sub_intCast_ne_zero_of_mem_rootSet (ha : ¬IsSquare (-a : ℚ)) {n : ℕ}
    {β : AlgebraicClosure ℚ} (hβ : β ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ)) :
    β - (a : AlgebraicClosure ℚ) ≠ 0 := by
  intro hzero
  have hroot := aeval_eq_zero_of_mem_rootSet hβ
  rw [sub_eq_zero.mp hzero, aeval_intCast_iteratedPoly, Int.cast_eq_zero] at hroot
  exact cSeq_ne_zero a ha n.succ_pos (by rw [cSeq_succ_eq_neg_one_pow_mul_eval, hroot, mul_zero])

/-- An irreducible `f_n` is separable, so it has exactly `2^n = deg f_n` roots in `ℚ̄`. -/
lemma card_rootSet_iteratedPoly {n : ℕ} (hirr : Irreducible fℚ[a, n]) :
    Fintype.card ↑(fℚ[a, n].rootSet (AlgebraicClosure ℚ)) = 2 ^ n := by
  simpa [natDegree_iteratedPoly] using
    card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _)

end

end QuadraticIterates
