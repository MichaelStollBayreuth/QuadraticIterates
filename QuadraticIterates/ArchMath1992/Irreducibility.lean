/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates
public import QuadraticIterates.Galois.Irreducibility

import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Squares

/-!
# Irreducibility of the iterates for an integer parameter

For an integer `a`, `|c_n| ≥ |a|` places `c_{n+1} = c_n² + a` strictly between consecutive
squares, so no `c_n` is a square when `-a` is not one, and every `f_n` is irreducible over `ℚ`
(Corollary 1.3, `QuadraticIterates.irreducible_iteratedPoly`, from Lemma 1.2,
`QuadraticIterates.irreducible_iteratedPoly_of_not_isSquare_cSeq`); conversely, irreducibility of a
single `f_n` with `n ≥ 1` already forces `-a` to be a non-square
(`QuadraticIterates.not_isSquare_neg_of_irreducible`, for a rational `a`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable {a : ℤ}

/-! ### The integers `c_n`: size, positivity and non-squareness -/

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
      (abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg ha) ih).trans (le_abs_self _)

theorem abs_le_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : |a| ≤ cSeq a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rw [cSeq_succ a (by lia)]
  exact abs_le_sq_add_of_abs_le_abs (ne_neg_one_of_not_isSquare_neg ha)
    (abs_le_abs_cSeq ha (by lia))

/-- Lemma 1.1 a): `c_n > 0` for all `n ≥ 2`. -/
theorem cSeq_pos (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) : 0 < cSeq a n :=
  (abs_pos.mpr (ne_zero_of_not_isSquare_neg ha)).trans_le (abs_le_cSeq ha hn)

/-- `c_n ≠ 0` for `n ≥ 1`, since `|c_n| ≥ |a| > 0`. -/
theorem cSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) : ∀ n ≥ 1, cSeq a n ≠ 0 := fun _ hn h ↦
  ne_zero_of_not_isSquare_neg ha (by simpa [h] using abs_le_abs_cSeq ha hn)

/-- The sequence `c` of the integer parameter `a` taken in `ℚ` does not vanish either: it is the
cast of the integer sequence (`QuadraticIterates.intCast_cSeq`). -/
theorem cSeq_intCast_ne_zero (ha : ¬IsSquare (-a : ℚ)) : ∀ n ≥ 1, cSeq (a : ℚ) n ≠ 0 :=
  fun n hn ↦ by
  rw [← intCast_cSeq]
  exact Int.cast_ne_zero.mpr (cSeq_ne_zero ha n hn)

/-- No `c_n` (`n ≥ 1`) is a rational square: `c_{n+1} = c_n² + a` lies strictly between two
consecutive squares because `|c_n| ≥ |a|`, and `c_1 = -a` is not a square by assumption. -/
theorem not_isSquare_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    ¬IsSquare (cSeq (a : ℚ) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using ha
  · rw [← intCast_cSeq, Rat.isSquare_intCast_iff, cSeq_succ a hm]
    exact not_isSquare_sq_add_of_abs_le_abs (ne_zero_of_not_isSquare_neg ha)
      (ne_neg_one_of_not_isSquare_neg ha) (abs_le_abs_cSeq ha hm)

end

section

variable {a : ℚ}

/-- If `-a = r ^ 2` in `ℚ`, then `f_n = f_{n-1} ^ 2 + a = (f_{n-1} - r) * (f_{n-1} + r)` factors
nontrivially, so irreducibility of any `f_n` with `n ≥ 1` implies that `-a` is not a square. -/
theorem not_isSquare_neg_of_irreducible {n : ℕ} (hn : 1 ≤ n) (hirr : Irreducible fℚ[a, n]) :
    ¬IsSquare (-a) := by
  intro ⟨r, hr⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  have hfac : fℚ[a, m + 1] = (fℚ[a, m] - C r) * (fℚ[a, m] + C r) := by
    rw [iteratedPoly_succ, neg_eq_iff_eq_neg.mp hr, map_neg, map_mul]
    ring
  refine (hirr.isUnit_or_isUnit hfac).elim ?_ ?_ <;>
    exact not_isUnit_of_natDegree_pos _ (by simp [natDegree_iteratedPoly])

lemma cSeq_ne_zero_of_irreducible (hirr : ∀ k, Irreducible fℚ[a, k]) : ∀ n ≥ 1, cSeq a n ≠ 0 :=
  fun n hn ↦ by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  exact cSeq_succ_ne_zero_of_irreducible (hirr (m + 1))
end

/-- Corollary 1.3: for an integer `a` with `-a` not a square, all `f_n` are irreducible over `ℚ`
(including `f_0 = X`). -/
theorem irreducible_iteratedPoly {a : ℤ} (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    Irreducible fℚ[a, n] :=
  irreducible_iteratedPoly_of_not_isSquare_cSeq fun _ hk _ ↦ not_isSquare_cSeq ha hk

end QuadraticIterates

end
