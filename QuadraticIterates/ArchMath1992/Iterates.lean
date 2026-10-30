/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Sequences
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Galois.TwoIndependent

import QuadraticIterates.Galois.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Sequence.Valuation

/-!
# The iterates of `X² + a` for an integer `a`

The integer material of Section 1 of the paper, on top of the iterates `f_n`, the sequence
`(c_n)` and the Galois groups `Ω_n` of `QuadraticIterates.iteratedPoly`, `QuadraticIterates.cSeq`
and `QuadraticIterates.GaloisGroup`, which are defined for any coefficient ring.

For an integer `a`, `(c_n)` is a strong divisibility sequence (`QuadraticIterates.cSeq_gcd`).
When `-a` is not a square, `|c_n| ≥ |a|` and `c_n > 0` for `n ≥ 2` (Lemma 1.1 a),
`QuadraticIterates.cSeq_pos`), so `c_{n+1} = c_n² + a` lies strictly between consecutive squares
and no `c_n` is a square (`QuadraticIterates.not_isSquare_cSeq`); hence every `f_n` is irreducible
over `ℚ` (Corollary 1.3, `QuadraticIterates.irreducible_iteratedPoly`), and conversely an
irreducible `f_n` with `n ≥ 1` forces `-a` to be a non-square
(`QuadraticIterates.not_isSquare_neg_of_irreducible`). The rescaling `normPoly a = |a| X² + sign a`
of `X² + a` has the `γ`-sequence `|c_n| / |a|` used in Section 3. A pairwise coprime family of
integers is 2-independent iff none of its members is a square and at most one of their negatives
is (`QuadraticIterates.twoIndependent_iff_of_pairwise_isCoprime`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244, along the paper's own route; see
`QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-! ### The sequence `c` over `ℤ` -/

/-- **Strong divisibility** for the `c`-sequence: `gcd (c_m) (c_n) = |c_{gcd m n}|`. -/
theorem cSeq_gcd (a : ℤ) (m n : ℕ) : Int.gcd (cSeq a m) (cSeq a n) = (cSeq a (m.gcd n)).natAbs :=
  gammaSeq_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

/-- Strong divisibility of the `c`-sequence in the `Associated`-of-`gcd` form consumed by the
`moebiusFactorR` API. -/
theorem cSeq_associated_gcd (a : ℤ) (m n : ℕ) :
    Associated (gcd (cSeq a m) (cSeq a n)) (cSeq a (m.gcd n)) :=
  gammaSeq_associated_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

section

variable {a : ℤ}

/-- If `-a` is not a rational square then `a ≠ 0`, since `-0` is. -/
lemma ne_zero_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ 0 := fun h ↦ ha (by simp [h])

private lemma ne_neg_one_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : a ≠ -1 :=
  fun h ↦ ha (by simp [h])

/-- `QuadraticIterates.cSeq_ne_zero` for an integer `a` with `-a` not a square. -/
theorem cSeq_intCast_ne_zero_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) :
    ∀ n ≥ 1, cSeq (a : ℚ) n ≠ 0 :=
  fun _ ↦ cSeq_ne_zero (mod_cast ne_zero_of_not_isSquare_neg ha)
    (mod_cast ne_neg_one_of_not_isSquare_neg ha)

theorem cSeq_ne_zero_of_not_isSquare_neg (ha : ¬IsSquare (-a : ℚ)) : ∀ n ≥ 1, cSeq a n ≠ 0 :=
  fun n hn h ↦ cSeq_intCast_ne_zero_of_not_isSquare_neg ha n hn (by simp [← intCast_cSeq, h])

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

/-- No `c_n` (`n ≥ 1`) is a rational square: `c_{n+1} = c_n² + a` lies strictly between two
consecutive squares because `|c_n| ≥ |a|`, and `c_1 = -a` is not a square by assumption. -/
theorem not_isSquare_cSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    ¬IsSquare (cSeq a n : ℚ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by lia : n ≠ 0)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using ha
  · rw [← intCast_cSeq, Rat.isSquare_intCast_iff, cSeq_succ a hm]
    exact not_isSquare_sq_add_of_abs_le_abs (ne_zero_of_not_isSquare_neg ha)
      (ne_neg_one_of_not_isSquare_neg ha) (abs_le_abs_cSeq ha hm)

/-! ### Irreducibility of the iterates -/

/-- Corollary 1.3: all `f_n` are irreducible over `ℚ` (including `f_0 = X`). -/
theorem irreducible_iteratedPoly (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) : Irreducible fℚ[a, n] :=
  irreducible_iteratedPoly_of_not_isSquare_cSeq fun _ hk _ ↦ not_isSquare_cSeq ha hk

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

end

/-! ### The rescaled polynomial -/

/-- The rescaling `|a|·X² + sign a` of `X² + a`. Substituting `x ↦ |a|·x` turns the recursion
`c_{n+1} = c_n² + a` into the `γ`-recursion of `normPoly a`, whose sequence is therefore
`|c_n| / |a|` (`QuadraticIterates.abs_cSeq_eq_gammaSeq_mul_abs`) — in particular positive, which is
what Lemma 2.2 needs and `X² + a` itself does not provide. -/
noncomputable def normPoly (a : ℤ) : ℤ[X] := C |a| * X ^ 2 + C a.sign

@[simp] lemma eval_normPoly (a x : ℤ) : (normPoly a).eval x = |a| * x ^ 2 + a.sign := by
  simp [normPoly]

lemma evenPoly_normPoly (a : ℤ) : EvenPoly (normPoly a) := evenPoly_C_mul_X_sq_add_C |a| a.sign

/-! ### 2-independence -/

section TwoIndependent

variable {ι : Type*}

theorem twoIndependent_intCast_iff (f : ι → ℤ) :
    TwoIndependent (fun i ↦ (f i : ℚ)) ↔ TwoIndependent f :=
  congr(∀ S : Finset ι, S.Nonempty → ¬$(Int.cast_prod (R := ℚ) f S ▸ Rat.isSquare_intCast_iff))

open Function in
/-- A pairwise coprime family of integers is 2-independent iff none of its members is a square and
at most one of their negatives is. -/
theorem twoIndependent_iff_of_pairwise_isCoprime {f : ι → ℤ} (hf : Pairwise (IsCoprime on f)) :
    TwoIndependent f ↔ (∀ i, ¬IsSquare (f i)) ∧ {i | IsSquare (-f i)}.Subsingleton := by
  classical
  refine ⟨fun h ↦ ⟨h.not_isSquare, fun i hi j hj ↦ by_contra fun hij ↦
    h {i, j} (Finset.insert_nonempty _ _) ?_⟩, fun ⟨hsq, hsub⟩ S hS hprod ↦ ?_⟩
  · rw [Finset.prod_pair hij, ← neg_mul_neg]
    exact hi.mul hj
  · have hneg (i : ι) (hi : i ∈ S) : IsSquare (-f i) :=
      (isSquare_abs_iff.mp (Int.isSquare_abs_of_isSquare_prod_of_pairwise_isCoprime
        (hf.set_pairwise _) hprod hi)).resolve_left (hsq i)
    obtain ⟨i, hi⟩ := hS
    rw [Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨i, hi⟩, fun j hj ↦
      hsub (hneg j hj) (hneg i hi)⟩, Finset.prod_singleton] at hprod
    exact hsq i hprod

end TwoIndependent

end QuadraticIterates
