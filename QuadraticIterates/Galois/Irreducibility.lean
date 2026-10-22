/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Galois.Iterates

import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp

/-!
# Irreducibility of the iterates over `ℚ`

For a rational parameter `a`, `f_{n+1} = f_n ∘ (X² + a)` is even, and when `f_n` is irreducible it
has no nontrivial even divisor; so a factorization of `f_{n+1}` has the shape
`g · g(-X) = ± f_{n+1}` (`Polynomial.Monic.exists_mul_comp_neg_X_eq_of_not_irreducible`), and
evaluation at `0` exhibits `c_{n+1}` as a square (Lemma 1.2 of [Stoll 1992]). The consequences for
the roots of an irreducible `f_n` that the degree criterion needs close the file.

## Main statements

* `QuadraticIterates.irreducible_iteratedPoly_succ_of_not_isSquare`: if `f_n` is irreducible and
  `c_{n+1}` is not a square in `ℚ`, then `f_{n+1}` is irreducible.
* `QuadraticIterates.irreducible_iteratedPoly_of_not_isSquare_cSeq` (Lemma 1.2 of [Stoll 1992]): if
  none of `c_1, …, c_n` is a square in `ℚ`, then `f_n` is irreducible.

## References

* M. Stoll, *Galois groups over ℚ of some iterated polynomials*, Arch. Math. **59** (1992),
  239-244.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable {a : ℚ}

/-! ### Irreducibility of the iterates -/

/-- If `f_{j+1}` factors over `ℚ` as `g * g(-X) = C ((-1)^{deg g}) * f_{j+1}` with
`deg f_{j+1} = 2 · deg g`, then evaluation at `0` exhibits `c_{j+1}` as a square in `ℚ`. -/
private lemma isSquare_cSeq_of_even_factorization {j : ℕ} {g : ℚ[X]}
    (hgdeg : 2 * g.natDegree = fℚ[a, j + 1].natDegree)
    (hgeq : g * g.comp (-X) = C ((-1 : ℚ) ^ g.natDegree) * fℚ[a, j + 1]) :
    IsSquare (cSeq a (j + 1)) := by
  have hgnd : g.natDegree = 2 ^ j := by grind [natDegree_iteratedPoly]
  have heval := congr(eval 0 $hgeq)
  simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_zero] at heval
  exact ⟨g.eval 0, by rw [cSeq_succ_eq_neg_one_pow_mul_eval_zero, ← hgnd, heval]⟩

/-- Lemma 1.2 of [Stoll 1992], one step: if `f_n` is irreducible over `ℚ` and `c_{n+1}` is not a
square, then `f_{n+1}` is irreducible. `f_{n+1} = f_n ∘ (X² + a)` is even and, `f_n` being
irreducible, has no nontrivial even divisor, so a factorization would have the shape
`g · g(-X) = ± f_{n+1}`, and evaluation at `0` would exhibit `c_{n+1}` as a square. -/
theorem irreducible_iteratedPoly_succ_of_not_isSquare {n : ℕ} (hirr : Irreducible fℚ[a, n])
    (hc : ¬IsSquare (cSeq a (n + 1))) : Irreducible fℚ[a, n + 1] := by
  have hF0 : fℚ[a, n].eval a ≠ 0 := fun h0 ↦ hc (by simp [cSeq_succ_eq_neg_one_pow_mul_eval, h0])
  by_contra hred
  obtain ⟨g, hgdeg, hgeq⟩ :=
    (monic_iteratedPoly a (n + 1)).exists_mul_comp_neg_X_eq_of_not_irreducible
      (iteratedPoly_succ_comp_neg_X a n) hred fun _ ↦ iteratedPoly_succ_comp a n ▸
        hirr.isUnit_or_associated_of_dvd_comp_of_associated_comp_neg_X hF0
  exact hc (isSquare_cSeq_of_even_factorization hgdeg hgeq)

/-- Lemma 1.2 of [Stoll 1992]: if none of `c_1, …, c_n` is a square in `ℚ`, then `f_n` is
irreducible over `ℚ`. -/
theorem irreducible_iteratedPoly_of_not_isSquare_cSeq {n : ℕ}
    (h : ∀ k ≥ 1, k ≤ n → ¬IsSquare (cSeq a k)) : Irreducible fℚ[a, n] := by
  induction n with
  | zero => simpa using irreducible_X (R := ℚ)
  | succ n ih =>
    exact irreducible_iteratedPoly_succ_of_not_isSquare
      (ih fun k hk hkn ↦ h k hk (hkn.trans n.le_succ)) (h (n + 1) n.succ_pos le_rfl)

/-! ### Consequences for the roots of `f_n` -/

/-- `c_{n+1} = ± f_{n+1}(0)` is nonzero when `f_{n+1}` is irreducible: otherwise `X` would divide
`f_{n+1}`. -/
lemma cSeq_succ_ne_zero_of_irreducible {n : ℕ} (hirr : Irreducible fℚ[a, n + 1]) :
    cSeq a (n + 1) ≠ 0 := fun h ↦
  hirr.not_isRoot_of_natDegree_ne_one
    (natDegree_iteratedPoly a (n + 1) ▸ (Nat.one_lt_two_pow n.succ_ne_zero).ne')
    (by simpa [cSeq_succ_eq_neg_one_pow_mul_eval_zero] using h)

/-- `a` is not a root of `f_n` when `c_{n+1} = ± f_n(a) ≠ 0`: the shifted roots `β - a` of `f_n`,
whose square roots generate `K_{n+1}` over `K_n`, are nonzero. -/
lemma sub_ratCast_ne_zero_of_mem_rootSet {n : ℕ} (hc : cSeq a (n + 1) ≠ 0)
    {β : AlgebraicClosure ℚ} (hβ : β ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ)) :
    β - (a : AlgebraicClosure ℚ) ≠ 0 := fun hzero ↦ by
  have hroot := aeval_eq_zero_of_mem_rootSet hβ
  rw [sub_eq_zero.mp hzero, aeval_ratCast_iteratedPoly, Rat.cast_eq_zero] at hroot
  exact hc (by rw [cSeq_succ_eq_neg_one_pow_mul_eval, hroot, mul_zero])

/-- An irreducible `f_n` is separable, so it has exactly `2^n = deg f_n` roots in `ℚ̄`. -/
lemma card_rootSet_iteratedPoly {n : ℕ} (hirr : Irreducible fℚ[a, n]) :
    Fintype.card ↑(fℚ[a, n].rootSet (AlgebraicClosure ℚ)) = 2 ^ n := by
  simpa [natDegree_iteratedPoly] using
    card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _)

end

end QuadraticIterates
