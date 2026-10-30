/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Galois.TwoIndependent

import QuadraticIterates.Galois.DegreeCriterion
import QuadraticIterates.Galois.Irreducibility
import QuadraticIterates.Galois.Tower

/-!
# Stoll's criterion

For every rational `a` and every `n`, `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent; hence the
arboreal Galois representation of `X² + a` is surjective iff the whole sequence `(c_n)_{n ≥ 1}` is
2-independent. The direction `⇐`, and `⇒` for irreducible iterates, is Section 1 of
[Stoll 1992]; that `Ω_n ≅ [C₂]ⁿ` forces `f_0, …, f_n` to be irreducible makes the criterion
unconditional.

## Main statements

* `QuadraticIterates.nonempty_mulEquiv_iff_twoIndependent_of_irreducible`: the criterion when
  `f_0, …, f_n` are irreducible.
* `QuadraticIterates.irreducible_iteratedPoly_of_nonempty_mulEquiv`: if `Ω_n ≅ [C₂]ⁿ`, then
  `f_0, …, f_n` are irreducible.
* `QuadraticIterates.nonempty_mulEquiv_iff_twoIndependent`: the criterion for every rational `a`.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent`: the infinite version; the
  arboreal Galois representation of `X² + a` is surjective iff `(c_n)_{n ≥ 1}` is 2-independent.

## References

* M. Stoll, *Galois groups over ℚ of some iterated polynomials*, Arch. Math. **59** (1992),
  239-244.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable {a : ℚ}

/-- Section 1 of [Stoll 1992], `(a) ↔ (b)`, for a rational parameter `a` whose iterates
`f_0, …, f_n` are irreducible: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent. By induction on
`n`: `Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}`
(`QuadraticIterates.nonempty_mulEquiv_succ_iff`, Lemma 1.4 of [Stoll 1992]), the degree condition
says that `c_{n+1}` is not a square in `K_n` (`QuadraticIterates.relfinrank_succ_eq_two_pow_iff`,
Lemma 1.6 of [Stoll 1992], which needs `f_n` irreducible and `c_{n+1} ≠ 0`, the latter as
`f_{n+1}` is irreducible), and given `Ω_n ≅ [C₂]ⁿ` this means that `c_1, …, c_{n+1}` are
2-independent (`QuadraticIterates.not_isSquare_algebraMap_iff_twoIndependent_snoc`, Lemma 1.5 of
[Stoll 1992]). -/
theorem nonempty_mulEquiv_iff_twoIndependent_of_irreducible {n : ℕ}
    (hirr : ∀ k ≤ n, Irreducible fℚ[a, k]) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent fun i : Fin n ↦ cSeq a ((i : ℕ) + 1) := by
  induction n with
  | zero =>
    exact ⟨fun _ S ⟨i, _⟩ ↦ i.elim0, fun _ ↦ (nonempty_mulEquiv_iff_finrank_eq a 0).mpr (by simp)⟩
  | succ n ih =>
    have ih := ih fun k hk ↦ hirr k (hk.trans n.le_succ)
    have h16 := relfinrank_succ_eq_two_pow_iff (hirr n n.le_succ)
      (cSeq_succ_ne_zero_of_irreducible (hirr (n + 1) le_rfl))
    rw [← Fin.snoc_init_self (fun i : Fin (n + 1) ↦ cSeq a ((i : ℕ) + 1)),
      nonempty_mulEquiv_succ_iff a n]
    refine ⟨fun ⟨hiso, hrel⟩ ↦ ?_, fun h ↦ ?_⟩
    · exact (not_isSquare_algebraMap_iff_twoIndependent_snoc hiso (ih.mp hiso)).mp (h16.mp hrel)
    · have hiso := ih.mpr h.of_snoc
      exact ⟨hiso, h16.mpr ((not_isSquare_algebraMap_iff_twoIndependent_snoc hiso h.of_snoc).mpr h)⟩

/-- If `f_n` is irreducible and `[K_{n+1} : K_n] = 2^{2^n}`, then `c_{n+1} ≠ 0`: otherwise `a` is a
rational root of the irreducible `f_n`, so `n = 0` and `a = -c_1 = 0`, but then
`K_1 = K_0 = ℚ`. -/
lemma cSeq_succ_ne_zero_of_relfinrank_eq {n : ℕ} (hirr : Irreducible fℚ[a, n])
    (h : (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n) :
    cSeq a (n + 1) ≠ 0 := fun h0 ↦ by
  have hroot : fℚ[a, n].IsRoot a := by simpa [cSeq_succ_eq_neg_one_pow_mul_eval] using h0
  obtain rfl : n = 0 := by
    by_contra hn
    exact hirr.not_isRoot_of_natDegree_ne_one (by simpa [natDegree_iteratedPoly]) hroot
  obtain rfl : a = 0 := by simpa using h0
  simp at h

/-- If `f_n` is irreducible and `[K_{n+1} : K_n] = 2^{2^n}`, then `f_{n+1}` is irreducible:
otherwise `c_{n+1}` is a square in `ℚ`
(`QuadraticIterates.irreducible_iteratedPoly_succ_of_not_isSquare`), hence in `K_n`, which the
degree criterion `QuadraticIterates.relfinrank_succ_eq_two_pow_iff` rules out. -/
theorem irreducible_iteratedPoly_succ_of_relfinrank_eq {n : ℕ} (hirr : Irreducible fℚ[a, n])
    (h : (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n) :
    Irreducible fℚ[a, n + 1] :=
  irreducible_iteratedPoly_succ_of_not_isSquare hirr fun hsq ↦
    (relfinrank_succ_eq_two_pow_iff hirr (cSeq_succ_ne_zero_of_relfinrank_eq hirr h)).mp h
      (hsq.map _)

/-- If `Ω_n ≅ [C₂]ⁿ`, then `f_0, …, f_n` are irreducible over `ℚ`: by induction, using that
`Ω_{n+1} ≅ [C₂]^{n+1}` forces `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}`
(`QuadraticIterates.nonempty_mulEquiv_succ_iff`). -/
theorem irreducible_iteratedPoly_of_nonempty_mulEquiv {n : ℕ}
    (h : Nonempty (GaloisGroup a n ≃* WreathPower n)) {k : ℕ} (hk : k ≤ n) :
    Irreducible fℚ[a, k] := by
  induction n generalizing k with
  | zero => simpa [Nat.le_zero.mp hk] using irreducible_X (R := ℚ)
  | succ n ih =>
    obtain ⟨hiso, hrel⟩ := (nonempty_mulEquiv_succ_iff a n).mp h
    rcases Nat.le_succ_iff.mp hk with hk | rfl
    · exact ih hiso hk
    · exact irreducible_iteratedPoly_succ_of_relfinrank_eq (ih hiso le_rfl) hrel

/-- The iterates `f_0, …, f_n` are irreducible over `ℚ` when `c_1, …, c_n` are 2-independent, none
of them being a square (Lemma 1.2 of [Stoll 1992]). -/
theorem irreducible_iteratedPoly_of_twoIndependent {n : ℕ}
    (h : TwoIndependent fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)) {k : ℕ} (hk : k ≤ n) :
    Irreducible fℚ[a, k] :=
  irreducible_iteratedPoly_of_not_isSquare_cSeq fun j hj hjk ↦ by
    simpa [Nat.sub_add_cancel hj] using h.not_isSquare ⟨j - 1, by lia⟩

variable (a) in
/-- **Stoll's criterion**: for every rational `a`, `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are
2-independent. Either side forces `f_0, …, f_n` to be irreducible, and then
`QuadraticIterates.nonempty_mulEquiv_iff_twoIndependent_of_irreducible` applies. -/
theorem nonempty_mulEquiv_iff_twoIndependent (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent fun i : Fin n ↦ cSeq a ((i : ℕ) + 1) :=
  ⟨fun h ↦ (nonempty_mulEquiv_iff_twoIndependent_of_irreducible fun _ ↦
      irreducible_iteratedPoly_of_nonempty_mulEquiv h).mp h,
    fun h ↦ (nonempty_mulEquiv_iff_twoIndependent_of_irreducible fun _ ↦
      irreducible_iteratedPoly_of_twoIndependent h).mpr h⟩

variable (a) in
/-- **Stoll's criterion**, infinite version: the arboreal Galois representation of `X² + a` is
surjective, i.e. `Ω_n ≅ [C₂]ⁿ` for all `n`, iff the sequence `(c_n)_{n ≥ 1}` is 2-independent. -/
theorem forall_nonempty_mulEquiv_iff_twoIndependent :
    (∀ n, Nonempty (GaloisGroup a n ≃* WreathPower n)) ↔
      TwoIndependent fun n : ℕ ↦ cSeq a (n + 1) := by
  rw [twoIndependent_iff_forall_fin]
  exact congr(∀ n, $(nonempty_mulEquiv_iff_twoIndependent a n))

end

end QuadraticIterates
