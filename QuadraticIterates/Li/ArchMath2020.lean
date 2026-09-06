/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Li.Residues

import QuadraticIterates.ArchMath1992.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.Int.Order.Units
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# Li, *Arboreal Galois representation for a certain type of quadratic polynomials*

The results of H.-C. Li, Arch. Math. **114** (2020), 265-269, for `a < 0` with `a ≡ 3 mod 4` and
`-a` not a square: `|b_n|` is not a square for all `n ≥ 3` (Theorem 3.4), and `Ω_n ≅ [C₂]ⁿ` for
all `n ≥ 1` if and only if `-a - 1` is not a square (Theorem 3.5). The index-`2` statement of
that paper in the exceptional case (`Ω_n` of index `2` in `[C₂]ⁿ` for all `n ≥ 2` when `-a - 1` is
a square) is not formalized.

## Main statements

* `li2020_theorem_3_4`, `li2020_theorem_3_5`: the two theorems.
* `not_isSquare_abs_bSeq_of_not_squarefree_of_neg_of_emod_four_eq_three` (Lemma 3.1): `n` not
  squarefree, with the modulus `γ_k + γ_{k+1} ≡ 3 mod 4`, `k = n / rad n ≥ 2`.
* `not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_three` (Lemmas 3.2 and 3.3): `n`
  squarefree and `> 2`, with the modulus `γ_2 = -a - 1 ≡ 0 mod 4`.

Part of the formalization of the results of Li extending M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.Li`.
-/

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace QuadraticIterates

variable {a : ℤ}

/-- Lemma 3.1 of [Li 2020]: for `a < 0` with `a ≡ 3 mod 4` and `n ≥ 1` not squarefree, `|b_n|` is
not a square: `k = n / rad n ≥ 2`, and `γ_k + γ_{k+1} ≡ 3 mod 4`. -/
theorem not_isSquare_abs_bSeq_of_not_squarefree_of_neg_of_emod_four_eq_three (ha : a < 0)
    (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) {n : ℕ} (hn : 1 ≤ n) (hsf : ¬Squarefree n) :
    ¬IsSquare |bSeq a n| := by
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast hsq
  have hk₀2 := Nat.two_le_div_radical_of_not_squarefree (by lia) hsf
  have h4 := gammaSeq_normPoly_add_succ_emod_four_eq_three ha ha4 hk₀2
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le
    (a := γ[a] (n / radical n) + γ[a] (n / radical n + 1)) (by
      have := gammaSeq_normPoly_pos ha' (n / radical n) (by lia)
      have := gammaSeq_normPoly_pos ha' (n / radical n + 1) (by lia)
      lia)
  exact not_isSquare_abs_bSeq_of_dvd_add_succ ha' (hk₀2.trans (Nat.div_le_self n _))
    (Nat.div_mul_cancel radical_dvd_self).symm (dvd_of_eq hm.symm)
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three (by lia))

/-- Lemmas 3.2 and 3.3 of [Li 2020]: for `a < 0` with `a ≡ 3 mod 4` and squarefree `n > 2`,
`|b_n|` is not a square (modulo `γ_2 = -a - 1 ≡ 0 mod 4`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_three (ha : a < 0)
    (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) {n : ℕ} (hsf : Squarefree n) (hn : 2 < n) :
    ¬IsSquare |bSeq a n| := by
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast hsq
  rw [abs_bSeq_eq_betaSeq ha' (by lia), ← Rat.isSquare_intCast_iff]
  exact not_isSquare_betaSeq_of_squarefree_of_not_isSquare_neg_one (evenPoly_normPoly a)
    (Int.sign_sq_of_ne_zero ha.ne) (fun d hd ↦ (gammaSeq_normPoly_pos ha' d hd).ne')
    (by rw [eval_normPoly_of_neg ha]; ring) (gammaSeq_normPoly_one ha.ne)
    (m := (-a - 1).toNat) (by rw [Int.toNat_of_nonneg (by lia), gammaSeq_normPoly_two ha])
    (ZMod.not_isSquare_neg_one_of_four_dvd (by lia)) hsf hn

/-- Theorem 3.4 of [Li 2020]: for `a < 0` with `a ≡ 3 mod 4` and `-a` not a square, `|b_n|` is not
a square for all `n ≥ 3`. -/
theorem li2020_theorem_3_4 (ha : a < 0) (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) {n : ℕ}
    (hn : 3 ≤ n) : ¬IsSquare |bSeq a n| :=
  (em (Squarefree n)).elim
    (fun h ↦ not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_three ha ha4 hsq h (by lia))
    fun h ↦
      not_isSquare_abs_bSeq_of_not_squarefree_of_neg_of_emod_four_eq_three ha ha4 hsq (by lia) h

/-- Theorem 3.5 of [Li 2020]: for `a < 0` with `a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ`
for all `n ≥ 1` if and only if `-a - 1` is not a square. -/
theorem li2020_theorem_3_5 (ha : a < 0) (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) := by
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast hsq
  refine ⟨fun h hsq2 ↦ ?_, fun h n _ ↦ section1_of_not_isSquare_abs_bSeq ha' n fun k hk _ ↦ ?_⟩
  · have hind := ((section1_tfae ha' 2).out 0 2).mp (h 2 one_le_two)
    exact hind.not_isSquare 1 (by simpa [bSeq_two ha'] using Rat.isSquare_intCast_iff.mpr hsq2)
  · rcases eq_or_ne k 2 with rfl | hk2
    · have : a ≠ -1 := fun h ↦ hsq ⟨1, by rw [h]; norm_num⟩
      rwa [bSeq_two ha', abs_of_pos (by lia)]
    · exact li2020_theorem_3_4 ha ha4 hsq (by lia)

end QuadraticIterates
