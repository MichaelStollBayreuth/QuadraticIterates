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
# Li, *On Stoll's criterion for the maximality of quadratic arboreal Galois representations*

The results of H.-C. Li, Arch. Math. **117** (2021), 133-140: `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` when
`a = -(8k+2)(8k+3)` (Theorem 3.3) or `a = -((4k+1)(4k+2)+1)` (Theorem 3.9), `k ≥ 0`. Both follow
the pattern of the Section 3 theorem of the paper: no `|b_n|` with `n ≥ 2` is a square, by the
single-index criteria of `QuadraticIterates.ArchMath1992.Sequences` with suitable moduli.

## Main statements

* `li2021_theorem_3_3`: `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` when `a = -(8k+2)(8k+3)`.
* `not_isSquare_abs_bSeq_of_squarefree` (Lemma 2.2): for squarefree `n > 1`, `|b_n|` is not a
  square once `-1` is not a square modulo `γ_1 + γ_2`; the three cases `a > 0`, `a ≡ 4 mod 8`,
  `a < 0`, `a ≡ 2 mod 8`, and `a < 0`, `a ≡ 1 mod 4`.
* `not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul` (Lemma 3.1): for `a = -(8k+2)(8k+3)`
  and `n` not squarefree, `|b_n|` is not a square.

Part of the formalization of the results of Li extending M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.Li`.
-/

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace QuadraticIterates

variable {a : ℤ}

/-- The common shape of Li's theorems: `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` once no `|b_n|` with `n ≥ 2`
is a square, checked separately for squarefree and for non-squarefree `n`. -/
theorem nonempty_mulEquiv_of_forall_not_isSquare_abs_bSeq (ha : ¬IsSquare (-a : ℚ))
    (hsf : ∀ n, Squarefree n → 1 < n → ¬IsSquare |bSeq a n|)
    (hnsf : ∀ n, ¬Squarefree n → 1 ≤ n → ¬IsSquare |bSeq a n|) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) := fun n _ ↦
  section1_of_not_isSquare_abs_bSeq ha n fun k hk _ ↦
    (em (Squarefree k)).elim (fun h ↦ hsf k h (by lia)) fun h ↦ hnsf k h (by lia)

/-- Lemma 2.2 of [Li 2021]: for squarefree `n > 1`, `|b_n|` is not a square as soon as `-1` is not
a square modulo `γ_1 + γ_2 = |a| + sgn a + 1`, since then `n / rad n = 1`. -/
theorem not_isSquare_abs_bSeq_of_squarefree (ha : ¬IsSquare (-a : ℚ)) {m : ℕ}
    (hm : (m : ℤ) = |a| + a.sign + 1) (hnsq : ¬IsSquare (-1 : ZMod m)) {n : ℕ}
    (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| := by
  have ha0 := ne_zero_of_not_isSquare_neg ha
  rw [abs_bSeq_eq_betaSeq ha hn, ← Rat.isSquare_intCast_iff]
  refine not_isSquare_betaSeq_of_dvd_add_succ (evenPoly_normPoly a) (Int.sign_sq_of_ne_zero ha0)
    (fun d hd ↦ (gammaSeq_normPoly_pos ha d hd).ne') (isUnit_eval_zero_normPoly ha0) hn rfl
    ((one_mul n).symm.trans (congrArg _ (Nat.radical_eq_self_of_squarefree hsf).symm)) ?_ hnsq
  rw [hm, gammaSeq_succ _ _ le_rfl, gammaSeq_normPoly_one ha0, eval_normPoly]
  exact dvd_of_eq (by ring)

/-- Lemma 2.2 (1) of [Li 2021]: for `a > 0` with `a ≡ 4 mod 8`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = a + 2 ≡ 6 mod 8`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_pos_of_emod_eight_eq_four (ha : 0 < a)
    (ha8 : a % 8 = 4) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast not_isSquare_of_neg (by lia)) (m := (a + 2).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_pos ha, Int.sign_eq_one_of_pos ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (by omega)) hsf hn

/-- Lemma 2.2 (2) of [Li 2021]: for `a < 0` with `a ≡ 2 mod 8`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = -a ≡ 6 mod 8`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_eight_eq_two (ha : a < 0)
    (ha8 : a % 8 = 2) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast Int.not_isSquare_of_emod_four_eq_two (by omega))
    (m := (-a).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_neg ha, Int.sign_eq_neg_one_of_neg ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (by omega)) hsf hn

/-- Lemma 2.2 (3) of [Li 2021]: for `a < 0` with `a ≡ 1 mod 4`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = -a ≡ 3 mod 4`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_one (ha : a < 0)
    (ha4 : a % 4 = 1) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast Int.not_isSquare_of_emod_four_eq_three (by omega))
    (m := (-a).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_neg ha, Int.sign_eq_neg_one_of_neg ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three (by omega)) hsf hn

section

variable {k : ℕ} (ha : a = -((8 * k + 2) * (8 * k + 3)))
include ha

private lemma neg_of_eq_neg_mul : a < 0 := by
  rw [ha]
  nlinarith

private lemma emod_eight_of_eq_neg_mul : a % 8 = 2 := by
  rw [ha, show -((8 * (k : ℤ) + 2) * (8 * k + 3)) = 2 + 8 * (-(8 * k ^ 2 + 5 * k + 1)) by ring,
    Int.add_mul_emod_self_left]
  decide

/-- Lemma 3.1 of [Li 2021]: for `a = -(8k+2)(8k+3)` and `n ≥ 1` not squarefree, `|b_n|` is not a
square. With `k₀ = n / rad n ≥ 2`, the modulus `m = (8k+2) γ_{k₀} + 1` divides
`γ_{k₀} + γ_{k₀+1} = -a γ_{k₀}² + γ_{k₀} - 1 = ((8k+3) γ_{k₀} - 1) m`, and `m ≡ 3 mod 4` because
`γ_{k₀} ≡ 5 mod 8`. -/
theorem not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul {n : ℕ} (hn : 1 ≤ n)
    (hsf : ¬Squarefree n) : ¬IsSquare |bSeq a n| := by
  have ha0 := neg_of_eq_neg_mul ha
  have ha8 := emod_eight_of_eq_neg_mul ha
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast Int.not_isSquare_of_emod_four_eq_two (by omega)
  have hk₀2 := Nat.two_le_div_radical_of_not_squarefree (by lia) hsf
  have hn2 : 2 ≤ n := by
    have := Nat.div_mul_cancel (radical_dvd_self (a := n))
    nlinarith [Nat.radical_pos n]
  have hγ4 : ((gammaSeq (normPoly a) a.sign (n / radical n) : ℤ) : ZMod 4) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff' _ _ 8).mp
      (gammaSeq_normPoly_zmod_eight_of_even ha0 (Int.even_iff.mpr (by omega)) _ hk₀2)
    exact (ZMod.intCast_eq_intCast_iff' _ 1 4).mpr (by omega)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := (8 * k + 2) *
    gammaSeq (normPoly a) a.sign (n / radical n) + 1)
    (by nlinarith [gammaSeq_normPoly_pos ha' (n / radical n) (by lia)])
  have hm4 : m % 4 = 3 := by
    have := (ZMod.intCast_eq_intCast_iff' (m : ℤ) 3 4).mp (by
      rw [← hm]; push_cast; rw [hγ4]; generalize (k : ZMod 4) = x; decide +revert)
    omega
  rw [abs_bSeq_eq_betaSeq ha' hn2, ← Rat.isSquare_intCast_iff]
  refine not_isSquare_betaSeq_of_dvd_add_succ (evenPoly_normPoly a) (Int.sign_sq_of_ne_zero ha0.ne)
    (fun d hd ↦ (gammaSeq_normPoly_pos ha' d hd).ne') (isUnit_eval_zero_normPoly ha0.ne) hn2 rfl
    (Nat.div_mul_cancel radical_dvd_self).symm (m := m) ?_
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three hm4)
  rw [← hm, gammaSeq_succ _ _ (by lia), eval_normPoly_of_neg ha0]
  exact ⟨(8 * k + 3) * gammaSeq (normPoly a) a.sign (n / radical n) - 1, by
    linear_combination (-(gammaSeq (normPoly a) a.sign (n / radical n)) ^ 2) * ha⟩

/-- Theorem 3.3 of [Li 2021]: for `a = -(8k+2)(8k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem li2021_theorem_3_3 : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  have ha8 := emod_eight_of_eq_neg_mul ha
  nonempty_mulEquiv_of_forall_not_isSquare_abs_bSeq
    (mod_cast Int.not_isSquare_of_emod_four_eq_two (by omega))
    (fun _ hsf hn ↦ not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_eight_eq_two
      (neg_of_eq_neg_mul ha) ha8 hsf hn)
    fun _ hsf hn ↦ not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul ha hn hsf

end

end QuadraticIterates
