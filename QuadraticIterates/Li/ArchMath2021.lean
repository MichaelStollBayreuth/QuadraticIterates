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
  square once `-1` is not a square modulo `γ_1 + γ_2`; its three cases
  `not_isSquare_abs_bSeq_of_squarefree_of_pos_of_emod_eight_eq_four`,
  `…_of_neg_of_emod_eight_eq_two` and `…_of_neg_of_emod_four_eq_one`.
* `nonempty_mulEquiv_of_forall_not_isSquare_abs_bSeq`: the common shape of both theorems, a case
  split on `Squarefree n` in front of part 2 of the Section 1 theorem.
* `not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul` (Lemma 3.1): for `a = -(8k+2)(8k+3)`
  and `n` not squarefree, `|b_n|` is not a square.
* `li2021_theorem_3_9`: `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` when `a = -((4k+1)(4k+2)+1)`.
* `not_isSquare_abs_bSeq_of_not_squarefree_of_not_four_dvd_of_emod_four_eq_one` (Lemma 3.4):
  for `a < 0`, `a ≡ 1 mod 4` and `n` not squarefree with `4 ∤ n`, `|b_n|` is not a square.
* `not_isSquare_abs_bSeq_of_even_div_radical_of_eq_neg_mul_add_one` (Lemma 3.6): for
  `a = -((4k+1)(4k+2)+1)` and `n / rad n` even, `|b_n|` is not a square.

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
  refine not_isSquare_abs_bSeq_of_dvd_add_succ ha hn
    ((one_mul n).symm.trans (congrArg _ (Nat.squarefree_iff_radical_eq_self.mp hsf).symm)) ?_ hnsq
  rw [hm, gammaSeq_succ _ _ le_rfl, gammaSeq_normPoly_one (ne_zero_of_not_isSquare_neg ha),
    eval_normPoly]
  exact dvd_of_eq (by ring)

/-- Lemma 2.2 (1) of [Li 2021]: for `a > 0` with `a ≡ 4 mod 8`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = a + 2 ≡ 6 mod 8`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_pos_of_emod_eight_eq_four (ha : 0 < a)
    (ha8 : a % 8 = 4) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast not_isSquare_of_neg (by lia)) (m := (a + 2).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_pos ha, Int.sign_eq_one_of_pos ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (by lia)) hsf hn

/-- Lemma 2.2 (2) of [Li 2021]: for `a < 0` with `a ≡ 2 mod 8`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = -a ≡ 6 mod 8`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_eight_eq_two (ha : a < 0)
    (ha8 : a % 8 = 2) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast Int.not_isSquare_of_emod_four_eq_two (by lia))
    (m := (-a).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_neg ha, Int.sign_eq_neg_one_of_neg ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (by lia)) hsf hn

/-- Lemma 2.2 (3) of [Li 2021]: for `a < 0` with `a ≡ 1 mod 4`, `|b_n|` is not a square for
squarefree `n > 1` (`-1` is not a square modulo `γ_1 + γ_2 = -a ≡ 3 mod 4`). -/
theorem not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_one (ha : a < 0)
    (ha4 : a % 4 = 1) {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) : ¬IsSquare |bSeq a n| :=
  not_isSquare_abs_bSeq_of_squarefree (mod_cast Int.not_isSquare_of_emod_four_eq_three (by lia))
    (m := (-a).toNat)
    (by rw [Int.toNat_of_nonneg (by lia), abs_of_neg ha, Int.sign_eq_neg_one_of_neg ha]; ring)
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three (by lia)) hsf hn

private lemma mul_add_one_emod_four_eq_three {k : ℕ} {γ : ℤ} (hγ : γ % 4 = 1) :
    ((8 * k + 2) * γ + 1) % 4 = 3 := by
  rw [Int.add_emod, Int.mul_emod, hγ, show (8 * (k : ℤ) + 2) % 4 = 2 by lia]
  decide

section

variable {k : ℕ} (ha : a = -((8 * k + 2) * (8 * k + 3)))
include ha

private lemma neg_of_eq_neg_mul : a < 0 := ha ▸ neg_lt_zero.mpr (by positivity)

private lemma emod_eight_eq_two_of_eq_neg_mul : a % 8 = 2 := by
  rw [ha, show -((8 * (k : ℤ) + 2) * (8 * k + 3)) = 2 + 8 * (-(8 * k ^ 2 + 5 * k + 1)) by ring,
    Int.add_mul_emod_self_left]
  decide

/-- Lemma 3.1 of [Li 2021]: for `a = -(8k+2)(8k+3)` and `n ≥ 1` not squarefree, `|b_n|` is not a
square. With `k₀ = n / rad n ≥ 2`, the modulus `m = (8k+2) γ_{k₀} + 1` divides
`γ_{k₀} + γ_{k₀+1} = -a γ_{k₀}² + γ_{k₀} - 1 = ((8k+3) γ_{k₀} - 1) m`, and `m ≡ 3 mod 4` because
`γ_{k₀} ≡ 1 mod 4`. -/
theorem not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul {n : ℕ} (hn : 1 ≤ n)
    (hsf : ¬Squarefree n) : ¬IsSquare |bSeq a n| := by
  have ha0 := neg_of_eq_neg_mul ha
  have ha8 := emod_eight_eq_two_of_eq_neg_mul ha
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast Int.not_isSquare_of_emod_four_eq_two (by lia)
  have hk₀2 := Nat.two_le_div_radical_of_not_squarefree (by lia) hsf
  have hpos := gammaSeq_normPoly_pos ha' (n / radical n) (by lia)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := (8 * k + 2) * γ[a] (n / radical n) + 1)
    (add_nonneg (mul_nonneg (by positivity) hpos.le) zero_le_one)
  have hm4 : m % 4 = 3 := by
    have := mul_add_one_emod_four_eq_three (k := k)
      (gammaSeq_normPoly_emod_four_eq_one_of_emod_eight_eq_two ha0 ha8 hk₀2)
    lia
  refine not_isSquare_abs_bSeq_of_dvd_add_succ ha' (hk₀2.trans (Nat.div_le_self n _))
    (Nat.div_mul_cancel radical_dvd_self).symm (m := m) ?_
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three hm4)
  rw [← hm, gammaSeq_succ _ _ (by lia), eval_normPoly_of_neg ha0]
  exact ⟨(8 * k + 3) * γ[a] (n / radical n) - 1, by
    linear_combination (-(γ[a] (n / radical n)) ^ 2) * ha⟩

/-- Theorem 3.3 of [Li 2021]: for `a = -(8k+2)(8k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem li2021_theorem_3_3 : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  have ha8 := emod_eight_eq_two_of_eq_neg_mul ha
  nonempty_mulEquiv_of_forall_not_isSquare_abs_bSeq
    (mod_cast Int.not_isSquare_of_emod_four_eq_two (by lia))
    (fun _ hsf hn ↦ not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_eight_eq_two
      (neg_of_eq_neg_mul ha) ha8 hsf hn)
    fun _ hsf hn ↦ not_isSquare_abs_bSeq_of_not_squarefree_of_eq_neg_mul ha hn hsf

end

/-- Lemma 3.4 of [Li 2021]: for `a < 0` with `a ≡ 1 mod 4` and `n ≥ 1` not squarefree with
`4 ∤ n`, `|b_n|` is not a square: `k = n / rad n ≥ 3` is odd, `γ_k + γ_{k+2} ≡ 6 mod 8`, and the
odd part `M ≡ 3 mod 4` of `γ_k + γ_{k+2}` is coprime to `γ_{k+1}`. -/
theorem not_isSquare_abs_bSeq_of_not_squarefree_of_not_four_dvd_of_emod_four_eq_one (ha : a < 0)
    (ha4 : a % 4 = 1) {n : ℕ} (hn : 1 ≤ n) (hsf : ¬Squarefree n) (hn4 : ¬4 ∣ n) :
    ¬IsSquare |bSeq a n| := by
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast Int.not_isSquare_of_emod_four_eq_three (by lia)
  have hk₀2 := Nat.two_le_div_radical_of_not_squarefree (by lia) hsf
  have hko : Odd (n / radical n) :=
    Nat.not_even_iff_odd.mp fun h ↦ hn4 ((Nat.even_div_radical_iff_four_dvd (by lia)).mp h)
  have h8 := gammaSeq_normPoly_add_two_emod_eight_eq_six ha ha4 hko
    (by obtain ⟨j, hj⟩ := hko; lia)
  obtain ⟨M, hM⟩ : (2 : ℤ) ∣ γ[a] (n / radical n) + γ[a] (n / radical n + 2) := by lia
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := M) (by
    have := gammaSeq_normPoly_pos ha' (n / radical n) (by lia)
    have := gammaSeq_normPoly_pos ha' (n / radical n + 2) (by lia)
    lia)
  refine not_isSquare_abs_bSeq_of_odd_of_dvd_add_two ha'
    (Nat.div_mul_cancel radical_dvd_self).symm hko (by lia) ⟨2, by rw [← hm, hM]; ring⟩ ?_
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three (by lia))
  rw [← hm]
  exact isCoprime_gammaSeq_succ_of_odd_of_add_two_eq_two_mul (evenPoly_normPoly a)
    (by rw [eval_normPoly_of_neg ha]; ring) (gammaSeq_normPoly_one ha.ne) hko (by lia) hM
    (Int.odd_iff.mpr (by lia))

/-- With `A = 4k + 1`: if `α ≡ 3` and `γ ≡ 2 mod 4`, then `m` with `A m = α γ + A` is
`≡ 3 mod 4`. -/
private lemma emod_four_eq_three_of_mul_eq {k : ℕ} {α γ m : ℤ} (hα : α % 4 = 3) (hγ : γ % 4 = 2)
    (hm : α * γ + (4 * k + 1) = (4 * k + 1) * m) : m % 4 = 3 := by
  have h := (ZMod.intCast_eq_intCast_iff' m 3 4).mp (by
    have h1 := (ZMod.intCast_eq_intCast_iff' _ 2 4).mpr hγ
    have h2 := (ZMod.intCast_eq_intCast_iff' α 3 4).mpr hα
    have := congrArg (Int.cast : ℤ → ZMod 4) hm
    push_cast at this h1 h2
    rw [h1, h2] at this
    generalize (k : ZMod 4) = x at this
    generalize (m : ZMod 4) = y at this ⊢
    decide +revert)
  lia

/-- The modulus `m = (α γ + A) / A` is coprime to `γ_2 = AB`: modulo `A` it is `2`, and modulo
`B = 2(2k+1)` it is odd and `≡ 1 mod 2k+1`. -/
private lemma isCoprime_of_mul_eq {k : ℕ} {γ m : ℤ}
    (hm : (4 * (k : ℤ) + 1) * m = ((4 * k + 1) * (4 * k + 2) + 1) * γ + (4 * k + 1)) (hmo : Odd m)
    (hγA : (4 * (k : ℤ) + 1) ^ 2 ∣ γ - (4 * k + 1) * (4 * k + 2)) (hγB : (4 * (k : ℤ) + 2) ∣ γ) :
    IsCoprime m ((4 * (k : ℤ) + 1) * (4 * k + 2)) := by
  obtain ⟨w, hw⟩ := hγA
  obtain ⟨γ', hγ'⟩ := hγB
  obtain ⟨q, hq⟩ := hmo
  have hA : m = 2 + (4 * (k : ℤ) + 1) *
      ((4 * k + 2) ^ 2 + 1 + ((4 * k + 1) * (4 * k + 2) + 1) * w) := by
    have : (4 * (k : ℤ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ this
    rw [hm]
    linear_combination ((4 * (k : ℤ) + 1) * (4 * k + 2) + 1) * hw
  have hB : m = 1 + (2 * (k : ℤ) + 1) *
      (2 * (m - 1) - 2 * ((4 * k + 1) * (4 * k + 2) + 1) * γ') := by
    linear_combination -hm - ((4 * (k : ℤ) + 1) * (4 * k + 2) + 1) * hγ'
  have h2A : IsCoprime (2 : ℤ) (4 * k + 1) := ⟨-2 * k, 1, by ring⟩
  have hm2 : IsCoprime m 2 := ⟨1, -q, by linear_combination hq⟩
  refine IsCoprime.mul_right ?_ (show (4 * (k : ℤ) + 2) = 2 * (2 * k + 1) by ring ▸
    IsCoprime.mul_right hm2 ?_)
  · rw [hA]
    exact h2A.add_mul_left_left _
  · rw [hB]
    exact isCoprime_one_left.add_mul_left_left _

section

variable {k : ℕ} (ha : a = -((4 * k + 1) * (4 * k + 2) + 1))
include ha

private lemma neg_of_eq_neg_mul_add_one : a < 0 := ha ▸ neg_lt_zero.mpr (by positivity)

private lemma emod_four_eq_one_of_eq_neg_mul_add_one : a % 4 = 1 := by
  rw [ha, show -((4 * (k : ℤ) + 1) * (4 * k + 2) + 1) = 1 + 4 * (-(4 * k ^ 2 + 3 * k + 1)) by ring,
    Int.add_mul_emod_self_left]
  decide

/-- The factorization `y + g(g(y)) = (α y + A) (α² y³ - A α y² - (α + B) y + B)` for
`g = α X² - 1`, `A = 4k + 1`, `B = 4k + 2`, `α = AB + 1`. -/
private lemma add_eval_eval_eq_mul (y : ℤ) :
    y + (-a * (-a * y ^ 2 - 1) ^ 2 - 1) = (-a * y + (4 * k + 1)) *
      (a ^ 2 * y ^ 3 + (4 * k + 1) * a * y ^ 2 + (a - (4 * k + 2)) * y + (4 * k + 2)) := by
  subst ha
  ring

private lemma gammaSeq_normPoly_two_of_eq_neg_mul_add_one :
    γ[a] 2 = (4 * (k : ℤ) + 1) * (4 * k + 2) := by
  rw [gammaSeq_normPoly_two (neg_of_eq_neg_mul_add_one ha), ha]
  ring

/-- With `A = 4k+1`, `α = -a` and `k₀ ≥ 2` even, `A` divides `α γ_{k₀} + A`, and the quotient `m`
is `≡ 3 mod 4`. -/
private lemma exists_mul_eq_and_emod_four_eq_three_of_even {k₀ : ℕ} (hk₀2 : 2 ≤ k₀)
    (hke : Even k₀) :
    ∃ m : ℕ, (4 * (k : ℤ) + 1) * m = -a * γ[a] k₀ + (4 * k + 1) ∧ m % 4 = 3 := by
  have ha0 := neg_of_eq_neg_mul_add_one ha
  have ha4 := emod_four_eq_one_of_eq_neg_mul_add_one ha
  have hdvd2 : (4 * (k : ℤ) + 1) * (4 * k + 2) ∣ γ[a] k₀ :=
    gammaSeq_normPoly_two_of_eq_neg_mul_add_one ha ▸ gammaSeq_normPoly_two_dvd_of_even ha0 hk₀2 hke
  obtain ⟨m, hm⟩ : (4 * k + 1 : ℤ) ∣ -a * γ[a] k₀ + (4 * k + 1) :=
    dvd_add ((Dvd.intro _ rfl).trans hdvd2 |>.mul_left _) dvd_rfl
  have hm4 := emod_four_eq_three_of_mul_eq (by lia)
    (gammaSeq_normPoly_emod_four_eq_two_of_even ha0 ha4 hke hk₀2) hm
  have ha' : ¬IsSquare (-a : ℚ) := mod_cast Int.not_isSquare_of_emod_four_eq_three (by lia)
  have hpos := gammaSeq_normPoly_pos ha' k₀ (by lia)
  obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le (a := m) (pos_of_mul_pos_right
    (hm ▸ add_pos (mul_pos (neg_pos.mpr ha0) hpos) (by positivity)) (by positivity)).le
  exact ⟨m', hm.symm, by lia⟩

/-- The modulus `m` with `A m = α γ_{k₀} + A` divides `γ_{k₀} + γ_{k₀+2}`, by the factorization
`add_eval_eval_eq_mul`. -/
private lemma dvd_add_two_of_mul_eq {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {m : ℤ}
    (hm : (4 * (k : ℤ) + 1) * m = -a * γ[a] k₀ + (4 * k + 1)) :
    m ∣ γ[a] k₀ + γ[a] (k₀ + 2) := by
  have ha0 := neg_of_eq_neg_mul_add_one ha
  rw [gammaSeq_succ _ _ (by lia), gammaSeq_succ _ _ hk₀, eval_normPoly_of_neg ha0,
    eval_normPoly_of_neg ha0, add_eval_eval_eq_mul ha, ← hm]
  exact (dvd_mul_left _ _).mul_right _

/-- For even `k₀ ≥ 2`, an odd `m` with `A m = α γ_{k₀} + A` is coprime to `γ_2 = AB`: the
coprimality part of Lemma 3.6 of [Li 2021], by `isCoprime_of_mul_eq`. -/
private lemma isCoprime_gammaSeq_two_of_mul_eq {k₀ : ℕ} (hk₀2 : 2 ≤ k₀) (hke : Even k₀) {m : ℤ}
    (hm : (4 * (k : ℤ) + 1) * m = -a * γ[a] k₀ + (4 * k + 1))
    (hmo : Odd m) : IsCoprime m (γ[a] 2) := by
  have ha0 := neg_of_eq_neg_mul_add_one ha
  have hγ2 := gammaSeq_normPoly_two_of_eq_neg_mul_add_one ha
  have hsq := gammaSeq_normPoly_two_sq_dvd_sub_ite_even ha0 hk₀2
  rw [if_pos hke, hγ2] at hsq
  rw [hγ2]
  exact isCoprime_of_mul_eq (by linear_combination hm - γ[a] k₀ * ha) hmo
    ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) 2).trans hsq)
    ((dvd_mul_left _ _).trans (hγ2 ▸ gammaSeq_normPoly_two_dvd_of_even ha0 hk₀2 hke))

/-- Lemma 3.6 of [Li 2021]: for `a = -((4k+1)(4k+2)+1)` and `n ≥ 1` with `k₀ = n / rad n` even,
`|b_n|` is not a square. With `A = 4k+1`, `B = 4k+2`, `α = -a = AB + 1`: `γ_{k₀} + γ_{k₀+2}` is
divisible by `α γ_{k₀} + A = A m`, where `m ≡ 3 mod 4` and `m` is coprime to `γ_2 = AB`. -/
theorem not_isSquare_abs_bSeq_of_even_div_radical_of_eq_neg_mul_add_one {n : ℕ} (hn : 1 ≤ n)
    (hke : Even (n / radical n)) : ¬IsSquare |bSeq a n| := by
  have ha4 := emod_four_eq_one_of_eq_neg_mul_add_one ha
  have hk₀2 : 2 ≤ n / radical n :=
    Nat.le_of_dvd (Nat.div_radical_pos hn) (even_iff_two_dvd.mp hke)
  obtain ⟨m, hm, hm4⟩ := exists_mul_eq_and_emod_four_eq_three_of_even ha hk₀2 hke
  exact not_isSquare_abs_bSeq_of_even_of_dvd_add_two
    (mod_cast Int.not_isSquare_of_emod_four_eq_three (by lia)) (hk₀2.trans (Nat.div_le_self n _))
    (Nat.div_mul_cancel radical_dvd_self).symm hke (dvd_add_two_of_mul_eq ha (by lia) hm)
    (isCoprime_gammaSeq_two_of_mul_eq ha hk₀2 hke hm (Int.odd_iff.mpr (by lia)))
    (ZMod.not_isSquare_neg_one_of_emod_four_eq_three hm4)

/-- Theorem 3.9 of [Li 2021]: for `a = -((4k+1)(4k+2)+1)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem li2021_theorem_3_9 : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  have ha0 := neg_of_eq_neg_mul_add_one ha
  have ha4 := emod_four_eq_one_of_eq_neg_mul_add_one ha
  nonempty_mulEquiv_of_forall_not_isSquare_abs_bSeq
    (mod_cast Int.not_isSquare_of_emod_four_eq_three (by lia))
    (fun _ hsf hn ↦ not_isSquare_abs_bSeq_of_squarefree_of_neg_of_emod_four_eq_one ha0 ha4 hsf hn)
    fun n hsf hn ↦ (em (4 ∣ n)).elim
      (fun h4 ↦ not_isSquare_abs_bSeq_of_even_div_radical_of_eq_neg_mul_add_one ha hn
        ((Nat.even_div_radical_iff_four_dvd (by lia)).mpr h4))
      fun h4 ↦ not_isSquare_abs_bSeq_of_not_squarefree_of_not_four_dvd_of_emod_four_eq_one ha0 ha4
        hn hsf h4

end

end QuadraticIterates
