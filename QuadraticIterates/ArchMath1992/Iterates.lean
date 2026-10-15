/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.RegularWreathProduct
public import QuadraticIterates.ArchMath1992.Sequences
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Galois.Tower
public import QuadraticIterates.Galois.TwoIndependent
public import QuadraticIterates.Mathlib.FieldTheory.Multiquadratic

import QuadraticIterates.Mathlib.Algebra.QuadraticDiscriminant
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.Fintype.Basic
import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup
import QuadraticIterates.Mathlib.GroupTheory.Card
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The sequences `c_n` and `b_n` over the integers, and parameters in `[-2, 0]`

Material on the sequence `c_n` of `X² + a` used by the proofs of the paper through the Möbius
factors `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}`: strong divisibility of `c`, the factors `b_n` of a
parameter in a domain, the rescaled polynomial `normPoly a` of an integer parameter, and
2-independence of pairwise coprime integers; and the order-theoretic facts about `c_n` for a
parameter in `[-2, 0]` of an ordered ring. The iterates, their Galois groups and the sequence `c`
itself are in `QuadraticIterates.Galois.Iterates`.

## Main definitions

* `bSeq a`: the sequence `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}` of a parameter `a` in a domain.
* `normPoly a`: the rescaling `|a|·X² + sign a` of `X² + a`, `a ∈ ℤ`.

## Main statements

* `QuadraticIterates.cSeq_gcd`: strong divisibility of the integer sequence `c`.
* `QuadraticIterates.twoIndependent_iff_of_pairwise_isCoprime`: a pairwise coprime family of
  integers is 2-independent iff none of its members is a square and at most one of their negatives
  is.
* `QuadraticIterates.cSeq_add_cSeq_succ_neg`: in an ordered ring, for `α < a < 0` with `α` the
  real root of `x³ + 2x² + 2x + 2`, the sums `c_n + c_{n+1}` of successive iterates are negative
  (`QuadraticIterates.cSeq_le_sq_add`: for `-2 ≤ a ≤ 0` the sequence is bounded by `c_2 = a² + a`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-- The value of the integer iterate `f_n` at an integer, cast into any commutative ring `S`, is
the value of the iterate over `S`; this links `fℚ[a, n]` to the integer sequence `c`. -/
lemma intCast_eval_iteratedPoly {S : Type*} [CommRing S] (a x : ℤ) (n : ℕ) :
    (((iteratedPoly a n).eval x : ℤ) : S) = (iteratedPoly (a : S) n).eval (x : S) :=
  map_eval_iteratedPoly a (Int.castRingHom S) x n

section

variable {R : Type*} [CommRing R] (a : R)

/-- Rescaling: for `ε² = 1`, `c_n = εa · γ_n` for `n ≥ 2`, where `γ` is the `γ`-sequence of
`(εa) X² + ε` with sign `ε`; e.g. `ε = sgn a` gives the rescaled polynomial `|a| X² + sgn a`, and
`a = εr/s` gives `(r/s) X² + ε`, the polynomial of the sequence `QuadraticIterates.wEps r s ε`. -/
theorem cSeq_eq_mul_gammaSeq {ε : R} (hε : ε ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    cSeq a n = ε * a * gammaSeq (C (ε * a) * X ^ 2 + C ε) ε n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [cSeq_two, gammaSeq_succ _ _ le_rfl, gammaSeq_one]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, zero_pow two_ne_zero, mul_zero,
      zero_add]
    linear_combination (-(a ^ 2 * (1 + ε ^ 2 + ε ^ 4) + a)) * hε
  | succ k hk ih =>
    rw [cSeq_succ a (by lia), ih, gammaSeq_succ _ _ (by lia)]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination (-a) * hε

end

/-- **Strong divisibility** for the `c`-sequence: `gcd (c_m) (c_n) = |c_{gcd m n}|`. -/
theorem cSeq_gcd (a : ℤ) (m n : ℕ) : Int.gcd (cSeq a m) (cSeq a n) = (cSeq a (m.gcd n)).natAbs :=
  gammaSeq_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

/-- Strong divisibility of the `c`-sequence in the `Associated`-of-`gcd` form consumed by the
`moebiusFactorR` API. -/
theorem cSeq_associated_gcd (a : ℤ) (m n : ℕ) :
    Associated (gcd (cSeq a m) (cSeq a n)) (cSeq a (m.gcd n)) :=
  gammaSeq_associated_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

/-- The Möbius factors `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}` of the `c`-sequence of a parameter `a` in a
domain: the specialization of the general `β`-sequence to `X² + a`, `ε = -1`. Over `ℤ` these are
the integers `b_n` of the paper (`QuadraticIterates.intCast_bSeq_eq_moebiusFactorK`, an integer
by strong divisibility); over a field they are the Möbius products themselves
(`QuadraticIterates.bSeq_eq_moebiusFactorK`). -/
noncomputable def bSeq {R : Type*} [CommRing R] [IsDomain R] (a : R) (n : ℕ) : R :=
  betaSeq (X ^ 2 + C a) (-1) n

section bSeq

variable {R : Type*} [CommRing R] [IsDomain R] (a : R)

lemma bSeq_eq_moebiusFactorR (n : ℕ) : bSeq a n = moebiusFactorR (cSeq a) n := rfl

@[simp] lemma bSeq_one : bSeq a 1 = -a := by simp [bSeq_eq_moebiusFactorR]

end bSeq

/-- Over a field, `b_n` is the Möbius product `∏_{ed = n} c_d^{μ(e)}` itself. -/
lemma bSeq_eq_moebiusFactorK {K : Type*} [Field K] (a : K) (n : ℕ) :
    bSeq a n = moebiusFactorK (cSeq a) n :=
  moebiusFactorR_eq_moebiusFactorK _ n

/-- The rescaling `|a|·X² + sign a` of `X² + a`. Substituting `x ↦ |a|·x` turns the recursion
`c_{n+1} = c_n² + a` into the `γ`-recursion of `normPoly a`, whose sequence is therefore
`|c_n| / |a|` (`QuadraticIterates.abs_cSeq_eq_gammaSeq_mul_abs`) — in particular positive, which is
what Lemma 2.2 needs and `X² + a` itself does not provide. -/
noncomputable def normPoly (a : ℤ) : ℤ[X] := C |a| * X ^ 2 + C a.sign

@[simp] lemma eval_normPoly (a x : ℤ) : (normPoly a).eval x = |a| * x ^ 2 + a.sign := by
  simp [normPoly]

lemma evenPoly_normPoly (a : ℤ) : EvenPoly (normPoly a) := evenPoly_C_mul_X_sq_add_C |a| a.sign

/-! ### The iterates of a parameter in `[-2, 0]` of an ordered ring -/

section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a : R)

theorem le_cSeq {n : ℕ} (hn : 2 ≤ n) : a ≤ cSeq a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [cSeq_succ a (by lia)]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- For `-2 ≤ a ≤ 0` the second iterate `c_2 = a² + a` bounds the sequence from above: the
interval `[a, a² + a]`, contained in `[a, -a]`, is mapped into itself by `x ↦ x² + a`. -/
theorem cSeq_le_sq_add (h₂ : -2 ≤ a) (h₀ : a ≤ 0) {n : ℕ} (hn : 2 ≤ n) :
    cSeq a n ≤ a ^ 2 + a := by
  induction n, hn using Nat.le_induction with
  | base => exact (cSeq_two a).le
  | succ k hk ih =>
    have hle : a ^ 2 + a ≤ -a := by
      linear_combination mul_nonpos_of_nonpos_of_nonneg h₀ (by linarith : 0 ≤ a + 2)
    rw [cSeq_succ a (by lia), ← neg_sq a]
    exact add_le_add (sq_le_sq' (by linarith [le_cSeq a hk]) (ih.trans hle)) le_rfl

-- the real root of `x³ + 2x² + 2x + 2` is larger than `-2`
private lemma neg_two_lt_of_pos (h : 0 < a ^ 3 + 2 * a ^ 2 + 2 * a + 2) : -2 < a := by
  by_contra! h'
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith : a + 2 ≤ 0)
  linarith [(by linear_combination h1 + 2 * h' : a ^ 3 + 2 * a ^ 2 + 2 * a + 2 ≤ -2)]

/-- The first iterate `a = -c_1` and the second, `c_2 = a² + a`, have negative sum for
`-2 < a < 0`. -/
theorem add_cSeq_two_neg (h₂ : -2 < a) (ha : a < 0) : a + cSeq a 2 < 0 := by
  rw [cSeq_two]
  linear_combination mul_neg_of_neg_of_pos ha (by linarith : 0 < a + 2)

/-- **Sums of successive iterates are negative** for `α < a < 0`, where `α ≈ -1.5437` is the real
root of `x³ + 2x² + 2x + 2`: `c_n + c_{n+1} < 0` for all `n ≥ 2` (the first pair is
`QuadraticIterates.add_cSeq_two_neg`). The hypothesis `0 < a³ + 2a² + 2a + 2` says `α < a`, the
cubic being increasing; `QuadraticIterates.cSeq_add_cSeq_succ_neg_of_lt` has the root in the
statement. Proof: `c_n + c_{n+1} = q(c_n)` for `q(x) = x² + x + a`, `c_n` lies in `[a, a² + a]`,
and the convex `q` is negative at both endpoints, `q(a) = a (a + 2)` and
`q(a² + a) = a (a³ + 2a² + 2a + 2)`. -/
theorem cSeq_add_cSeq_succ_neg (ha : a < 0) (hα : 0 < a ^ 3 + 2 * a ^ 2 + 2 * a + 2) {n : ℕ}
    (hn : 2 ≤ n) : cSeq a n + cSeq a (n + 1) < 0 := by
  have h₂ := neg_two_lt_of_pos a hα
  have hl : 1 * (a * a) + 1 * a + a < 0 := by
    linear_combination mul_neg_of_neg_of_pos ha (by linarith : 0 < a + 2)
  have hu : 1 * ((a ^ 2 + a) * (a ^ 2 + a)) + 1 * (a ^ 2 + a) + a < 0 := by
    linear_combination mul_neg_of_neg_of_pos ha hα
  have := (quadratic_le_max_of_nonneg_of_mem_Icc zero_le_one 1 a
    ⟨le_cSeq a hn, cSeq_le_sq_add a h₂.le ha.le hn⟩).trans_lt (max_lt hl hu)
  rw [cSeq_succ a (by lia)]
  linear_combination this

/-- `QuadraticIterates.cSeq_add_cSeq_succ_neg` with the root in the statement: for a root `α` of
`x³ + 2x² + 2x + 2` (over `ℝ`, its only real root, `α ≈ -1.5437`) and `α < a < 0`, the sums
`c_n + c_{n+1}`, `n ≥ 2`, are negative. -/
theorem cSeq_add_cSeq_succ_neg_of_lt {α : R} (hα : α ^ 3 + 2 * α ^ 2 + 2 * α + 2 = 0) (h : α < a)
    (ha : a < 0) {n : ℕ} (hn : 2 ≤ n) : cSeq a n + cSeq a (n + 1) < 0 := by
  refine cSeq_add_cSeq_succ_neg a ha ?_ hn
  have hpos : 0 < a ^ 2 + a * α + α ^ 2 + 2 * a + 2 * α + 2 := by
    nlinarith [sq_nonneg (2 * a + α + 2), sq_nonneg (3 * α + 2)]
  linear_combination mul_pos (sub_pos.2 h) hpos - hα

end

/-! ### 2-independence -/

section TwoIndependent

variable {ι M : Type*}

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
