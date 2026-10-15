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

import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.Fintype.Basic
import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup
import QuadraticIterates.Mathlib.GroupTheory.Card
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The sequences `c_n` and `b_n` over the integers

Material on the sequence `c_n` of `X² + a` used by the proofs of the paper through the Möbius
factors `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}`: strong divisibility of `c`, the factors `b_n` of a
parameter in a domain, the rescaled polynomial `normPoly a` of an integer parameter, and
2-independence of pairwise coprime integers. The iterates, their Galois groups and the sequence `c`
itself are in `QuadraticIterates.Galois.Iterates`.

## Main definitions

* `bSeq a`: the sequence `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}` of a parameter `a` in a domain.
* `normPoly a`: the rescaling `|a|·X² + sign a` of `X² + a`, `a ∈ ℤ`.

## Main statements

* `QuadraticIterates.cSeq_gcd`: strong divisibility of the integer sequence `c`.
* `QuadraticIterates.twoIndependent_iff_of_pairwise_isCoprime`: a pairwise coprime family of
  integers is 2-independent iff none of its members is a square and at most one of their negatives
  is.

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
