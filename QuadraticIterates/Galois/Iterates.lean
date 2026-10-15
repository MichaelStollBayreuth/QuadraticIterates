/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.RegularWreathProduct
public import QuadraticIterates.EvenPoly

/-!
# The iterates of `X² + a`, their Galois groups and the sequence `c_n`

The iterates `f_n` of `f = X² + a` over a commutative semiring; for a rational parameter `a`, the
splitting field `K_n` of `f_n` over `ℚ`, taken inside `AlgebraicClosure ℚ`, and its Galois group
`Ω_n = Gal(f_n/ℚ)`; the iterated wreath product `[C₂]ⁿ`; and the sequence `c_1 = -a`,
`c_{n+1} = c_n² + a` of a parameter in a commutative ring.

## Main definitions

* `QuadraticIterates.iteratedPoly a n`: the `n`-th iterate `f_n` of `X² + a`.
* `QuadraticIterates.splittingField a n`: the splitting field `K_n` of `f_n`, `a ∈ ℚ`.
* `QuadraticIterates.GaloisGroup a n` and `QuadraticIterates.WreathPower n`: `Ω_n` and `[C₂]ⁿ`;
  the statement `Nonempty (GaloisGroup a n ≃* WreathPower n)` says that `Ω_n` is as large as
  possible.
* `QuadraticIterates.cSeq a`: the sequence `c_n`; `c_{n+1} = ± f_n(a)`
  (`QuadraticIterates.cSeq_succ_eq_neg_one_pow_mul_eval`), and `c` commutes with ring
  homomorphisms (`QuadraticIterates.map_cSeq`).

## Notation

`fℚ[a, n]` is scoped notation for `iteratedPoly (a : ℚ) n`, the iterate `f_n` over `ℚ`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-! ### The iterates `f_n` of `X² + a` -/

/-- The iterates `f_n` of `f = X² + a` over a commutative (semi)ring `R`: `f_0 = X`,
`f_{n+1} = f_n² + a`. Over `ℤ` (`R := ℤ`) this is the sequence of the paper. -/
noncomputable def iteratedPoly {R : Type*} [CommSemiring R] (a : R) : ℕ → R[X]
  | 0 => X
  | n + 1 => (iteratedPoly a n) ^ 2 + C a

section

variable {R : Type*} [CommSemiring R] (a : R)

@[simp] lemma iteratedPoly_zero : iteratedPoly a 0 = X := rfl

lemma iteratedPoly_succ (n : ℕ) : iteratedPoly a (n + 1) = iteratedPoly a n ^ 2 + C a := rfl

lemma iteratedPoly_one : iteratedPoly a 1 = X ^ 2 + C a := by
  rw [iteratedPoly_succ, iteratedPoly_zero]

lemma map_iteratedPoly {S : Type*} [CommSemiring S] (φ : R →+* S) (n : ℕ) :
    (iteratedPoly a n).map φ = iteratedPoly (φ a) n := by
  induction n <;> simp [iteratedPoly_succ, *]

lemma map_eval_iteratedPoly {S : Type*} [CommSemiring S] (φ : R →+* S) (x : R) (n : ℕ) :
    φ ((iteratedPoly a n).eval x) = (iteratedPoly (φ a) n).eval (φ x) := by
  rw [← map_iteratedPoly, eval_map, eval₂_at_apply]

/-- `f_{n+1} = f_n ∘ (X² + a)`: the iterate grows on the right as well as on the left
(`QuadraticIterates.iteratedPoly_succ`, `f_{n+1} = f_n ^ 2 + a`). -/
lemma iteratedPoly_succ_comp (n : ℕ) :
    iteratedPoly a (n + 1) = (iteratedPoly a n).comp (X ^ 2 + C a) := by
  induction n with
  | zero => simp [iteratedPoly_succ]
  | succ k ih =>
    nth_rw 1 [iteratedPoly_succ a (k + 1), ih]
    rw [iteratedPoly_succ, add_comp, pow_comp, C_comp]

lemma iteratedPoly_add (m n : ℕ) :
    iteratedPoly a (m + n) = (iteratedPoly a m).comp (iteratedPoly a n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iteratedPoly_succ_comp, ih, comp_assoc, ← iteratedPoly_succ_comp]

lemma eval_zero_iteratedPoly_succ (n : ℕ) :
    (iteratedPoly a (n + 1)).eval 0 = (iteratedPoly a n).eval a := by
  simp [iteratedPoly_succ_comp, eval_comp]

lemma monic_iteratedPoly [Nontrivial R] (n : ℕ) : (iteratedPoly a n).Monic := by
  induction n with
  | zero => exact monic_X
  | succ k ih =>
    rw [iteratedPoly_succ_comp]
    exact ih.comp (monic_X_pow_add_C a two_ne_zero) (by simp)

lemma natDegree_iteratedPoly [NoZeroDivisors R] [Nontrivial R] (n : ℕ) :
    (iteratedPoly a n).natDegree = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [iteratedPoly_succ_comp, natDegree_comp, ih, natDegree_X_pow_add_C, pow_succ]

@[simp] lemma iteratedPoly_zero_left (n : ℕ) : iteratedPoly (0 : R) n = X ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [iteratedPoly_succ, ih, ← pow_mul, ← pow_succ]

end

/-- The iterates `f_n` with `n ≥ 1` are even, `f_{n+1}(-X) = f_{n+1}`, because
`f_{n+1} = f_n ∘ (X² + a)`. -/
lemma iteratedPoly_succ_comp_neg_X {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (iteratedPoly a (n + 1)).comp (-X) = iteratedPoly a (n + 1) := by
  simp [iteratedPoly_succ_comp, comp_assoc]

/-! ### Splitting fields, Galois groups and wreath powers -/

/-- `fℚ[a, n]` denotes the `n`-th iterate `f_n` of `X² + a` over `ℚ`, `iteratedPoly (a : ℚ) n`. -/
scoped notation "fℚ[" a ", " n "]" => iteratedPoly (a : ℚ) n

/-- The iterate over `ℚ` evaluated at a rational number inside a field extension of `ℚ`: the cast
of its rational value. -/
lemma aeval_ratCast_iteratedPoly {S : Type*} [Field S] [Algebra ℚ S] (a x : ℚ) (n : ℕ) :
    aeval (x : S) (iteratedPoly a n) = (((iteratedPoly a n).eval x : ℚ) : S) := by
  rw [← eq_ratCast (algebraMap ℚ S) x, aeval_algebraMap_apply, coe_aeval_eq_eval, eq_ratCast]

/-- The splitting field `K_n` of `f_n` over `ℚ`, as the intermediate field of `AlgebraicClosure ℚ`
generated by the roots of `f_n`. -/
noncomputable abbrev splittingField (a : ℚ) (n : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (fℚ[a, n].rootSet (AlgebraicClosure ℚ))

instance splittingField.instIsSplittingField (a : ℚ) (n : ℕ) :
    IsSplittingField ℚ ↥(splittingField a n) fℚ[a, n] :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance splittingField.instFiniteDimensional (a : ℚ) (n : ℕ) :
    FiniteDimensional ℚ ↥(splittingField a n) :=
  IsSplittingField.finiteDimensional _ fℚ[a, n]

instance splittingField.instIsGalois (a : ℚ) (n : ℕ) : IsGalois ℚ ↥(splittingField a n) :=
  have : Normal ℚ ↥(splittingField a n) := Normal.of_isSplittingField fℚ[a, n]
  IsGalois.mk

/-- The Galois group `Ω_n = Gal(f_n/ℚ)` of the `n`-th iterate, via Mathlib's `Polynomial.Gal`. -/
noncomputable abbrev GaloisGroup (a : ℚ) (n : ℕ) : Type := fℚ[a, n].Gal

/-- The `n`-fold iterated regular wreath product `[C₂]ⁿ` of `C₂ = Multiplicative (ZMod 2)`, via
Mathlib's `IteratedWreathProduct`. -/
abbrev WreathPower (n : ℕ) : Type := IteratedWreathProduct (Multiplicative (ZMod 2)) n

/-- `[C₂]ⁿ` is built from `1 + 2 + ⋯ + 2^{n-1} = 2^n - 1` copies of `C₂`. -/
lemma card_wreathPower (n : ℕ) : Nat.card (WreathPower n) = 2 ^ (2 ^ n - 1) := by
  simp [IteratedWreathProduct.card, Nat.card_eq_fintype_card, Nat.geomSum_eq le_rfl]

lemma card_wreathPower_succ (n : ℕ) :
    Nat.card (WreathPower (n + 1)) = Nat.card (WreathPower n) * 2 ^ 2 ^ n := by
  rw [card_wreathPower, card_wreathPower, ← pow_add, pow_succ]
  congr 1
  lia

/-! ### The sequence `c` -/

section cSeq

variable {R : Type*} [CommRing R] (a : R)

/-- The sequence `c_n` (indexed from 1) of a parameter `a` in a commutative ring: `c_1 = -a`,
`c_{n+1} = c_n² + a`; the value at index `0` is `0`. It is the `γ`-sequence of `X² + a` with
`ε = -1`. Over `ℤ` this is the integer sequence of the paper, and `QuadraticIterates.intCast_cSeq`
identifies its cast into a ring `S` with the sequence of the cast parameter. -/
noncomputable def cSeq : ℕ → R := gammaSeq (X ^ 2 + C a) (-1)

lemma cSeq_eq_gammaSeq (n : ℕ) : cSeq a n = gammaSeq (X ^ 2 + C a) (-1) n := rfl

@[simp] lemma cSeq_zero : cSeq a 0 = 0 := rfl

@[simp] lemma cSeq_one : cSeq a 1 = -a := by simp [cSeq_eq_gammaSeq]

/-- The recursion `c_{n+1} = c_n² + a`. It only holds from `n = 1` on: `c_0 = 0` is a junk
value, and the sequence really starts at `c_1 = -a`. -/
theorem cSeq_succ {n : ℕ} (hn : 1 ≤ n) : cSeq a (n + 1) = cSeq a n ^ 2 + a := by
  simp [cSeq_eq_gammaSeq, gammaSeq_succ _ _ hn]

lemma cSeq_two : cSeq a 2 = a ^ 2 + a := by simp [cSeq_succ a le_rfl]

/-- `c_{k+1} = (-1)^{2^k} · f_k(a)`; in particular `c_{k+1} = f_k(a)` for `k ≥ 1`. -/
theorem cSeq_succ_eq_neg_one_pow_mul_eval (k : ℕ) :
    cSeq a (k + 1) = (-1) ^ 2 ^ k * (iteratedPoly a k).eval a := by
  induction k with
  | zero => simp [cSeq_one]
  | succ i ih =>
    have hone : (-1 : R) ^ 2 ^ (i + 1) = 1 := by simp [pow_succ, pow_mul']
    rw [cSeq_succ a (by lia), ih, iteratedPoly_succ]
    simp [mul_pow, ← pow_mul, ← pow_succ, hone]

/-- `c_{n+1} = (-1)^{2^n} · f_{n+1}(0)`: the sign is `-1` exactly for `n = 0`. -/
theorem cSeq_succ_eq_neg_one_pow_mul_eval_zero (n : ℕ) :
    cSeq a (n + 1) = (-1) ^ 2 ^ n * (iteratedPoly a (n + 1)).eval 0 := by
  rw [eval_zero_iteratedPoly_succ, cSeq_succ_eq_neg_one_pow_mul_eval]

lemma map_cSeq {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ) : φ (cSeq a n) = cSeq (φ a) n := by
  simp [cSeq_eq_gammaSeq, map_gammaSeq]

end cSeq

/-- The integer sequence `c` of an integer parameter, cast into a commutative ring `S`, is the
sequence of the cast parameter. -/
lemma intCast_cSeq {S : Type*} [CommRing S] (a : ℤ) (n : ℕ) :
    ((cSeq a n : ℤ) : S) = cSeq (a : S) n := by
  simpa using map_cSeq a (Int.castRingHom S) n

/-- The rational sequence `c` of a rational parameter, cast into a field `S` over `ℚ`, is the
sequence of the cast parameter. -/
lemma ratCast_cSeq {S : Type*} [Field S] [Algebra ℚ S] (a : ℚ) (n : ℕ) :
    ((cSeq a n : ℚ) : S) = cSeq (a : S) n := by
  simpa [eq_ratCast] using map_cSeq a (algebraMap ℚ S) n

end QuadraticIterates
