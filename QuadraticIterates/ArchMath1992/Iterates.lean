/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.RegularWreathProduct
public import QuadraticIterates.ArchMath1992.Sequences
public import QuadraticIterates.Mathlib.FieldTheory.Multiquadratic

import QuadraticIterates.Mathlib.Data.Fintype.Basic
import QuadraticIterates.Mathlib.FieldTheory.PolynomialGaloisGroup
import QuadraticIterates.Mathlib.GroupTheory.Card
import QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The iterates of `X² + a`, their splitting fields and Galois groups

The iterates `f_n` of `f = X² + a`, the splitting field `K_n` of `f_n` over `ℚ` taken inside
`AlgebraicClosure ℚ`, the Galois group `Ω_n = Gal(f_n/ℚ)` and the iterated wreath product `[C₂]ⁿ`;
the integer sequences `c_n` and `b_n` and the rescaled polynomial `normPoly a`; 2-independence.

## Main definitions

* `iteratedPoly a n`: the `n`-th iterate `f_n` of `X² + a` over a commutative semiring.
* `splittingField a n`: the splitting field `K_n` of `f_n` inside `AlgebraicClosure ℚ`.
* `GaloisGroup a n` and `WreathPower n`: the Galois group `Ω_n` and the wreath power `[C₂]ⁿ`.
* `cSeq a` and `bSeq a`: the integer sequences `c_n` and `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}`.
* `normPoly a`: the rescaling `|a|·X² + sign a` of `X² + a`.
* `TwoIndependent v`: no nonempty subfamily of `v` has a square product.

## Main statements

* `splittingField_succ_eq_sup_adjoin`, `relfinrank_succ_le` (Facts 1.0):
  `K_{n+1} = K_n(√(α - a) : α root of f_n)`, hence `[K_{n+1} : K_n] ≤ 2^{2^n}`.
* `odoni_embedding` (Odoni): `Ω_n` embeds into `[C₂]ⁿ`, being a `2`-group
  (`isPGroup_galoisGroup`) acting faithfully on the at most `2^n` roots of `f_n`; hence
  `Ω_n ≅ [C₂]ⁿ` iff `[K_n : ℚ] = 2^{2^n - 1}` (`nonempty_mulEquiv_iff_finrank_eq`).
* `nonempty_mulEquiv_succ_iff` (Lemma 1.4): `Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and
  `[K_{n+1} : K_n] = 2^{2^n}`.
* `twoIndependent_iff_linearIndependent`: a family is 2-independent iff its classes in
  `Lˣ/(Lˣ)²` are `𝔽₂`-linearly independent.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.

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

/-- Iterating commutes with any ring homomorphism: the image of `f_n` under `φ` is the `n`-th
iterate over the codomain with parameter `φ a`. -/
lemma map_iteratedPoly {S : Type*} [CommSemiring S] (φ : R →+* S) (n : ℕ) :
    (iteratedPoly a n).map φ = iteratedPoly (φ a) n := by
  induction n <;> simp [iteratedPoly_succ, *]

/-- Evaluation commutes with `map_iteratedPoly`: `φ (f_n(x)) = f_n^φ(φ x)`. -/
lemma map_eval_iteratedPoly {S : Type*} [CommSemiring S] (φ : R →+* S) (x : R) (n : ℕ) :
    φ ((iteratedPoly a n).eval x) = (iteratedPoly (φ a) n).eval (φ x) := by
  rw [← map_iteratedPoly, eval_map, eval₂_at_apply]

/-- `f_{n+1} = f_n ∘ (X² + a)`: the iterate can also grow on the right. -/
lemma iteratedPoly_succ_comp (n : ℕ) :
    iteratedPoly a (n + 1) = (iteratedPoly a n).comp (X ^ 2 + C a) := by
  induction n with
  | zero => simp [iteratedPoly_succ]
  | succ k ih =>
    nth_rw 1 [iteratedPoly_succ a (k + 1), ih]
    rw [iteratedPoly_succ, add_comp, pow_comp, C_comp]

/-- Iterates compose additively: `f_{m+n} = f_m ∘ f_n`. -/
lemma iteratedPoly_add (m n : ℕ) :
    iteratedPoly a (m + n) = (iteratedPoly a m).comp (iteratedPoly a n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iteratedPoly_succ_comp, ih, comp_assoc, ← iteratedPoly_succ_comp]

/-- `f_{n+1}(0) = f_n(a)`. -/
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

end

/-- The value of the integer iterate `f_n` at an integer, cast into any commutative ring `S`, is
the value of the iterate over `S`; this links `fℚ[a, n]` to the integer sequence `c`. -/
lemma intCast_eval_iteratedPoly {S : Type*} [CommRing S] (a x : ℤ) (n : ℕ) :
    (((iteratedPoly a n).eval x : ℤ) : S) = (iteratedPoly (a : S) n).eval (x : S) :=
  map_eval_iteratedPoly a (Int.castRingHom S) x n

/-- The iterates `f_n` with `n ≥ 1` are even, `f_{n+1}(-X) = f_{n+1}`, because
`f_{n+1} = f_n ∘ (X² + a)`. -/
lemma iteratedPoly_succ_comp_neg_X {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (iteratedPoly a (n + 1)).comp (-X) = iteratedPoly a (n + 1) := by
  simp [iteratedPoly_succ_comp, comp_assoc]

/-! ### Splitting fields, Galois groups and wreath powers -/

/-- `fℚ[a, n]` denotes the `n`-th iterate `f_n` of `X² + a` over `ℚ`, `iteratedPoly (a : ℚ) n`. -/
scoped notation "fℚ[" a ", " n "]" => iteratedPoly (a : ℚ) n

/-- `intCast_eval_iteratedPoly` for the iterate over `ℚ` evaluated in a `ℚ`-algebra. -/
lemma aeval_intCast_iteratedPoly {S : Type*} [CommRing S] [Algebra ℚ S] (a x : ℤ) (n : ℕ) :
    aeval (x : S) (fℚ[a, n]) = (((iteratedPoly a n).eval x : ℤ) : S) := by
  rw [aeval_def, ← eval_map, map_iteratedPoly, map_intCast, ← intCast_eval_iteratedPoly]

/-- The splitting field `K_n` of `f_n` over `ℚ`, as the intermediate field of `AlgebraicClosure ℚ`
generated by the roots of `f_n`. -/
noncomputable abbrev splittingField (a : ℤ) (n : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (fℚ[a, n].rootSet (AlgebraicClosure ℚ))

instance splittingField.instIsSplittingField (a : ℤ) (n : ℕ) :
    IsSplittingField ℚ ↥(splittingField a n) fℚ[a, n] :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance splittingField.instFiniteDimensional (a : ℤ) (n : ℕ) :
    FiniteDimensional ℚ ↥(splittingField a n) :=
  IsSplittingField.finiteDimensional _ fℚ[a, n]

instance splittingField.instIsGalois (a : ℤ) (n : ℕ) : IsGalois ℚ ↥(splittingField a n) :=
  have : Normal ℚ ↥(splittingField a n) := Normal.of_isSplittingField fℚ[a, n]
  IsGalois.mk

/-- The Galois group `Ω_n = Gal(f_n/ℚ)` of the `n`-th iterate, via Mathlib's `Polynomial.Gal`. -/
noncomputable abbrev GaloisGroup (a : ℤ) (n : ℕ) : Type := fℚ[a, n].Gal

/-- The `n`-fold iterated regular wreath product `[C_2]^n` of `C_2 = Multiplicative (ZMod 2)`, via
Mathlib's `IteratedWreathProduct`. -/
abbrev WreathPower (n : ℕ) : Type := IteratedWreathProduct (Multiplicative (ZMod 2)) n

/-! ### The sequences `c` and `b` over `ℤ` -/

/-- The integer sequence `c_n` (indexed from 1): `c_1 = -a`, `c_{n+1} = c_n² + a`; the value at
index `0` is `0`. It is the `γ`-sequence of `X² + a` with `ε = -1`. -/
noncomputable def cSeq (a : ℤ) : ℕ → ℤ := gammaSeq (X ^ 2 + C a) (-1)

lemma cSeq_eq_gammaSeq (a : ℤ) (n : ℕ) : cSeq a n = gammaSeq (X ^ 2 + C a) (-1) n := rfl

@[simp] lemma cSeq_zero (a : ℤ) : cSeq a 0 = 0 := rfl

@[simp] lemma cSeq_one (a : ℤ) : cSeq a 1 = -a := by simp [cSeq_eq_gammaSeq]

/-- The recursion `c_{n+1} = c_n² + a`. It only holds from `n = 1` on: `c_0 = 0` is a junk
value, and the sequence really starts at `c_1 = -a`. -/
theorem cSeq_succ (a : ℤ) {n : ℕ} (hn : 1 ≤ n) : cSeq a (n + 1) = cSeq a n ^ 2 + a := by
  simp [cSeq_eq_gammaSeq, gammaSeq_succ _ _ hn]

lemma cSeq_two (a : ℤ) : cSeq a 2 = a ^ 2 + a := by simp [cSeq_succ a le_rfl]

/-- **Strong divisibility** for the `c`-sequence: `gcd (c_m) (c_n) = |c_{gcd m n}|`. -/
theorem cSeq_gcd (a : ℤ) (m n : ℕ) : Int.gcd (cSeq a m) (cSeq a n) = (cSeq a (m.gcd n)).natAbs :=
  gammaSeq_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

/-- Strong divisibility of the `c`-sequence in the `Associated`-of-`gcd` form consumed by the
`moebiusFactorR` API. -/
theorem cSeq_associated_gcd (a : ℤ) (m n : ℕ) :
    Associated (gcd (cSeq a m) (cSeq a n)) (cSeq a (m.gcd n)) :=
  gammaSeq_associated_gcd (evenPoly_X_sq_add_C a) neg_one_sq m n

/-- `c_{k+1} = (-1)^{2^k} · f_k(a)`; in particular `c_{k+1} = f_k(a)` for `k ≥ 1`. -/
theorem cSeq_succ_eq_neg_one_pow_mul_eval (a : ℤ) (k : ℕ) :
    cSeq a (k + 1) = (-1) ^ 2 ^ k * (iteratedPoly a k).eval a := by
  induction k with
  | zero => simp [cSeq_one]
  | succ i ih =>
    have hone : (-1 : ℤ) ^ 2 ^ (i + 1) = 1 := by simp [pow_succ, pow_mul']
    rw [cSeq_succ a (by lia), ih, iteratedPoly_succ]
    simp [mul_pow, ← pow_mul, ← pow_succ, hone]

/-- `c_{n+1} = (-1)^{2^n} · f_{n+1}(0)`: the sign is `-1` exactly for `n = 0`. -/
theorem cSeq_succ_eq_neg_one_pow_mul_eval_zero (a : ℤ) (n : ℕ) :
    cSeq a (n + 1) = (-1) ^ 2 ^ n * (iteratedPoly a (n + 1)).eval 0 := by
  rw [eval_zero_iteratedPoly_succ, cSeq_succ_eq_neg_one_pow_mul_eval]

/-- `cSeq_succ_eq_neg_one_pow_mul_eval_zero` after casting to a commutative ring `S`. -/
lemma intCast_cSeq_succ_eq_neg_one_pow_mul_eval_zero {S : Type*} [CommRing S] (a : ℤ) (n : ℕ) :
    (cSeq a (n + 1) : S) = (-1) ^ 2 ^ n * (iteratedPoly (a : S) (n + 1)).eval 0 := by
  simp [cSeq_succ_eq_neg_one_pow_mul_eval_zero, intCast_eval_iteratedPoly]

/-- The Möbius factors `b_n = ∏_{d ∣ n} c_d^{μ(n/d)} ∈ ℤ` of the `c`-sequence: the specialization
of the general `β`-sequence to `X² + a`, `ε = -1` (an integer by strong divisibility, see
`intCast_bSeq`). -/
noncomputable def bSeq (a : ℤ) (n : ℕ) : ℤ := betaSeq (X ^ 2 + C a) (-1) n

lemma bSeq_eq_moebiusFactorR (a : ℤ) (n : ℕ) : bSeq a n = moebiusFactorR (cSeq a) n := rfl

@[simp] lemma bSeq_one (a : ℤ) : bSeq a 1 = -a := by simp [bSeq_eq_moebiusFactorR]

/-- The rescaling `|a|·X² + sign a` of `X² + a`. Substituting `x ↦ |a|·x` turns the recursion
`c_{n+1} = c_n² + a` into the `γ`-recursion of `normPoly a`, whose sequence is therefore
`|c_n| / |a|` (`abs_cSeq_eq_gammaSeq_mul_abs`) — in particular positive, which is what
Lemma 2.2 needs and `X² + a` itself does not provide. -/
noncomputable def normPoly (a : ℤ) : ℤ[X] := C |a| * X ^ 2 + C a.sign

@[simp] lemma eval_normPoly (a x : ℤ) : (normPoly a).eval x = |a| * x ^ 2 + a.sign := by
  simp [normPoly]

lemma evenPoly_normPoly (a : ℤ) : EvenPoly (normPoly a) := evenPoly_C_mul_X_sq_add_C |a| a.sign

/-! ### 2-independence -/

section TwoIndependent

variable {ι M : Type*}

/-- A family of elements of a commutative monoid is *2-independent* if no nonempty subfamily has
a square product. For nonzero rationals this says that the classes in `ℚ*/(ℚ*)²` are
`𝔽₂`-linearly independent (`twoIndependent_iff_linearIndependent`). -/
def TwoIndependent [CommMonoid M] (v : ι → M) : Prop :=
  ∀ S : Finset ι, S.Nonempty → ¬IsSquare (∏ i ∈ S, v i)

/-- No member of a 2-independent family is a square (the singleton subfamilies). -/
lemma TwoIndependent.not_isSquare [CommMonoid M] {v : ι → M} (h : TwoIndependent v) (i : ι) :
    ¬IsSquare (v i) := by
  simpa using h {i} (Finset.singleton_nonempty i)

/-- The members of a 2-independent family are nonzero, `0` being a square. -/
lemma TwoIndependent.ne_zero [CommMonoidWithZero M] {v : ι → M} (h : TwoIndependent v) (i : ι) :
    v i ≠ 0 :=
  fun hi ↦ h.not_isSquare i (hi ▸ IsSquare.zero)

/-- 2-independence of `Fin.snoc v c` restricts to the initial family `v`. -/
theorem TwoIndependent.of_snoc [CommMonoid M] {n : ℕ} {v : Fin n → M} {c : M}
    (h : TwoIndependent (Fin.snoc v c)) :
    TwoIndependent v := fun S hS ↦ by
  simpa [Fin.snoc_castSucc, Finset.prod_map S Fin.castSuccEmb (Fin.snoc v c)] using
    h (S.map Fin.castSuccEmb) hS.map

/-- `Fin.snoc v c` is 2-independent iff `v` is and `c` times no subproduct of `v` is a square. -/
theorem twoIndependent_snoc_iff [CommMonoid M] {n : ℕ} (v : Fin n → M) (c : M) :
    TwoIndependent (Fin.snoc v c) ↔
      TwoIndependent v ∧ ∀ S : Finset (Fin n), ¬IsSquare (c * ∏ i ∈ S, v i) := by
  have hprod (S : Finset (Fin n)) :
      ∏ i ∈ S.map Fin.castSuccEmb, Fin.snoc v c i = ∏ i ∈ S, v i := by
    simp [Fin.snoc_castSucc]
  refine ⟨fun h ↦ ⟨h.of_snoc, fun S ↦ ?_⟩, fun ⟨hv, hc⟩ T hT ↦ ?_⟩
  · simpa [Finset.prod_insert, hprod S, Fin.snoc_last] using
      h (insert (Fin.last n) (S.map Fin.castSuccEmb)) (Finset.insert_nonempty _ _)
  · obtain ⟨S, rfl | rfl⟩ := Fin.exists_eq_map_castSuccEmb_or_insert_last T
    · rw [hprod]
      exact hv S (Finset.map_nonempty.mp hT)
    · rw [Finset.prod_insert (by simp), Fin.snoc_last, hprod]
      exact hc S

/-- A family in a field `L` is 2-independent iff the family of its classes in `Lˣ/(Lˣ)²` is
`𝔽₂`-linearly independent. -/
theorem twoIndependent_iff_linearIndependent [Finite ι] {L : Type*} [Field L] [DecidableEq L]
    (v : ι → L) :
    TwoIndependent v ↔ LinearIndependent (ZMod 2) fun i ↦ sqClass (v i) := by
  have := Fintype.ofFinite ι
  refine ⟨fun h ↦ (rootRelations_eq_bot_iff v).mp ((Submodule.eq_bot_iff _).mpr fun ε hε ↦ ?_),
    fun H S hS hsq ↦ ?_⟩
  · by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact h {j | ε j = 1} ⟨i, by simpa using (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hi⟩
      ((mem_rootRelations fun i ↦ h.ne_zero i).mp hε)
  · classical
    have hv0 (i : ι) : v i ≠ 0 := fun hvi ↦ H.ne_zero i (by rw [hvi, sqClass_zero])
    have hmem : (fun j ↦ if j ∈ S then (1 : ZMod 2) else 0) ∈ rootRelations v :=
      (mem_rootRelations hv0).mpr (by simpa using hsq)
    obtain ⟨i, hiS⟩ := hS
    have h0 := (Submodule.mem_bot (ZMod 2)).mp (((rootRelations_eq_bot_iff v).mpr H).le hmem)
    simpa [hiS] using congrFun h0 i

/-- Square roots of a 2-independent family of radicands `r : ι → L` generate an extension of the
full degree `2^|ι|`: there are no relations in `multiquadratic_degree_family`. -/
theorem TwoIndependent.finrank_adjoin_range_eq_two_pow [Fintype ι] {L : Type*} [Field L]
    [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E] {r : ι → L} (hr : TwoIndependent r)
    {x : ι → E} (hx : ∀ i, x i ^ 2 = algebraMap L E (r i)) :
    Module.finrank L (IntermediateField.adjoin L (Set.range x)) = 2 ^ Fintype.card ι := by
  classical
  rw [multiquadratic_degree_family hx hr.ne_zero, (rootRelations_eq_bot_iff _).mpr
    ((twoIndependent_iff_linearIndependent _).mp hr), finrank_bot, Nat.sub_zero]

end TwoIndependent

/-! ### The iterates over `ℚ` -/

section

variable (a : ℤ)

lemma ncard_rootSet_iteratedPoly_le (n : ℕ) :
    (fℚ[a, n].rootSet (AlgebraicClosure ℚ)).ncard ≤ 2 ^ n :=
  (ncard_rootSet_le _ _).trans_eq (natDegree_iteratedPoly _ n)

lemma mem_rootSet_iteratedPoly_succ (n : ℕ) (β : AlgebraicClosure ℚ) :
    β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ) ↔
    β ^ 2 + (a : AlgebraicClosure ℚ) ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ) := by
  rw [mem_rootSet_of_ne (monic_iteratedPoly (a : ℚ) _).ne_zero,
    mem_rootSet_of_ne (monic_iteratedPoly (a : ℚ) _).ne_zero, iteratedPoly_succ_comp, aeval_comp]
  simp

/-- A square root `β` of `α - a`, for `α` a root of `f_n`, is a root of `f_{n+1}`. -/
lemma mem_rootSet_succ_of_sq_eq_sub {n : ℕ} {α β : AlgebraicClosure ℚ}
    (hα : α ∈ fℚ[a, n].rootSet (AlgebraicClosure ℚ)) (hβ : β ^ 2 = α - a) :
    β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ) :=
  (mem_rootSet_iteratedPoly_succ a n β).mpr (by rwa [hβ, sub_add_cancel])

/-! ### The tower of splitting fields `K_n ⊆ K_{n+1}` -/

/-- Every element of `ℚ̄` has a square root after subtracting `a`; the square roots of the
`α - a` for `α` a root of `f_n` are what generates `K_{n+1}` over `K_n`. -/
lemma exists_sq_eq_sub (α : AlgebraicClosure ℚ) :
    ∃ β : AlgebraicClosure ℚ, β ^ 2 = α - (a : AlgebraicClosure ℚ) :=
  IsAlgClosed.exists_pow_nat_eq _ two_pos

/-- `K_n ⊆ K_{n+1}`: a root `α` of `f_n` is `β² + a` for a root `β` of `f_{n+1}`. -/
lemma splittingField_le_succ (n : ℕ) : splittingField a n ≤ splittingField a (n + 1) := by
  refine IntermediateField.adjoin_le_iff.mpr fun α hα ↦ ?_
  obtain ⟨β, hβ⟩ := exists_sq_eq_sub a α
  rw [← sub_add_cancel α (a : AlgebraicClosure ℚ), ← hβ]
  exact add_mem (pow_mem (IntermediateField.subset_adjoin ℚ _
    (mem_rootSet_succ_of_sq_eq_sub a hα hβ)) 2) (IntermediateField.intCast_mem _ a)

lemma splittingField_mono {m n : ℕ} (hmn : m ≤ n) : splittingField a m ≤ splittingField a n :=
  monotone_nat_of_le_succ (splittingField_le_succ a) hmn

/-- `K_0 = ℚ`: the only root of `f_0 = X` is `0`. -/
@[simp] lemma splittingField_zero_eq_bot : splittingField a 0 = ⊥ := by
  refine IntermediateField.adjoin_eq_bot_iff.mpr fun x hx ↦ ?_
  obtain rfl : x = 0 := by simpa [mem_rootSet] using hx
  exact zero_mem _

/-- `K_{n+1} = K_n(√(α - a) : α root of f_n)`, for any choice `g` of square roots: a root `β` of
`f_{n+1}` is `± g(β² + a)`, and `g α` is a root of `f_{n+1}` for every root `α` of `f_n`. -/
theorem splittingField_succ_eq_sup_adjoin (n : ℕ) (g : AlgebraicClosure ℚ → AlgebraicClosure ℚ)
    (hg : ∀ α, g α ^ 2 = α - (a : AlgebraicClosure ℚ)) :
    splittingField a (n + 1) = splittingField a n ⊔
      IntermediateField.adjoin ℚ (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ))) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr fun β hβ ↦ ?_)
    (sup_le (splittingField_le_succ a n) (IntermediateField.adjoin_le_iff.mpr ?_))
  · have hgmem : g (β ^ 2 + a) ∈ splittingField a n ⊔
        IntermediateField.adjoin ℚ (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ))) :=
      SetLike.le_def.mp le_sup_right (IntermediateField.subset_adjoin ℚ _
        ⟨_, (mem_rootSet_iteratedPoly_succ a n β).mp hβ, rfl⟩)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show β ^ 2 = g (β ^ 2 + a) ^ 2 by
      rw [hg, add_sub_cancel_right]) with h | h
    · exact h ▸ hgmem
    · exact h ▸ neg_mem hgmem
  · intro x ⟨α, hα, hx⟩
    exact hx ▸ IntermediateField.subset_adjoin ℚ _ (mem_rootSet_succ_of_sq_eq_sub a hα (hg α))

/-- The square of a root of `f_{n+1}` lies in `K_n`: `K_n ⊆ K_{n+1}` is a `2`-Kummer extension. -/
lemma sq_mem_splittingField_of_mem_rootSet_succ {n : ℕ} {β : AlgebraicClosure ℚ}
    (hβ : β ∈ fℚ[a, n + 1].rootSet (AlgebraicClosure ℚ)) : β ^ 2 ∈ splittingField a n := by
  rw [← add_sub_cancel_right (β ^ 2) (a : AlgebraicClosure ℚ)]
  exact sub_mem
    (IntermediateField.subset_adjoin ℚ _ ((mem_rootSet_iteratedPoly_succ a n β).mp hβ))
    (IntermediateField.intCast_mem _ a)

/-- The relative degree `[K_{n+1} : K_n]` is the degree of the multiquadratic extension of `K_n`
generated by a choice `g` of square roots of the `α - a`, `α` a root of `f_n`. -/
theorem relfinrank_succ_eq_finrank_adjoin (n : ℕ) (g : AlgebraicClosure ℚ → AlgebraicClosure ℚ)
    (hg : ∀ α, g α ^ 2 = α - (a : AlgebraicClosure ℚ)) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = Module.finrank ↥(splittingField a n)
          ↥(IntermediateField.adjoin ↥(splittingField a n)
            (g '' (fℚ[a, n].rootSet (AlgebraicClosure ℚ)))) := by
  rw [splittingField_succ_eq_sup_adjoin a n g hg,
    ← IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.relfinrank_eq_finrank_of_le
      (by rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact le_sup_left)]
  rfl

/-- `[K_{n+1} : K_n] ≤ 2^{2^n}`: `K_{n+1}` is generated over `K_n` by at most `2^n` square
roots. -/
theorem relfinrank_succ_le (n : ℕ) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) ≤ 2 ^ 2 ^ n := by
  choose g hg using exists_sq_eq_sub a
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg]
  refine (IntermediateField.finrank_adjoin_sqrt_le_two_pow_ncard ((rootSet_finite _ _).image g)
    ?_).trans (Nat.pow_le_pow_right two_pos
      ((Set.ncard_image_le (rootSet_finite _ _)).trans (ncard_rootSet_iteratedPoly_le a n)))
  intro x ⟨α, hα, hx⟩
  exact ⟨⟨α - a, sub_mem (IntermediateField.subset_adjoin ℚ _ hα)
    (IntermediateField.intCast_mem _ a)⟩, hx ▸ hg α⟩

/-! ### Odoni's embedding `Ω_n ↪ [C₂]ⁿ` -/

/-- Any `ℚ`-automorphism of `ℚ̄` raised to the power `2 ^ m` fixes every root of `f_m`. -/
theorem pow_two_pow_apply_root (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {m : ℕ} {γ : AlgebraicClosure ℚ} (hγ : γ ∈ fℚ[a, m].rootSet (AlgebraicClosure ℚ)) :
    (φ ^ 2 ^ m) γ = γ := by
  induction m generalizing γ with
  | zero =>
    obtain rfl : γ = 0 := by simpa [mem_rootSet] using hγ
    simp
  | succ k ih =>
    have hsq : ((φ ^ 2 ^ k) γ) ^ 2 = γ ^ 2 := add_right_cancel (by
      simpa only [map_add, map_pow, map_intCast] using
        ih ((mem_rootSet_iteratedPoly_succ a k γ).mp hγ))
    rw [pow_succ, pow_mul, sq, AlgEquiv.mul_apply]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> simp only [h, map_neg, neg_neg]

/-- `Ω_n = Gal(f_n/ℚ)` is a 2-group. -/
theorem isPGroup_galoisGroup (n : ℕ) : IsPGroup 2 (GaloisGroup a n) := by
  set F := fℚ[a, n]
  refine isPGroup_iff_pow_pow_eq_one.mpr fun σ ↦ ⟨n, ?_⟩
  obtain ⟨φ, rfl⟩ := Gal.restrict_surjective F (AlgebraicClosure ℚ) σ
  apply Gal.galActionHom_injective F (AlgebraicClosure ℚ)
  rw [map_one, ← map_pow]
  exact Equiv.ext fun β ↦ Subtype.ext <|
    (Gal.galActionHom_restrict F (AlgebraicClosure ℚ) (φ ^ 2 ^ n) β).trans
      (pow_two_pow_apply_root a φ β.2)

/-- Odoni's embedding theorem: `Ω_n` embeds into `[C_2]^n`, being a `2`-group acting faithfully on
the at most `2 ^ n` roots of `f_n`. -/
theorem odoni_embedding (n : ℕ) : ∃ φ : GaloisGroup a n →* WreathPower n, Function.Injective φ :=
  (isPGroup_galoisGroup a n).exists_injective_monoidHom_iteratedWreathProduct
    (Gal.galActionHom_injective fℚ[a, n] (AlgebraicClosure ℚ))
    ((Nat.card_coe_set_eq _).trans_le (ncard_rootSet_iteratedPoly_le a n))
    (Multiplicative (ZMod 2)) (Nat.card_zmod 2)

/-! ### Lemma 1.4: `Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}` -/

/-- `[C_2]^n` is built from `1 + 2 + ⋯ + 2^{n-1} = 2^n - 1` copies of `C_2`. -/
lemma card_wreathPower (n : ℕ) : Nat.card (WreathPower n) = 2 ^ (2 ^ n - 1) := by
  simp [IteratedWreathProduct.card, Nat.card_eq_fintype_card, Nat.geomSum_eq le_rfl]

/-- `#[C_2]^{n+1} = #[C_2]^n · 2^{2^n}`. -/
lemma card_wreathPower_succ (n : ℕ) :
    Nat.card (WreathPower (n + 1)) = Nat.card (WreathPower n) * 2 ^ 2 ^ n := by
  rw [card_wreathPower, card_wreathPower, ← pow_add, pow_succ]
  congr 1
  lia

/-- `#Ω_n = [K_n : ℚ]`, since `K_n` is a Galois splitting field of `f_n` over `ℚ`. -/
lemma card_galoisGroup_eq_finrank (n : ℕ) :
    Nat.card (GaloisGroup a n) = Module.finrank ℚ ↥(splittingField a n) :=
  (Nat.card_congr (AlgEquiv.autCongr (IsSplittingField.algEquiv _ fℚ[a, n]).symm).toEquiv).trans
    (IsGalois.card_aut_eq_finrank ℚ _)

/-- `Ω_n ≅ [C_2]^n` iff `K_n` has the maximal possible degree `2^(2^n - 1)` over `ℚ`, since `Ω_n`
embeds into `[C_2]^n` (`odoni_embedding`) and `#Ω_n = [K_n : ℚ]`. -/
theorem nonempty_mulEquiv_iff_finrank_eq (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1) := by
  obtain ⟨φ, hφ⟩ := odoni_embedding a n
  rw [φ.nonempty_mulEquiv_iff_card_eq hφ, card_galoisGroup_eq_finrank, card_wreathPower]

/-- Lemma 1.4: `Ω_{n+1} ≅ [C_2]^{n+1}` iff `Ω_n ≅ [C_2]^n` and `[K_{n+1} : K_n] = 2^{2^n}`. Both
`#Ω_n ≤ #[C_2]^n` (by `odoni_embedding`) and `[K_{n+1} : K_n] ≤ 2^{2^n}`, and the products of the
two sides agree iff both factors do. -/
theorem nonempty_mulEquiv_succ_iff (n : ℕ) :
    Nonempty (GaloisGroup a (n + 1) ≃* WreathPower (n + 1)) ↔
      Nonempty (GaloisGroup a n ≃* WreathPower n) ∧
        (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n := by
  obtain ⟨φn, hφn⟩ := odoni_embedding a n
  obtain ⟨φn1, hφn1⟩ := odoni_embedding a (n + 1)
  rw [φn1.nonempty_mulEquiv_iff_card_eq hφn1, φn.nonempty_mulEquiv_iff_card_eq hφn,
    card_wreathPower_succ, card_galoisGroup_eq_finrank a (n + 1),
    ← IntermediateField.finrank_bot_mul_relfinrank (splittingField_le_succ a n),
    ← card_galoisGroup_eq_finrank]
  exact mul_eq_mul_iff_eq_and_eq_of_pos
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_injective φn hφn)) (relfinrank_succ_le a n)
    Nat.card_pos (Nat.two_pow_pos _)

end

end QuadraticIterates
