/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import QuadraticIterates.Mathlib.RingTheory.MoebiusFactor

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.BigOperators
import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Defs
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Algebra.GCDMonoid.Basic
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.RingTheory.PrincipalIdealDomain
import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt

/-!
# The iteration sequence of a polynomial and its Möbius factors

For `g ∈ R[X]` and a sign `ε`, the sequence `γ_1 = ε · g(0)`, `γ_{n+1} = g(γ_n)` and its Möbius
factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}`. The results are stated at the generality each one needs:
over a `CommSemiring` for the recursion, over a `CommRing` for the congruences, over a GCD domain
for strong divisibility, over a UFD for the valuation shape and the integrality of `β`, and
finally over `ℤ` for Lemmas 2.1 and 2.2 of the paper.

## Main statements

* `QuadraticIterates.EvenPoly`: `g` is even, i.e. `g ∈ R[X²]`; over a domain of characteristic `≠ 2`
  this is `g(-X) = g` (`QuadraticIterates.evenPoly_iff_comp_neg_X`).
* `QuadraticIterates.gammaSeq`, `QuadraticIterates.betaSeq`: the sequences `γ` and `β`.
  `QuadraticIterates.map_gammaSeq` says that `γ` commutes with ring homomorphisms, which is how the
  congruences of this file are computed in `ZMod m`.
* `QuadraticIterates.gammaSeq_associated_gcd`: strong divisibility of `γ` for even `g` and `ε² = 1`.
* `QuadraticIterates.gammaSeq_eq_ite_even_of_add_two_eq`,
  `QuadraticIterates.gammaSeq_eq_ite_even_of_add_two_eq_zero`,
  `QuadraticIterates.gammaSeq_two_sq_dvd_sub_ite_even`: the sequence is `2`-periodic from an index
  `n₀` on once `γ_{n₀+2} = ±γ_{n₀}`, and always modulo `γ_2²` when `γ_1 = 1`.
* `QuadraticIterates.factorization_gammaSeq_shape`: `v_p(γ_n)` is constant on the multiples of some
  index and `0` elsewhere.
* `QuadraticIterates.not_isSquare_betaSeq_of_prod_eq_neg_prod`: `β_n` is not a square in `ℚ` when
  the numerator and denominator of its Möbius product are congruent up to sign modulo an `m` with
  `-1` not a square mod `m`.
* `QuadraticIterates.not_isSquare_betaSeq_of_dvd_add_two_mul`,
  `QuadraticIterates.not_isSquare_betaSeq_of_dvd_add_succ`: Lemma 2.1 of the paper at a single index
  `n`, with a modulus dividing `γ_k + γ_{2k}` resp. `γ_k + γ_{k+1}` for `k = n / rad n` (Lemma 2.1
  and Corollary 2.4 of [Li 2021]).
* `QuadraticIterates.not_isSquare_betaSeq_of_even_of_dvd_add_two`,
  `QuadraticIterates.not_isSquare_betaSeq_of_odd_of_dvd_add_two`: Proposition 2.5 of [Li 2021],
  `β_n` is not a square with a modulus dividing `γ_k + γ_{k+2}`, using the `2`-periodicity
  `QuadraticIterates.gammaSeq_eq_ite_even_of_add_two_eq_zero` of the sequence modulo such an `m`.
* `QuadraticIterates.not_isSquare_betaSeq_of_squarefree_of_not_isSquare_neg_one`: Lemma 3.3 of
  [Li 2020], `β_n` for squarefree `n ≥ 3` with the modulus `γ_2`, when `g(0) = -1` and `γ_1 = 1`.
* `QuadraticIterates.not_isSquare_betaSeq`, `QuadraticIterates.not_isSquare_betaSeq_of_pos`:
  Lemmas 2.1 and 2.2 of the paper, `β_n` is not a square in `ℚ` for `n ≥ 2` under congruence
  conditions on `γ` resp. on `g(0)`, `g(1)`.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

/-! ### Even polynomials -/

section EvenPoly

variable {R : Type*} [CommSemiring R]

/-- `g` is an even polynomial (`g ∈ R[X²]`): `g = Polynomial.expand R 2 h` for some `h`. -/
def EvenPoly (g : R[X]) : Prop := ∃ h : R[X], g = expand R 2 h

namespace EvenPoly

variable {g : R[X]}

theorem eval_congr (hg : EvenPoly g) {x y : R} (h : x ^ 2 = y ^ 2) : g.eval x = g.eval y := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval, h]

theorem map {S : Type*} [CommSemiring S] (hg : EvenPoly g) (φ : R →+* S) : EvenPoly (g.map φ) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h.map φ, by rw [map_expand]⟩

end EvenPoly

lemma evenPoly_X_sq_add_C (a : R) : EvenPoly (X ^ 2 + C a) :=
  ⟨X + C a, by rw [map_add, expand_X, expand_C]⟩

lemma evenPoly_C_mul_X_sq_add_C (b c : R) : EvenPoly (C b * X ^ 2 + C c) :=
  ⟨C b * X + C c, by simp⟩

end EvenPoly

section EvenPoly

variable {R : Type*} [CommRing R] {g : R[X]}

namespace EvenPoly

theorem eval_neg (hg : EvenPoly g) (y : R) : g.eval (-y) = g.eval y := hg.eval_congr (neg_sq y)

/-- The iterates of the evaluation map of an even polynomial are even functions (`k ≥ 1`). -/
lemma iterate_eval_neg (hg : EvenPoly g) {k : ℕ} (hk : 1 ≤ k) (y : R) :
    (g.eval ·)^[k] (-y) = (g.eval ·)^[k] y := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hg.eval_neg]

lemma dvd_eval_sub (hg : EvenPoly g) {N a b : R} (h : N ∣ a ^ 2 - b ^ 2) :
    N ∣ g.eval a - g.eval b := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval]
  exact h.trans (sub_dvd_eval_sub (a ^ 2) (b ^ 2) h')

lemma comp_neg_X (hg : EvenPoly g) : g.comp (-X) = g := by
  obtain ⟨h, rfl⟩ := hg
  exact expand_two_comp_neg_X h

end EvenPoly

/-- Over a domain of characteristic `≠ 2`, `g` lies in `R[X²]` (`QuadraticIterates.EvenPoly g`) iff
it is invariant under `X ↦ -X`; the forward implication, `QuadraticIterates.EvenPoly.comp_neg_X`,
holds over every commutative ring. -/
lemma evenPoly_iff_comp_neg_X [NoZeroDivisors R] [NeZero (2 : R)] :
    EvenPoly g ↔ g.comp (-X) = g :=
  ⟨EvenPoly.comp_neg_X, fun h ↦ ⟨contract 2 g, eq_expand_two_contract_of_comp_neg_X_eq h⟩⟩

end EvenPoly

/-! ### The sequences `γ` and `β` -/

/-- The iteration sequence `γ_n` of `g ∈ R[X]` with sign choice `ε`: `γ_1 = ε · g(0)`, `γ_{n+1} =
g(γ_n)`; the value at index `0` is `0` (chosen so that over `ℤ`, `γ` is a strong divisibility
sequence). -/
def gammaSeq {R : Type*} [CommSemiring R] (g : R[X]) (ε : R) : ℕ → R
  | 0 => 0
  | 1 => ε * g.eval 0
  | n + 2 => g.eval (gammaSeq g ε (n + 1))

/-- The Möbius factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}` of the `γ`-sequence, as elements of the
coefficient ring: the unique preimage of the fraction-field Möbius product under
`R → FractionRing R` (junk when that product is not integral). -/
noncomputable def betaSeq {R : Type*} [CommRing R] [IsDomain R] (g : R[X]) (ε : R) (n : ℕ) : R :=
  moebiusFactorR (gammaSeq g ε) n

lemma betaSeq_eq_moebiusFactorR {R : Type*} [CommRing R] [IsDomain R] (g : R[X]) (ε : R) (n : ℕ) :
    betaSeq g ε n = moebiusFactorR (gammaSeq g ε) n := rfl

/-! ### The `γ`-sequence over a commutative semiring -/

section

variable {R : Type*} [CommSemiring R] (g : R[X])

@[simp] lemma gammaSeq_zero (ε : R) : gammaSeq g ε 0 = 0 := rfl

@[simp] lemma gammaSeq_one (ε : R) : gammaSeq g ε 1 = ε * g.eval 0 := rfl

lemma gammaSeq_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε (n + 1) = g.eval (gammaSeq g ε n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rfl

lemma gammaSeq_add (ε : R) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    gammaSeq g ε (m + n) = (g.eval ·)^[n] (gammaSeq g ε m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, gammaSeq_succ g ε (by lia), ih, Function.iterate_succ_apply']

lemma map_gammaSeq {S : Type*} [CommSemiring S] (φ : R →+* S) (ε : R) (n : ℕ) :
    φ (gammaSeq g ε n) = gammaSeq (g.map φ) (φ ε) n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [eval_zero_map]
    · rw [gammaSeq_succ g ε hm, gammaSeq_succ (g.map φ) (φ ε) hm, ← ih, eval_map_apply]

/-- The recursion `γ_{n+1} = g(γ_n)` for the `ε = 1` sequence, valid at every index (including `0`,
since `γ_0 = 0` and `γ_1 = g(0)`). -/
lemma gammaSeq_one_succ (n : ℕ) : gammaSeq g 1 (n + 1) = g.eval (gammaSeq g 1 n) := by
  cases n with
  | zero => simp
  | succ m => exact gammaSeq_succ g 1 (by lia)

variable {g}

/-- In a ring with `4 = 0`, the `ε = 1` sequence of an even `g` with `g(0) = 1`, `g(1) = 2`
alternates: `γ_n = 2` for even `n` and `γ_n = 1` for odd `n`. (The only property of `ZMod 4` used
in the mod-4 step is `4 = 0`, which gives `g(2) = g(0)` by evenness.) -/
theorem gammaSeq_eq_ite_even (hg : EvenPoly g) (h4 : (4 : R) = 0) (h0 : g.eval 0 = 1)
    (h1 : g.eval 1 = 2) : ∀ n ≥ 1, gammaSeq g 1 n = if Even n then 2 else 1 := by
  have h20 : g.eval 2 = 1 :=
    (hg.eval_congr (by rw [show (2 : R) ^ 2 = 4 by norm_num, h4, zero_pow two_ne_zero])).trans h0
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [h0]
  | succ k hk ih => grind [gammaSeq_succ g 1 hk, Nat.even_add_one]

/-- Consecutive terms of the alternating sequence of `QuadraticIterates.gammaSeq_eq_ite_even` sum to
`3`. -/
theorem gammaSeq_add_succ_eq_three (hg : EvenPoly g) (h4 : (4 : R) = 0) (h0 : g.eval 0 = 1)
    (h1 : g.eval 1 = 2) : ∀ n ≥ 1, gammaSeq g 1 n + gammaSeq g 1 (n + 1) = 3 := fun n hn ↦ by
  rw [gammaSeq_eq_ite_even hg h4 h0 h1 n hn, gammaSeq_eq_ite_even hg h4 h0 h1 (n + 1) (by lia)]
  simp only [Nat.even_add_one]
  split_ifs <;> norm_num

/-- If `ε² = g(0)² = g(1)² = 1` and `g` is even, then `γ_n = g(1)` for all `n ≥ 2`. (The only
property of `ZMod 8` used in the mod-8 step is that the relevant residues square to `1`.) -/
theorem gammaSeq_eq_eval_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1) (h0 : g.eval 0 ^ 2 = 1)
    (h1 : g.eval 1 ^ 2 = 1) : ∀ n ≥ 2, gammaSeq g ε n = g.eval 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact hg.eval_congr (by rw [gammaSeq_one, mul_pow, hε, one_mul, h0, one_pow])
  | succ k hk ih =>
    rw [gammaSeq_succ g ε (by lia), ih]
    exact hg.eval_congr (by rw [h1, one_pow])

/-- Consecutive terms of the eventually constant sequence of
`QuadraticIterates.gammaSeq_eq_eval_one` sum to `2·g(1)` (`n ≥ 2`). -/
theorem gammaSeq_add_succ_eq_two_mul_eval_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (h0 : g.eval 0 ^ 2 = 1) (h1 : g.eval 1 ^ 2 = 1) :
    ∀ n ≥ 2, gammaSeq g ε n + gammaSeq g ε (n + 1) = 2 * g.eval 1 := fun n hn ↦ by
  rw [gammaSeq_eq_eval_one hg hε h0 h1 n hn, gammaSeq_eq_eval_one hg hε h0 h1 (n + 1) (by lia),
    two_mul]

/-- For even `g` and `ε² = 1`, the `ε`-sequence *equals* the `ε = 1` sequence from index `2` on:
the sign is absorbed by the square inside `g`. -/
theorem gammaSeq_eq_gammaSeq_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    gammaSeq g ε n = gammaSeq g 1 n := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact hg.eval_congr (by rw [gammaSeq_one, gammaSeq_one, mul_pow, mul_pow, hε, one_pow])
  | succ k hk ih => rw [gammaSeq_succ g ε (by lia), gammaSeq_succ g 1 (by lia), ih]

lemma gammaSeq_one_associated_eval_zero {ε : R} (hε : IsUnit ε) :
    Associated (gammaSeq g ε 1) (g.eval 0) :=
  associated_unit_mul_left _ _ hε

/-- For even `g` and `ε² = 1`, the `ε`-sequence is associated to the `ε = 1` sequence: the two
agree from index `2` on and differ by the unit `ε` at index `1`. -/
theorem gammaSeq_associated_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1) (n : ℕ) :
    Associated (gammaSeq g ε n) (gammaSeq g 1 n) := by
  match n with
  | 0 => simp
  | 1 => simpa using gammaSeq_one_associated_eval_zero (IsUnit.of_pow_eq_one hε two_ne_zero)
  | (_ + 2) => rw [gammaSeq_eq_gammaSeq_one hg hε (by lia)]

end

/-! ### The `γ`-sequence over a commutative ring -/

section

variable {R : Type*} [CommRing R] (g : R[X])

/-- The `ε = 1` sequence satisfies the translation congruence `γ_m ∣ γ_{m+j} - γ_j`. -/
private lemma gammaSeq_one_dvd_sub (m j : ℕ) :
    gammaSeq g 1 m ∣ gammaSeq g 1 (m + j) - gammaSeq g 1 j := by
  induction j with
  | zero => simp
  | succ j ih => simpa [← add_assoc, gammaSeq_one_succ] using ih.trans (sub_dvd_eval_sub _ _ g)

variable {g}

/-- **Strong divisibility of the `γ`-sequence over a GCD domain**: for even `g` and `ε² = 1`,
`gcd (γ_m) (γ_n)` is associated to `γ_{gcd m n}`. -/
theorem gammaSeq_associated_gcd [IsDomain R] [NormalizedGCDMonoid R] (hg : EvenPoly g) {ε : R}
    (hε : ε ^ 2 = 1) (m n : ℕ) :
    Associated (gcd (gammaSeq g ε m) (gammaSeq g ε n)) (gammaSeq g ε (m.gcd n)) :=
  (((gammaSeq_associated_one hg hε m).gcd (gammaSeq_associated_one hg hε n)).trans
    (associated_gcd_of_dvd_sub rfl (gammaSeq_one_dvd_sub g) m n)).trans
    (gammaSeq_associated_one hg hε (m.gcd n)).symm

/-- Periodicity propagates along the recursion: a divisor of `γ_{n₀+m} - γ_{n₀}` divides
`γ_{n+m} - γ_n` for all `n ≥ n₀ ≥ 1`. -/
lemma gammaSeq_period {ε : R} {m n₀ : ℕ} (hn₀ : 1 ≤ n₀) {q : R}
    (hbase : q ∣ gammaSeq g ε (n₀ + m) - gammaSeq g ε n₀) :
    ∀ n ≥ n₀, q ∣ gammaSeq g ε (n + m) - gammaSeq g ε n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    rw [Nat.add_right_comm, gammaSeq_succ g ε (by lia), gammaSeq_succ g ε (by lia)]
    exact ih.trans (sub_dvd_eval_sub _ _ g)

lemma sq_dvd_gammaSeq_succ_sub (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε n ^ 2 ∣ gammaSeq g ε (n + 1) - g.eval 0 := by
  rw [gammaSeq_succ g ε hn]
  exact hg.dvd_eval_sub (by simp)

/-- `QuadraticIterates.sq_dvd_gammaSeq_succ_sub` in the form
`QuadraticIterates.factorization_gammaSeq_shape` consumes: `p ^ E ∣ γ_n` with `E ≥ 1` gives
`p ^ (E + 1) ∣ γ_{n+1} - g(0)`, since `2E ≥ E + 1` (for any `p`, prime or not). -/
lemma pow_succ_dvd_gammaSeq_succ_sub (hg : EvenPoly g) {ε : R} {n : ℕ} (hn : 1 ≤ n) {p : R}
    {E : ℕ} (hE : 1 ≤ E) (hpE : p ^ E ∣ gammaSeq g ε n) :
    p ^ (E + 1) ∣ gammaSeq g ε (n + 1) - g.eval 0 :=
  calc p ^ (E + 1) ∣ p ^ (2 * E) := pow_dvd_pow p (by lia)
    _ ∣ gammaSeq g ε n ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hpE 2
    _ ∣ gammaSeq g ε (n + 1) - g.eval 0 := sq_dvd_gammaSeq_succ_sub hg ε hn

/-- If `g` is even with `g(0)² = 1` and `γ_1 = 1`, then modulo `γ_2²` the sequence alternates
from index `2` on: `γ_n ≡ γ_2` for even `n` and `γ_n ≡ g(0)` for odd `n ≥ 3`. -/
theorem gammaSeq_two_sq_dvd_sub_ite_even (hg : EvenPoly g) {ε : R} (h0 : g.eval 0 ^ 2 = 1)
    (h1 : gammaSeq g ε 1 = 1) :
    ∀ n ≥ 2, gammaSeq g ε 2 ^ 2 ∣ gammaSeq g ε n - if Even n then gammaSeq g ε 2 else g.eval 0 := by
  have h2 : gammaSeq g ε 2 = g.eval 1 := by rw [gammaSeq_succ g ε le_rfl, h1]
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    simp only [Nat.even_add_one]
    split_ifs with he
    · rw [ite_eq_left he] at ih
      exact (pow_dvd_pow_of_dvd ((dvd_sub_left dvd_rfl).mp ((dvd_pow_self _ two_ne_zero).trans ih))
        2).trans (sq_dvd_gammaSeq_succ_sub hg ε (by lia))
    · rw [ite_eq_right he] at ih
      rw [gammaSeq_succ g ε (n := n) (by lia)]
      nth_rw 2 [h2]
      refine hg.dvd_eval_sub ?_
      rw [show gammaSeq g ε n ^ 2 - 1 ^ 2
          = (gammaSeq g ε n - g.eval 0) * (gammaSeq g ε n + g.eval 0) by linear_combination h0]
      exact ih.mul_right _

/-- For even `g` with `g(0)² = 1` and `γ_1 = 1`, `γ_2` divides `γ_n` for every even `n ≥ 2`. -/
theorem gammaSeq_two_dvd_of_even (hg : EvenPoly g) {ε : R} (h0 : g.eval 0 ^ 2 = 1)
    (h1 : gammaSeq g ε 1 = 1) {n : ℕ} (hn : 2 ≤ n) (hne : Even n) :
    gammaSeq g ε 2 ∣ gammaSeq g ε n :=
  (dvd_sub_left dvd_rfl).mp ((dvd_pow_self _ two_ne_zero).trans
    (by simpa [ite_eq_left hne] using gammaSeq_two_sq_dvd_sub_ite_even hg h0 h1 n hn))

/-- A divisor `q` of `γ_{m+1} - g(0)` is a period divisor of `γ` from index `2` on, i.e.
`q ∣ γ_{n+m} - γ_n` for all `n ≥ 2` (for even `g` and `ε² = 1`, so that `γ_1² = g(0)²`). -/
lemma gammaSeq_period_of_dvd_succ_sub_eval_zero (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    {m : ℕ} {q : R} (hq : q ∣ gammaSeq g ε (m + 1) - g.eval 0) :
    ∀ n ≥ 2, q ∣ gammaSeq g ε (n + m) - gammaSeq g ε n := by
  refine gammaSeq_period one_le_two ?_
  rw [show 2 + m = m + 1 + 1 by ring, gammaSeq_succ g ε (by lia), show (2 : ℕ) = 1 + 1 from rfl,
    gammaSeq_succ g ε le_rfl]
  refine hg.dvd_eval_sub ?_
  have h1 : gammaSeq g ε 1 ^ 2 = g.eval 0 ^ 2 := by rw [gammaSeq_one, mul_pow, hε, one_mul]
  rw [h1, sq_sub_sq]
  exact hq.mul_left _

/-- If `γ_k + γ_{2k} = 0`, then `γ_{lk} = γ_{2k}` for all `l ≥ 2` (over any ring, for even `g`):
`γ` is constant on positive multiples of `k` past the first. -/
theorem gammaSeq_mul_eq_two_mul (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) :
    ∀ l ≥ 2, gammaSeq g ε (l * k) = gammaSeq g ε (2 * k) := by
  have hneg : gammaSeq g ε (2 * k) = -gammaSeq g ε k := by linear_combination hzero
  have hfix : (g.eval ·)^[k] (gammaSeq g ε (2 * k)) = gammaSeq g ε (2 * k) := by
    rw [hneg, hg.iterate_eval_neg hk, ← gammaSeq_add g ε hk, ← two_mul, hneg]
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
    rw [show (l + 1) * k = l * k + k by ring, gammaSeq_add g ε (one_le_mul (by lia) hk), ih, hfix]

/-- If `γ_k + γ_{2k} = 0` and `γ_{2k}` is a unit, then `∏_{t ∈ S} γ_{kt}` is a unit for every set
`S` of positive indices (over any ring, for even `g`): every factor is `±γ_{2k}`. -/
theorem isUnit_prod_gammaSeq_mul (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) (hu : IsUnit (gammaSeq g ε (2 * k)))
    {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) : IsUnit (∏ t ∈ S, gammaSeq g ε (k * t)) := by
  refine IsUnit.prod_iff.mpr fun t ht ↦ ?_
  rcases eq_or_ne t 1 with rfl | h1
  · rw [mul_one, show gammaSeq g ε k = -gammaSeq g ε (2 * k) by linear_combination hzero]
    exact hu.neg
  · rw [mul_comm, gammaSeq_mul_eq_two_mul hg hk hzero t (by have := hS t ht; lia)]
    exact hu

/-- If `γ_k + γ_{2k} = 0`, then the products of the `γ_{kt}` over the two halves of the sign
partition of the divisors `t` of a squarefree `n' > 1` (by `μ (n'/t) = ±1`) are negatives of each
other (over any ring, for even `g`): all factors equal `γ_{2k}` except `γ_k = -γ_{2k}` at `t = 1`,
and the two halves have the same size. -/
theorem prod_gammaSeq_mul_eq_neg_prod (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) {n' : ℕ} (hsf : Squarefree n')
    (hn'1 : 1 < n') :
    ∏ t ∈ n'.divisors with μ (n' / t) = 1, gammaSeq g ε (k * t)
      = -∏ t ∈ n'.divisors with μ (n' / t) = -1, gammaSeq g ε (k * t) := by
  have hunion := hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one
  refine Finset.prod_eq_neg_prod_of_forall_card_filter_eq (κ := fun _ ↦ ())
    (w := fun _ ↦ gammaSeq g ε (2 * k)) (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia)
    (by rw [hunion]; exact Nat.one_mem_divisors.mpr (by lia))
    (by rw [mul_one]; linear_combination hzero)
    (fun t ht h1 ↦ ?_) fun _ ↦ by
      simpa using hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one subset_rfl
        (ArithmeticFunction.sum_divisors_moebius_div_eq_zero hn'1)
  have := Nat.pos_of_mem_divisors (hunion ▸ ht)
  rw [mul_comm]
  exact gammaSeq_mul_eq_two_mul hg hk hzero t (by lia)

/-- If `γ_{n₀+2} = γ_{n₀}` (`n₀ ≥ 1`), then the sequence is `2`-periodic from index `n₀` on:
`γ_n = γ_{n₀}` for `n ≡ n₀ mod 2` and `γ_n = γ_{n₀+1}` otherwise, for all `n ≥ n₀`. -/
theorem gammaSeq_eq_ite_even_of_add_two_eq (g : R[X]) {ε : R} {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (h : gammaSeq g ε (n₀ + 2) = gammaSeq g ε n₀) :
    ∀ n ≥ n₀,
      gammaSeq g ε n = if Even (n + n₀) then gammaSeq g ε n₀ else gammaSeq g ε (n₀ + 1) := by
  have h1 : g.eval (gammaSeq g ε n₀) = gammaSeq g ε (n₀ + 1) := (gammaSeq_succ g ε hn₀).symm
  have h2 : g.eval (gammaSeq g ε (n₀ + 1)) = gammaSeq g ε n₀ := by
    rw [← h, gammaSeq_succ g ε (n := n₀ + 1) (by lia)]
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => grind [Nat.even_add_one]
  | succ n hn ih => grind [gammaSeq_succ g ε (by lia : 1 ≤ n), Nat.even_add_one]

/-- **2-periodicity.** If `γ_k + γ_{k+2} = 0` (`k ≥ 1`), then the sequence is `2`-periodic from
index `k + 1` on: `γ_r = -γ_k` for `r ≡ k mod 2` and `γ_r = γ_{k+1}` otherwise, for all
`r ≥ k + 1` (over any ring, for even `g`). -/
theorem gammaSeq_eq_ite_even_of_add_two_eq_zero (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (k + 2) = 0) :
    ∀ r ≥ k + 1,
      gammaSeq g ε r = if Even (r + k) then -gammaSeq g ε k else gammaSeq g ε (k + 1) := by
  have h1 : g.eval (-gammaSeq g ε k) = gammaSeq g ε (k + 1) := by
    rw [hg.eval_neg, gammaSeq_succ g ε hk]
  have h2 : g.eval (gammaSeq g ε (k + 1)) = -gammaSeq g ε k := by
    rw [← gammaSeq_succ g ε (by lia)]
    linear_combination hzero
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => grind [Nat.even_add_one]
  | succ r hr ih => grind [gammaSeq_succ g ε (by lia : 1 ≤ r), Nat.even_add_one]

/-- If `g` is even with `g(0)² = 1` and `g(1) = 0`, and `γ_1 = 1`, then the sequence
`1, 0, g(0), 0, g(0), …` alternates from index `2` on: `γ_n = 0` for even `n` and `γ_n = g(0)` for
odd `n ≥ 3`. -/
theorem gammaSeq_eq_ite_even_of_eval_one_eq_zero (hg : EvenPoly g) {ε : R} (h0 : g.eval 0 ^ 2 = 1)
    (h1 : gammaSeq g ε 1 = 1) (hg1 : g.eval 1 = 0) :
    ∀ n ≥ 2, gammaSeq g ε n = if Even n then 0 else g.eval 0 := by
  have h2 : gammaSeq g ε 2 = 0 := by rw [gammaSeq_succ g ε le_rfl, h1, hg1]
  have h3 : gammaSeq g ε 3 = g.eval 0 := by rw [gammaSeq_succ g ε one_le_two, h2]
  have h4 : gammaSeq g ε (2 + 2) = gammaSeq g ε 2 := by
    rw [gammaSeq_succ g ε (by lia), h3, h2]
    exact (hg.eval_congr (by rw [h0, one_pow])).trans hg1
  intro n hn
  rw [gammaSeq_eq_ite_even_of_add_two_eq g one_le_two h4 n hn, h2, h3]
  simp [Nat.even_add]

/-- For odd `k` with `γ_k + γ_{k+2} = 0`, the value `γ_{kt}` for `t ≥ 2` depends only on the parity
of `t`: it is `γ_{k+1}` for even `t` and `-γ_k` for odd `t`. -/
theorem gammaSeq_mul_eq_ite_even_of_odd (hg : EvenPoly g) {ε : R} {k : ℕ} (hko : Odd k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (k + 2) = 0) {t : ℕ} (ht : 2 ≤ t) :
    gammaSeq g ε (k * t) = if Even t then gammaSeq g ε (k + 1) else -gammaSeq g ε k := by
  have := Nat.mul_le_mul_left k ht
  have := hko.pos
  rw [gammaSeq_eq_ite_even_of_add_two_eq_zero hg hko.pos hzero (k * t) (by lia)]
  grind [Nat.not_even_iff_odd]

/-- For odd `k` with `γ_k + γ_{k+2} = 0`, `∏_{t ∈ S} γ_{kt}` is a unit for every set `S` of positive
indices once `γ_k` and `γ_{k+1}` are units: every factor is one of `γ_k`, `-γ_k`, `γ_{k+1}`. -/
theorem isUnit_prod_gammaSeq_mul_of_odd (hg : EvenPoly g) {ε : R} {k : ℕ} (hko : Odd k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (k + 2) = 0) (hu : IsUnit (gammaSeq g ε k))
    (hu1 : IsUnit (gammaSeq g ε (k + 1))) {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) :
    IsUnit (∏ t ∈ S, gammaSeq g ε (k * t)) := by
  refine IsUnit.prod_iff.mpr fun t ht ↦ ?_
  rcases eq_or_ne t 1 with rfl | h1
  · rwa [mul_one]
  · rw [gammaSeq_mul_eq_ite_even_of_odd hg hko hzero (by have := hS t ht; lia)]
    split_ifs
    exacts [hu1, hu.neg]

/-- For odd `k` with `γ_k + γ_{k+2} = 0`, the products of the `γ_{kt}` over the two halves of the
sign partition of the divisors `t` of a squarefree `n' ≥ 3` are negatives of each other (over any
ring, for even `g`): the factors are `γ_{k+1}` for even `t` and `-γ_k` for odd `t`, except `γ_k` at
`t = 1`, and the two halves contain equally many odd and equally many even divisors. -/
theorem prod_gammaSeq_mul_eq_neg_prod_of_odd (hg : EvenPoly g) {ε : R} {k : ℕ} (hko : Odd k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (k + 2) = 0) {n' : ℕ} (hsf : Squarefree n')
    (hn'3 : 3 ≤ n') :
    ∏ t ∈ n'.divisors with μ (n' / t) = 1, gammaSeq g ε (k * t)
      = -∏ t ∈ n'.divisors with μ (n' / t) = -1, gammaSeq g ε (k * t) := by
  have hunion := hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one
  refine Finset.prod_eq_neg_prod_of_forall_card_filter_eq (κ := (· % 2))
    (w := fun i ↦ if i = 0 then gammaSeq g ε (k + 1) else -gammaSeq g ε k)
    (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia)
    (by rw [hunion]; exact Nat.one_mem_divisors.mpr (by lia)) (by simp) (fun t ht h1 ↦ ?_)
    fun i ↦ by
      simpa [Finset.filter_filter, and_comm] using
        hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one (Finset.filter_subset _ _)
          (ArithmeticFunction.sum_divisors_filter_mod_two_moebius_div hn'3 i)
  have := Nat.pos_of_mem_divisors (hunion ▸ ht)
  rw [gammaSeq_mul_eq_ite_even_of_odd hg hko hzero (by lia)]
  simp only [Nat.even_iff]

/-- For even `g`, `γ_n + γ_{n+1}` divides `γ_{n+j} - γ_{n+1}` for all `j ≥ 1` (`n ≥ 1`): modulo
`γ_n + γ_{n+1}` one has `g(γ_{n+1}) ≡ g(-γ_n) = γ_{n+1}`, so the sequence is constant from index
`n + 1` on. -/
lemma gammaSeq_add_succ_dvd_sub (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    ∀ j ≥ 1,
      gammaSeq g ε n + gammaSeq g ε (n + 1) ∣ gammaSeq g ε (n + j) - gammaSeq g ε (n + 1) := by
  have hfix : gammaSeq g ε n + gammaSeq g ε (n + 1) ∣
      g.eval (gammaSeq g ε (n + 1)) - gammaSeq g ε (n + 1) := by
    have h := sub_dvd_eval_sub (gammaSeq g ε (n + 1)) (-gammaSeq g ε n) g
    rwa [sub_neg_eq_add, add_comm, hg.eval_neg, ← gammaSeq_succ g ε hn] at h
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [← add_assoc, gammaSeq_succ g ε (n := n + j) (by lia),
      ← sub_add_sub_cancel _ (g.eval (gammaSeq g ε (n + 1))) _]
    exact dvd_add (ih.trans (sub_dvd_eval_sub _ _ g)) hfix

/-- For even `g`, `γ_n + γ_{n+1}` divides `γ_n + γ_{2n}` (`n ≥ 1`), since `γ_{2n} ≡ γ_{n+1}`
modulo the left-hand side. -/
lemma gammaSeq_add_succ_dvd (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε n + gammaSeq g ε (n + 1) ∣ gammaSeq g ε n + gammaSeq g ε (2 * n) := by
  have h := dvd_add (dvd_refl _) (gammaSeq_add_succ_dvd_sub hg ε hn n hn)
  rwa [add_add_sub_cancel, ← two_mul] at h

/-- `γ_{n+1} ≡ g(0)` modulo `γ_n`, so `γ_n + γ_{n+1}` and `γ_n` are coprime once `g(0)` is a
unit (`n ≥ 1`). -/
lemma isCoprime_gammaSeq_add_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) (h0 : IsUnit (g.eval 0)) :
    IsCoprime (gammaSeq g ε n + gammaSeq g ε (n + 1)) (gammaSeq g ε n) := by
  obtain ⟨k, hk⟩ := sub_dvd_eval_sub (gammaSeq g ε n) 0 g
  have heq : gammaSeq g ε n + gammaSeq g ε (n + 1) = g.eval 0 + gammaSeq g ε n * (1 + k) := by
    rw [gammaSeq_succ g ε hn]; linear_combination hk
  rw [heq]
  exact ((isCoprime_zero_right.mpr h0).of_isCoprime_of_dvd_right (dvd_zero _)).add_mul_left_left _

end

/-! ### Valuations of the `γ`-sequence over a UFD -/

section

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R] {g : R[X]}

lemma factorization_gammaSeq_of_dvd_eval_zero (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p)
    (hpg : p ∣ g.eval 0) {n : ℕ} (hn : 1 ≤ n) :
    factorization (gammaSeq g ε n) p = factorization (g.eval 0) p := by
  have hg0 : g.eval 0 ≠ 0 := fun h ↦ hne 1 le_rfl (by rw [gammaSeq_one, h, mul_zero])
  have hv1 := (one_le_factorization_iff_dvd hp hpn hg0).mpr hpg
  induction n, hn using Nat.le_induction with
  | base =>
    rw [(gammaSeq_one_associated_eval_zero (IsUnit.of_pow_eq_one hε two_ne_zero)).factorization_eq]
  | succ k hk ih =>
    refine factorization_eq_of_dvd_sub hp hpn (hne (k + 1) (by lia)) hg0 rfl ?_
    exact pow_succ_dvd_gammaSeq_succ_sub hg hk hv1
      ((pow_dvd_iff_le_factorization hp hpn (hne k hk)).mpr ih.ge)

/-- The main case: if `p ∤ g(0)` but `p` divides some `γ_m`, the valuation `v_p(γ_n)` is
supported on the multiples of the minimal such index `m`, with constant value. -/
private lemma factorization_gammaSeq_shape_of_exists (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p)
    (hpg : ¬p ∣ g.eval 0) (hex : ∃ k : ℕ, 1 ≤ k ∧ p ∣ gammaSeq g ε k) :
    ∃ m ≥ 1, ∃ E : ℕ, ∀ n ≥ 1, factorization (gammaSeq g ε n) p = if m ∣ n then E else 0 := by
  classical
  obtain ⟨m, ⟨hm1, hpm⟩, hmin⟩ := Nat.findX hex
  have hm2 : 2 ≤ m :=
    hm1.lt_of_ne' fun h ↦ hpg ((gammaSeq_one_associated_eval_zero
      (IsUnit.of_pow_eq_one hε two_ne_zero)).dvd_iff_dvd_right.mp (h ▸ hpm))
  set E := factorization (gammaSeq g ε m) p with hE
  have hE1 := (one_le_factorization_iff_dvd hp hpn (hne m hm1)).mpr hpm
  -- `p^{E+1} ∣ γ_{m+1} - g(0)` via `γ_m² ∣ γ_{m+1} - g(0)`
  have hcm1 := pow_succ_dvd_gammaSeq_succ_sub hg hm1 hE1
    ((pow_dvd_iff_le_factorization hp hpn (hne m hm1)).mpr le_rfl)
  exact ⟨m, hm1, E, factorization_periodic_shape hp hpn hm2 hne hE.symm
    (fun k hk h1 hd ↦ hmin k hk ⟨h1, hd⟩)
    (fun hdvd ↦ hpg ((dvd_sub_right hdvd).mp ((dvd_pow_self p E.succ_ne_zero).trans hcm1)))
    (gammaSeq_period_of_dvd_succ_sub_eval_zero hg hε hcm1)⟩

/-- **Constant-valuation shape of the `γ`-sequence over a UFD** (for even `g`, `ε² = 1`, `γ`
nowhere zero): for each normalized prime `p`, the valuation `v_p(γ_n)` equals a constant `E`
on the multiples of some index `m ≥ 1` and vanishes elsewhere. -/
theorem factorization_gammaSeq_shape (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p) :
    ∃ m ≥ 1, ∃ E : ℕ, ∀ n ≥ 1, factorization (gammaSeq g ε n) p = if m ∣ n then E else 0 := by
  by_cases hpg : p ∣ g.eval 0
  · exact ⟨1, le_rfl, factorization (g.eval 0) p, fun n hn ↦ by
      simpa using factorization_gammaSeq_of_dvd_eval_zero hg hε hne hp hpn hpg hn⟩
  · by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ p ∣ gammaSeq g ε k
    · exact factorization_gammaSeq_shape_of_exists hg hε hne hp hpn hpg hex
    · exact ⟨1, le_rfl, 0, fun n hn ↦ by
        simpa [factorization_eq_zero_iff_not_dvd hp hpn (hne n hn)] using fun hd ↦ hex ⟨n, hn, hd⟩⟩

end

/-! ### The `γ`- and `β`-sequences over `ℤ` -/

section

open ArithmeticFunction UniqueFactorizationMonoid
open scoped Finset

variable (g : ℤ[X])

lemma intCast_gammaSeq (ε : ℤ) (S : Type*) [CommRing S] (i : ℕ) : ((gammaSeq g ε i : ℤ) : S)
    = gammaSeq (g.map (Int.castRingHom S)) (ε : S) i :=
  map_gammaSeq g (Int.castRingHom S) ε i

variable {g}

/-- **Strong divisibility** over `ℤ`, for even `g` and `ε = ±1`:
`gcd (γ_m) (γ_n) = |γ_{gcd m n}|`. -/
theorem gammaSeq_gcd (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1) (m n : ℕ) :
    Int.gcd (gammaSeq g ε m) (gammaSeq g ε n) = (gammaSeq g ε (m.gcd n)).natAbs := by
  rw [← Int.natAbs_gcd, Int.associated_iff_natAbs.mp (gammaSeq_associated_gcd hg hε m n)]

/-- The image of `β_n` in `ℚ` is the Möbius product `∏_{ed = n} γ_d^{μ(e)}` (for even `g`,
`ε = ±1`, and `γ` nowhere zero on positive indices): the specialization of
`algebraMap_moebiusFactorR` to `ℤ ⊆ ℚ`, by strong divisibility. -/
lemma intCast_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ((betaSeq g ε n : ℤ) : ℚ) = moebiusFactorK (gammaSeq g ε) n :=
  algebraMap_moebiusFactorR hγ (gammaSeq_associated_gcd hg hε) hn

/-- **`β_n` from a congruence between numerator and denominator.** For `n ≥ 1`, `n' = rad n` and
`k = n / n'`, let `P` and `Q` be the products of the `γ_{kt}` over the divisors `t` of `n'` with
`μ (n'/t) = 1` resp. `μ (n'/t) = -1`, so that `β_n = P / Q`, and let `P = c P'`, `Q = c Q'` with
`c ≠ 0`. If `P' ≡ -Q' mod m` with `Q'` a unit mod `m`, and `-1` is not a square mod `m`, then
`β_n` is not a square in `ℚ`. -/
theorem not_isSquare_betaSeq_of_prod_eq_neg_prod (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {n k n' : ℕ} (hn : 1 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') {c P Q : ℤ} (hc : c ≠ 0)
    (hP : ∏ t ∈ n'.divisors with μ (n' / t) = 1, gammaSeq g ε (k * t) = c * P)
    (hQ : ∏ t ∈ n'.divisors with μ (n' / t) = -1, gammaSeq g ε (k * t) = c * Q)
    {m : ℕ} (hPQ : (P : ZMod m) = -(Q : ZMod m)) (hQu : IsUnit (Q : ZMod m))
    (hnsq : ¬IsSquare (-1 : ZMod m)) : ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  rw [intCast_betaSeq hg hε hγ hn, moebiusFactorK_eq_prod]
  simp only [eq_intCast]
  rw [prod_pow_moebius_eq_div n k n' hn hn' hk (fun d ↦ ((gammaSeq g ε d : ℤ) : ℚ)),
    ← Int.cast_prod, ← Int.cast_prod, hP, hQ, Int.cast_mul, Int.cast_mul,
    mul_div_mul_left _ _ (Int.cast_ne_zero.mpr hc)]
  exact fun hsq ↦ hnsq (ZMod.isSquare_neg_one_of_isSquare_div hPQ hQu hsq)

/-- The squarefree case of `QuadraticIterates.not_isSquare_betaSeq_of_prod_eq_neg_prod`: `n' = n`
and `k = 1`. -/
theorem not_isSquare_betaSeq_of_squarefree_of_prod_eq_neg_prod (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {n : ℕ} (hsf : Squarefree n) {c P Q : ℤ}
    (hc : c ≠ 0) (hP : ∏ t ∈ n.divisors with μ (n / t) = 1, gammaSeq g ε t = c * P)
    (hQ : ∏ t ∈ n.divisors with μ (n / t) = -1, gammaSeq g ε t = c * Q) {m : ℕ}
    (hPQ : (P : ZMod m) = -(Q : ZMod m)) (hQu : IsUnit (Q : ZMod m))
    (hnsq : ¬IsSquare (-1 : ZMod m)) : ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) :=
  not_isSquare_betaSeq_of_prod_eq_neg_prod hg hε hγ (Nat.pos_of_ne_zero hsf.ne_zero)
    (Nat.squarefree_iff_radical_eq_self.mp hsf).symm (one_mul n).symm hc (by simpa using hP)
    (by simpa using hQ) hPQ hQu hnsq

/-- **Lemma 2.1 at a single index.** Let `n ≥ 2`, `n' = rad n` and `k = n / n'`. If the modulus `m`
divides `γ_k + γ_{2k}`, is prime to `γ_k`, and `-1` is not a square mod `m`, then `β_n` is not a
square in `ℚ`: modulo `m`, `γ_{kt} ≡ γ_{2k}` for all `t ≥ 2` and `γ_k ≡ -γ_{2k}`, so the numerator
and the denominator of `β_n` are congruent up to sign, and the denominator is a unit. -/
theorem not_isSquare_betaSeq_of_dvd_add_two_mul (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') {m : ℕ} (hdvd : (m : ℤ) ∣ gammaSeq g ε k + gammaSeq g ε (2 * k))
    (hcop : IsCoprime (m : ℤ) (gammaSeq g ε k)) (hnsq : ¬IsSquare (-1 : ZMod m)) :
    ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have hn'1 : 1 < n' := hn' ▸ Nat.one_lt_radical_iff.mpr (by lia)
  have hkpos : 1 ≤ k := by grind
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hdvd
  have hu := ZMod.isUnit_intCast_of_isCoprime_of_dvd_add hcop hdvd
  simp only [Int.cast_add, intCast_gammaSeq] at hz hu
  refine not_isSquare_betaSeq_of_prod_eq_neg_prod hg hε hγ (by lia) hn' hk one_ne_zero
    (one_mul _).symm (one_mul _).symm (m := m) ?_ ?_ hnsq <;> push_cast [intCast_gammaSeq]
  · exact prod_gammaSeq_mul_eq_neg_prod (hg.map _) hkpos hz (hn' ▸ squarefree_radical) hn'1
  · exact isUnit_prod_gammaSeq_mul (hg.map _) hkpos hz hu fun t ht ↦
      Nat.pos_of_mem_divisors (Finset.mem_of_mem_filter t ht)

/-- The `γ_2`-free part of `γ_t`: `γ_t / γ_2` for even `t`, and `γ_t` itself for odd `t`. -/
private noncomputable def oddPart (g : ℤ[X]) (ε : ℤ) (t : ℕ) : ℤ :=
  if t % 2 = 0 then gammaSeq g ε t / gammaSeq g ε 2 else gammaSeq g ε t

private lemma gammaSeq_eq_mul_oddPart (hg : EvenPoly g) {ε : ℤ} (h0 : g.eval 0 ^ 2 = 1)
    (h1 : gammaSeq g ε 1 = 1) {t : ℕ} (ht : 1 ≤ t) :
    gammaSeq g ε t = (if t % 2 = 0 then gammaSeq g ε 2 else 1) * oddPart g ε t := by
  rw [oddPart]
  split_ifs with he
  · exact (Int.mul_ediv_cancel' (gammaSeq_two_dvd_of_even hg h0 h1 (by lia)
      (Nat.even_iff.mpr he))).symm
  · rw [one_mul]

/-- Modulo `γ_2`, the `γ_2`-free part of `γ_t` is `1` for even `t > 1` and `-1` for odd `t > 1`
(when `g(0) = -1` and `γ_1 = 1`). -/
private lemma intCast_oddPart (hg : EvenPoly g) {ε : ℤ} (h0 : g.eval 0 = -1)
    (h1 : gammaSeq g ε 1 = 1) (h2 : gammaSeq g ε 2 ≠ 0) {m : ℕ} (hm : (m : ℤ) = gammaSeq g ε 2)
    {t : ℕ} (ht : 1 < t) : ((oddPart g ε t : ℤ) : ZMod m) = if t % 2 = 0 then 1 else -1 := by
  have hd := gammaSeq_two_sq_dvd_sub_ite_even hg (by rw [h0]; ring) h1 t ht
  rw [oddPart]
  split_ifs with he
  · rw [ite_eq_left (Nat.even_iff.mpr he)] at hd
    obtain ⟨w, hw⟩ := hd
    rw [show gammaSeq g ε t = gammaSeq g ε 2 * (1 + gammaSeq g ε 2 * w) by linear_combination hw,
      Int.mul_ediv_cancel_left _ h2, ← hm]
    push_cast
    simp
  · rw [ite_eq_right (Nat.even_iff.not.mpr he), h0, sub_neg_eq_add, add_comm] at hd
    exact_mod_cast ZMod.intCast_eq_neg_intCast_of_dvd_add
      (hm ▸ (dvd_pow_self _ two_ne_zero).trans hd)

private lemma prod_gammaSeq_eq_pow_mul_prod_oddPart (hg : EvenPoly g) {ε : ℤ} (h0 : g.eval 0 = -1)
    (h1 : gammaSeq g ε 1 = 1) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.divisors) :
    ∏ t ∈ S, gammaSeq g ε t = gammaSeq g ε 2 ^ #{t ∈ S | t % 2 = 0} * ∏ t ∈ S, oddPart g ε t := by
  rw [Finset.prod_congr rfl fun t ht ↦ gammaSeq_eq_mul_oddPart hg (by rw [h0]; ring) h1
      (Nat.pos_of_mem_divisors (hS ht)),
    Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma isUnit_intCast_oddPart (hg : EvenPoly g) {ε : ℤ} (h0 : g.eval 0 = -1)
    (h1 : gammaSeq g ε 1 = 1) (h2 : gammaSeq g ε 2 ≠ 0) {m : ℕ} (hm : (m : ℤ) = gammaSeq g ε 2)
    {t : ℕ} (ht : 1 ≤ t) : IsUnit ((oddPart g ε t : ℤ) : ZMod m) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [oddPart, h1]
  · rw [intCast_oddPart hg h0 h1 h2 hm ht]
    split_ifs <;> simp

/-- **Lemma 3.3 of [Li 2020], abstractly.** For even `g` with `g(0) = -1` and `γ_1 = 1`, and
squarefree `n ≥ 3`, `β_n` is not a square in `ℚ` as soon as `-1` is not a square modulo `γ_2`:
modulo `γ_2²`, `γ_t ≡ γ_2` for even `t` and `γ_t ≡ -1` for odd `t ≥ 3`, so after cancelling the
common power of `γ_2` (the two halves of the sign partition contain equally many even divisors)
the numerator and denominator of `β_n` are congruent up to sign modulo `γ_2`. -/
theorem not_isSquare_betaSeq_of_squarefree_of_not_isSquare_neg_one (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) (h0 : g.eval 0 = -1)
    (h1 : gammaSeq g ε 1 = 1) {m : ℕ} (hm : (m : ℤ) = gammaSeq g ε 2)
    (hnsq : ¬IsSquare (-1 : ZMod m)) {n : ℕ} (hsf : Squarefree n) (hn : 3 ≤ n) :
    ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have h2 : gammaSeq g ε 2 ≠ 0 := hγ 2 one_le_two
  have hcard (i : ℕ) : #{t ∈ {t ∈ n.divisors | μ (n / t) = 1} | t % 2 = i}
      = #{t ∈ {t ∈ n.divisors | μ (n / t) = -1} | t % 2 = i} := by
    simpa [Finset.filter_filter, and_comm] using
      hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one (Finset.filter_subset _ _)
        (sum_divisors_filter_mod_two_moebius_div hn i)
  have hunion := hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one
  refine not_isSquare_betaSeq_of_squarefree_of_prod_eq_neg_prod hg hε hγ hsf (pow_ne_zero _ h2)
    (prod_gammaSeq_eq_pow_mul_prod_oddPart hg h0 h1 (Finset.filter_subset _ _))
    ((prod_gammaSeq_eq_pow_mul_prod_oddPart hg h0 h1 (Finset.filter_subset _ _)).trans
      (by rw [hcard 0])) (m := m) ?_ ?_ hnsq <;> push_cast
  · refine Finset.prod_eq_neg_prod_of_forall_card_filter_eq (κ := (· % 2))
      (w := fun i ↦ if i = 0 then 1 else -1) (Finset.disjoint_filter.mpr fun _ _ _ _ ↦ by lia)
      (by rw [hunion]; exact Nat.one_mem_divisors.mpr (by lia)) (by simp [oddPart, h1])
      (fun t ht h1t ↦ intCast_oddPart hg h0 h1 h2 hm
        (by have := Nat.pos_of_mem_divisors (hunion ▸ ht); lia)) hcard
  · exact IsUnit.prod_iff.mpr fun t ht ↦ isUnit_intCast_oddPart hg h0 h1 h2 hm
      (Nat.pos_of_mem_divisors (Finset.mem_of_mem_filter t ht))

/-- Lemma 2.1: if for each `n ≥ 1` the modulus `m n` divides `γ_n + γ_{2n}`, is prime to `γ_n`,
and `-1` is not a square mod `m n`, then `β_n` is not a square in `ℚ` for `n ≥ 2`. -/
theorem not_isSquare_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {m : ℕ → ℕ}
    (hdvd : ∀ n ≥ 1, (m n : ℤ) ∣ gammaSeq g ε n + gammaSeq g ε (2 * n))
    (hcop : ∀ n ≥ 1, IsCoprime (m n : ℤ) (gammaSeq g ε n))
    (hnsq : ∀ n ≥ 1, ¬IsSquare (-1 : ZMod (m n))) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  intro n hn
  obtain ⟨k, hk⟩ : radical n ∣ n := radical_dvd_self
  have hkpos : 1 ≤ k := by grind
  exact not_isSquare_betaSeq_of_dvd_add_two_mul hg hε hγ hn rfl (hk.trans (mul_comm _ _))
    (hdvd k hkpos) (hcop k hkpos) (hnsq k hkpos)

/-- Lemma 2.1 with the modulus `γ_k + γ_{k+1}`, `k = n / rad n` ([Li 2021], Corollary 2.4): if
`g(0)` is a unit and the modulus `m` divides `γ_k + γ_{k+1}`, then `β_n` is not a square in `ℚ`
(for `n ≥ 2` and `-1` not a square mod `m`), since `γ_k + γ_{k+1}` divides `γ_k + γ_{2k}` and is
prime to `γ_k`. -/
theorem not_isSquare_betaSeq_of_dvd_add_succ (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) (h0 : IsUnit (g.eval 0)) {n k n' : ℕ} (hn : 2 ≤ n)
    (hn' : n' = radical n) (hk : n = k * n') {m : ℕ}
    (hdvd : (m : ℤ) ∣ gammaSeq g ε k + gammaSeq g ε (k + 1)) (hnsq : ¬IsSquare (-1 : ZMod m)) :
    ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) :=
  have hkpos : 1 ≤ k := by grind
  not_isSquare_betaSeq_of_dvd_add_two_mul hg hε hγ hn hn' hk
    (hdvd.trans (gammaSeq_add_succ_dvd hg ε hkpos))
    ((isCoprime_gammaSeq_add_succ ε hkpos h0).of_isCoprime_of_dvd_left hdvd) hnsq

/-- **Proposition 2.5 of [Li 2021], `k` even.** Let `n ≥ 2`, `n' = rad n` and `k = n / n'` be
even. If the modulus `m` divides `γ_k + γ_{k+2}`, is prime to `γ_2`, and `-1` is not a square mod
`m`, then `β_n` is not a square in `ℚ`: by `2`-periodicity `γ_{2k} ≡ -γ_k mod m`, and `m` is prime
to `γ_k` because a common divisor would divide `γ_{k+2}` and hence `gcd (γ_k) (γ_{k+2}) = γ_2`. -/
theorem not_isSquare_betaSeq_of_even_of_dvd_add_two (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {n k n' : ℕ} (hn : 2 ≤ n) (hn' : n' = radical n)
    (hk : n = k * n') (hke : Even k) {m : ℕ}
    (hdvd : (m : ℤ) ∣ gammaSeq g ε k + gammaSeq g ε (k + 2))
    (hcop : IsCoprime (m : ℤ) (gammaSeq g ε 2)) (hnsq : ¬IsSquare (-1 : ZMod m)) :
    ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have hkpos : 1 ≤ k := by grind
  have hass := gammaSeq_associated_gcd hg hε k (k + 2)
  rw [Nat.gcd_self_add_right, Nat.gcd_eq_right (even_iff_two_dvd.mp hke)] at hass
  refine not_isSquare_betaSeq_of_dvd_add_two_mul hg hε hγ hn hn' hk ?_
    (isCoprime_of_isCoprime_gcd_of_dvd_add (hcop.of_isCoprime_of_dvd_right hass.dvd) hdvd) hnsq
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd ⊢
  push_cast [intCast_gammaSeq] at hdvd ⊢
  rw [gammaSeq_eq_ite_even_of_add_two_eq_zero (hg.map _) hkpos hdvd (2 * k) (by lia),
    ite_eq_left (by grind)]
  ring

/-- For odd `k` (`g` even, `ε = ±1`, `g(0)` a unit), a modulus `m` dividing `γ_k + γ_{k+2}` is
prime to `γ_k`: a common divisor of `m` and `γ_k` divides `γ_{k+2}`, hence
`gcd (γ_k) (γ_{k+2}) = γ_{gcd (k, k+2)} = γ_1`, a unit. -/
theorem isCoprime_gammaSeq_of_odd_of_dvd_add_two (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (h0 : IsUnit (g.eval 0)) {k : ℕ} (hko : Odd k) {m : ℤ}
    (hdvd : m ∣ gammaSeq g ε k + gammaSeq g ε (k + 2)) : IsCoprime m (gammaSeq g ε k) := by
  have hgcd : k.gcd (k + 2) = 1 := by
    rw [Nat.gcd_self_add_right]
    exact Nat.coprime_two_right.mpr hko
  have hu1 : IsUnit (gammaSeq g ε 1) := by
    rw [gammaSeq_one]
    exact (IsUnit.of_pow_eq_one hε two_ne_zero).mul h0
  exact isCoprime_of_isCoprime_gcd_of_dvd_add (isCoprime_one_right.of_isCoprime_of_dvd_right
    (((hgcd ▸ gammaSeq_associated_gcd hg hε k (k + 2)).isUnit_iff.mpr hu1).dvd)) hdvd

/-- If `g` is even with `g(0)² = 1` and `γ_1 = 1`, and `k ≥ 3` is odd, then a common divisor `d`
of `γ_k + γ_{k+2}` and `γ_{k+1}` divides `2`: modulo `d`, `γ_{k+1} = 0` forces `γ_{k+2} = g(0)`,
`γ_k = -g(0)` and `g(1) = g(γ_k) = 0`, so the sequence alternates and `γ_k = g(0)`. -/
theorem dvd_two_of_dvd_add_two_of_dvd_succ (hg : EvenPoly g) {ε : ℤ} (h0 : g.eval 0 ^ 2 = 1)
    (h1 : gammaSeq g ε 1 = 1) {k : ℕ} (hko : Odd k) (hk1 : 1 < k) {d : ℤ}
    (hd : d ∣ gammaSeq g ε k + gammaSeq g ε (k + 2)) (hd' : d ∣ gammaSeq g ε (k + 1)) :
    d ∣ 2 := by
  rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd hd' ⊢
  push_cast [intCast_gammaSeq] at hd hd' ⊢
  set g' := g.map (Int.castRingHom (ZMod d.natAbs))
  have h0' : g'.eval 0 ^ 2 = 1 := by
    rw [eval_zero_map, eq_intCast]
    exact Int.cast_sq_eq_one_of_sq_eq_one h0
  have h1' : gammaSeq g' ε 1 = 1 := by rw [← intCast_gammaSeq, h1, Int.cast_one]
  have hk2 : gammaSeq g' ε (k + 2) = g'.eval 0 := by rw [gammaSeq_succ g' ε (by lia), hd']
  have hk : gammaSeq g' ε k = -g'.eval 0 := by linear_combination hd - hk2
  have hg1 : g'.eval 1 = 0 := by
    rw [← hd', gammaSeq_succ g' ε hko.pos, hk, (hg.map _).eval_neg]
    exact ((hg.map _).eval_congr (by rw [h0', one_pow])).symm
  have := gammaSeq_eq_ite_even_of_eval_one_eq_zero (hg.map _) h0' h1' hg1 k hk1
  rw [ite_eq_right (Nat.not_even_iff_odd.mpr hko), hk] at this
  linear_combination (-g'.eval 0) * this - 2 * h0'

/-- If `g` is even with `g(0)² = 1` and `γ_1 = 1`, and `k ≥ 3` is odd, then the odd part `M` of
`γ_k + γ_{k+2} = 2M` is coprime to `γ_{k+1}`. -/
theorem isCoprime_gammaSeq_succ_of_odd_of_add_two_eq_two_mul (hg : EvenPoly g) {ε : ℤ}
    (h0 : g.eval 0 ^ 2 = 1) (h1 : gammaSeq g ε 1 = 1) {k : ℕ} (hko : Odd k) (hk1 : 1 < k) {M : ℤ}
    (hM : gammaSeq g ε k + gammaSeq g ε (k + 2) = 2 * M) (hMo : Odd M) :
    IsCoprime M (gammaSeq g ε (k + 1)) := by
  refine IsRelPrime.isCoprime fun d hdM hdγ ↦ ?_
  have hd2 := dvd_two_of_dvd_add_two_of_dvd_succ hg h0 h1 hko hk1 (hM ▸ hdM.mul_left 2) hdγ
  rcases (Nat.dvd_prime Nat.prime_two).mp (Int.natAbs_dvd_natAbs.mpr hd2) with h | h
  · exact Int.isUnit_iff_natAbs_eq.mpr h
  · refine absurd (Int.natAbs_dvd.mpr hdM) fun h2 ↦ Int.not_even_iff_odd.mpr hMo ?_
    rw [h] at h2
    exact even_iff_two_dvd.mpr h2

/-- An odd divisor `k > 1` of `n ≠ 0` contributes an odd prime to `rad n`, so `rad n ≥ 3`. -/
private lemma three_le_radical_of_odd_dvd {k n : ℕ} (hn : n ≠ 0) (hk : k ∣ n) (hko : Odd k)
    (hk1 : 1 < k) : 3 ≤ radical n := by
  by_contra! h
  have h2 : radical n = 2 := by
    have := Nat.one_lt_radical_iff.mpr (hk1.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk))
    lia
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by lia)
  have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpk.trans hk, hn⟩
  rw [← Nat.primeFactors_radical, h2, Nat.prime_two.primeFactors, Finset.mem_singleton] at hpn
  exact Nat.not_even_iff_odd.mpr hko (even_iff_two_dvd.mpr (hpn ▸ hpk))

/-- **Proposition 2.5 of [Li 2021], `k` odd.** Let `g(0)` be a unit, `n' = rad n` and
`k = n / n' > 1` odd. If the modulus `m` divides `γ_k + γ_{k+2}`, is prime to `γ_{k+1}`, and `-1` is
not a square mod `m`, then `β_n` is not a square in `ℚ`: by `2`-periodicity, `γ_{kt} ≡ -γ_k` for odd
`t ≥ 3` and `γ_{kt} ≡ γ_{k+1}` for even `t`, and the sign partition of the divisors of `n'` is
balanced on each parity class. -/
theorem not_isSquare_betaSeq_of_odd_of_dvd_add_two (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) (h0 : IsUnit (g.eval 0)) {n k n' : ℕ}
    (hn' : n' = radical n) (hk : n = k * n') (hko : Odd k) (hk1 : 1 < k) {m : ℕ}
    (hdvd : (m : ℤ) ∣ gammaSeq g ε k + gammaSeq g ε (k + 2))
    (hcop : IsCoprime (m : ℤ) (gammaSeq g ε (k + 1))) (hnsq : ¬IsSquare (-1 : ZMod m)) :
    ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have hn : 2 ≤ n := hk ▸ hk1.trans_le (Nat.le_mul_of_pos_right k (hn' ▸ Nat.radical_pos n))
  have hn'3 : 3 ≤ n' := hn' ▸ three_le_radical_of_odd_dvd (by lia) (Dvd.intro _ hk.symm) hko hk1
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hdvd
  have hu := (ZMod.coe_int_isUnit_iff_isCoprime _ m).mpr
    (isCoprime_gammaSeq_of_odd_of_dvd_add_two hg hε h0 hko hdvd)
  have hu1 := (ZMod.coe_int_isUnit_iff_isCoprime _ m).mpr hcop
  simp only [Int.cast_add, intCast_gammaSeq] at hz hu hu1
  refine not_isSquare_betaSeq_of_prod_eq_neg_prod hg hε hγ (by lia) hn' hk one_ne_zero
    (one_mul _).symm (one_mul _).symm (m := m) ?_ ?_ hnsq <;> push_cast [intCast_gammaSeq]
  · exact prod_gammaSeq_mul_eq_neg_prod_of_odd (hg.map _) hko hz (hn' ▸ squarefree_radical) hn'3
  · exact isUnit_prod_gammaSeq_mul_of_odd (hg.map _) hko hz hu hu1 fun t ht ↦
      Nat.pos_of_mem_divisors (Finset.mem_of_mem_filter t ht)

/-- The `ZMod 4` specialization of `QuadraticIterates.gammaSeq_add_succ_eq_three` via
`QuadraticIterates.intCast_gammaSeq`. -/
lemma gammaSeq_add_succ_zmod_four_eq_three (hg : EvenPoly g) (h0 : g.eval 0 = 1)
    (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 2) :
    ∀ n ≥ 1, ((gammaSeq g 1 n + gammaSeq g 1 (n + 1) : ℤ) : ZMod 4) = 3 := by
  intro n hn
  push_cast [intCast_gammaSeq]
  exact gammaSeq_add_succ_eq_three (hg.map _) (by decide) (by rw [eval_zero_map, h0, map_one])
    (by rwa [eval_one_map]) n hn

/-- The `ZMod 8` specialization of `QuadraticIterates.gammaSeq_add_succ_eq_two_mul_eval_one` via
`QuadraticIterates.intCast_gammaSeq`; the mod-4 hypothesis on `g(1)` transfers through the canonical
map `ZMod 8 → ZMod 4`. -/
lemma gammaSeq_add_succ_zmod_eight_eq_six (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (h0 : g.eval 0 ^ 2 = 1) (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 3) :
    ∀ n ≥ 2, ((gammaSeq g ε n + gammaSeq g ε (n + 1) : ℤ) : ZMod 8) = 6 := by
  have hfiber : ∀ x : ZMod 8, ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4) x = 3 →
      x ^ 2 = 1 ∧ 2 * x = 6 := by decide
  obtain ⟨hsq1, h2x⟩ := hfiber ((g.eval 1 : ℤ) : ZMod 8) (by rwa [map_intCast])
  intro n hn
  push_cast [intCast_gammaSeq]
  rwa [gammaSeq_add_succ_eq_two_mul_eval_one (hg.map _) (Int.cast_sq_eq_one_of_sq_eq_one hε)
      (by rw [eval_zero_map, eq_intCast]; exact Int.cast_sq_eq_one_of_sq_eq_one h0)
      (by rwa [eval_one_map]) n hn, eval_one_map]

lemma gammaSeq_one_eq_one_of_pos {ε : ℤ} (hε : ε ^ 2 = 1) (h0 : g.eval 0 ^ 2 = 1)
    (hpos : 0 < gammaSeq g ε 1) : gammaSeq g ε 1 = 1 := by
  rw [gammaSeq_one] at hpos ⊢
  have := sq_eq_one_iff.mp (show (ε * g.eval 0) ^ 2 = 1 by rw [mul_pow, hε, h0, one_mul])
  lia

/-- The reduction of Lemma 2.2 to Lemma 2.1: for positive `γ` and a unit `g(0)`, the positive
integer `γ_n + γ_{n+1}` divides `γ_n + γ_{2n}` and is prime to `γ_n`, so `β_n` is not a square in
`ℚ` for `n ≥ 2` as soon as `-1` is not a square modulo `γ_n + γ_{n+1}` for all `n ≥ 1`. -/
theorem not_isSquare_betaSeq_of_pos_of_not_isSquare_neg_one (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n) (h0 : IsUnit (g.eval 0))
    (hnsq : ∀ n ≥ 1, ¬IsSquare (-1 : ZMod (gammaSeq g ε n + gammaSeq g ε (n + 1)).toNat)) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  intro n hn
  obtain ⟨k, hk⟩ : radical n ∣ n := radical_dvd_self
  have hkpos : 1 ≤ k := by grind
  have hdtn : ((gammaSeq g ε k + gammaSeq g ε (k + 1)).toNat : ℤ)
      = gammaSeq g ε k + gammaSeq g ε (k + 1) :=
    Int.toNat_of_nonneg (add_pos (hpos k hkpos) (hpos (k + 1) (by lia))).le
  exact not_isSquare_betaSeq_of_dvd_add_succ hg hε (fun n hn ↦ (hpos n hn).ne') h0 hn rfl
    (hk.trans (mul_comm _ _)) (hdtn ▸ dvd_rfl) (hnsq k hkpos)

/-- Lemma 2.2 a): if all `γ_n > 0`, `g(0) = 1` and `g(1) ≡ 2 mod 4`, then `β_n` is not a square
in `ℚ` for `n ≥ 2`, since `γ_n + γ_{n+1} ≡ 3 mod 4` for all `n ≥ 1`. -/
theorem not_isSquare_betaSeq_of_pos_of_eval_one_emod_four_eq_two (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n) (h0 : g.eval 0 = 1)
    (h1 : g.eval 1 % 4 = 2) : ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  obtain rfl : ε = 1 := by
    have := gammaSeq_one_eq_one_of_pos hε (by rw [h0, one_pow]) (hpos 1 le_rfl)
    rwa [gammaSeq_one, h0, mul_one] at this
  refine not_isSquare_betaSeq_of_pos_of_not_isSquare_neg_one hg hε hpos (h0 ▸ isUnit_one)
    fun n hn ↦ ZMod.not_isSquare_neg_one_of_emod_four_eq_three ?_
  have hsum := gammaSeq_add_succ_zmod_four_eq_three hg h0
    ((ZMod.intCast_eq_intCast_iff' (g.eval 1) 2 4).mpr (by lia)) n hn
  have := (ZMod.intCast_eq_intCast_iff' _ 3 4).mp (mod_cast hsum)
  have := hpos n hn
  have := hpos (n + 1) (by lia)
  lia

/-- Lemma 2.2 b): if all `γ_n > 0`, `g(0) = ±1` and `g(1) ≡ 3 mod 4`, then `β_n` is not a square
in `ℚ` for `n ≥ 2`, since `4 ∣ γ_1 + γ_2` and `γ_n + γ_{n+1} ≡ 6 mod 8` for all `n ≥ 2`. -/
theorem not_isSquare_betaSeq_of_pos_of_eval_one_emod_four_eq_three (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n) (h0 : g.eval 0 ^ 2 = 1)
    (h1 : g.eval 1 % 4 = 3) : ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  refine not_isSquare_betaSeq_of_pos_of_not_isSquare_neg_one hg hε hpos
    (IsUnit.of_pow_eq_one h0 two_ne_zero) fun n hn ↦ ?_
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by lia
    have hγ1 := gammaSeq_one_eq_one_of_pos hε h0 (hpos 1 le_rfl)
    have hγ2 : gammaSeq g ε 2 = g.eval 1 := by rw [gammaSeq_succ g ε le_rfl, hγ1]
    exact ZMod.not_isSquare_neg_one_of_four_dvd (by lia)
  · have hsum := gammaSeq_add_succ_zmod_eight_eq_six hg hε h0
      ((ZMod.intCast_eq_intCast_iff' (g.eval 1) 3 4).mpr (by lia)) n hn2
    have := (ZMod.intCast_eq_intCast_iff' _ 6 8).mp (mod_cast hsum)
    have := hpos n hn
    have := hpos (n + 1) (by lia)
    exact ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (by lia)

/-- Lemma 2.2: if all `γ_n > 0` and either `g(0) = 1, g(1) ≡ 2 mod 4`, or `g(0) = ±1, g(1) ≡ 3 mod
4`, then `β_n` is not a square in `ℚ` for `n ≥ 2`. -/
theorem not_isSquare_betaSeq_of_pos (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n)
    (hcase : (g.eval 0 = 1 ∧ g.eval 1 % 4 = 2) ∨ (g.eval 0 ^ 2 = 1 ∧ g.eval 1 % 4 = 3)) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) :=
  hcase.elim (fun h ↦ not_isSquare_betaSeq_of_pos_of_eval_one_emod_four_eq_two hg hε hpos h.1 h.2)
    fun h ↦ not_isSquare_betaSeq_of_pos_of_eval_one_emod_four_eq_three hg hε hpos h.1 h.2

end

end QuadraticIterates
