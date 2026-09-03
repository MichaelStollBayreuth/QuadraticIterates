/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Int.Basic
public import QuadraticIterates.Mathlib.RingTheory.MoebiusFactor

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Algebra.GCDMonoid.Basic
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# The iteration sequence of a polynomial and its Möbius factors

For `g ∈ R[X]` and a sign `ε`, the sequence `γ_1 = ε · g(0)`, `γ_{n+1} = g(γ_n)` and its Möbius
factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}`. The results are stated at the generality each one needs:
over a `CommSemiring` for the recursion, over a `CommRing` for the congruences, over a GCD domain
for strong divisibility, over a UFD for the valuation shape and the integrality of `β`, and
finally over `ℤ` for Lemmas 2.1 and 2.2 of the paper.

## Main statements

* `EvenPoly`: `g` is even, i.e. `g ∈ R[X²]`; over a domain of characteristic `≠ 2` this is
  `g(-X) = g` (`evenPoly_iff_comp_neg_X`).
* `gammaSeq`, `betaSeq`: the sequences `γ` and `β`. `map_gammaSeq` says that `γ` commutes with
  ring homomorphisms, which is how every congruence below is computed in `ZMod m`.
* `gammaSeq_associated_gcd`: strong divisibility of `γ` for even `g` and `ε² = 1`.
* `factorization_gammaSeq_shape`: `v_p(γ_n)` is constant on the multiples of some index and `0`
  elsewhere.
* `not_isSquare_betaSeq`, `not_isSquare_betaSeq_of_pos`: Lemmas 2.1 and 2.2 of the paper, `β_n`
  is not a square in `ℚ` for `n ≥ 2` under congruence conditions on `γ` resp. on `g(0)`, `g(1)`.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-! ### Even polynomials -/

section EvenPoly

variable {R : Type*} [CommSemiring R]

/-- `g` is an even polynomial (`g ∈ R[X²]`): `g = Polynomial.expand R 2 h` for some `h`. -/
def EvenPoly (g : R[X]) : Prop := ∃ h : R[X], g = expand R 2 h

namespace EvenPoly

variable {g : R[X]}

/-- An even polynomial takes equal values at points with equal squares. -/
theorem eval_congr (hg : EvenPoly g) {x y : R} (h : x ^ 2 = y ^ 2) : g.eval x = g.eval y := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval, h]

/-- Being an even polynomial is preserved by ring homomorphisms. -/
theorem map {S : Type*} [CommSemiring S] (hg : EvenPoly g) (φ : R →+* S) : EvenPoly (g.map φ) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h.map φ, by rw [map_expand]⟩

end EvenPoly

end EvenPoly

section EvenPoly

variable {R : Type*} [CommRing R] {g : R[X]}

namespace EvenPoly

/-- An even polynomial defines an even evaluation function. -/
theorem eval_neg (hg : EvenPoly g) (y : R) : g.eval (-y) = g.eval y := hg.eval_congr (neg_sq y)

/-- The iterates of the evaluation map of an even polynomial are even functions (`k ≥ 1`). -/
lemma iterate_eval_neg (hg : EvenPoly g) {k : ℕ} (hk : 1 ≤ k) (y : R) :
    (g.eval ·)^[k] (-y) = (g.eval ·)^[k] y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hg.eval_neg]

/-- For even `g`, a divisor of `a² - b²` divides `g(a) - g(b)`. -/
lemma dvd_eval_sub (hg : EvenPoly g) {N a b : R} (h : N ∣ a ^ 2 - b ^ 2) :
    N ∣ g.eval a - g.eval b := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval]
  exact h.trans (sub_dvd_eval_sub (a ^ 2) (b ^ 2) h')

/-- An even polynomial is fixed by `X ↦ -X`. -/
lemma comp_neg_X (hg : EvenPoly g) : g.comp (-X) = g := by
  obtain ⟨h, rfl⟩ := hg
  exact expand_two_comp_neg_X h

end EvenPoly

/-- Over a domain of characteristic `≠ 2` the converse holds too, so the two notions of evenness
this file uses — membership in `R[X²]` and invariance under `X ↦ -X` — agree. -/
lemma evenPoly_iff_comp_neg_X [NoZeroDivisors R] [NeZero (2 : R)] :
    EvenPoly g ↔ g.comp (-X) = g :=
  ⟨EvenPoly.comp_neg_X, fun h ↦ ⟨contract 2 g, eq_expand_two_contract_of_comp_neg_X h⟩⟩

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

/-- The recursion `γ_{n+1} = g(γ_n)`, valid for `n ≥ 1`. -/
lemma gammaSeq_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε (n + 1) = g.eval (gammaSeq g ε n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rfl

/-- `γ_{m+n}` is the `n`-fold iterate of `z ↦ g(z)` applied to `γ_m` (`m ≥ 1`). -/
lemma gammaSeq_add (ε : R) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    gammaSeq g ε (m + n) = (g.eval ·)^[n] (gammaSeq g ε m) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m' + 1 + (n + 1) = m' + n + 1 + 1 by ring, gammaSeq_succ g ε (by lia),
      show m' + n + 1 = m' + 1 + n by ring, ih, Function.iterate_succ_apply']

/-- A ring homomorphism intertwines the `γ`-sequences of `g` and its image:
`φ(γ_n(g, ε)) = γ_n(g.map φ, φ ε)`. -/
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
  | succ k hk ih =>
    rw [gammaSeq_succ g 1 hk, ih]
    simp only [Nat.even_add_one]
    split_ifs <;> assumption

/-- Consecutive terms of the alternating sequence of `gammaSeq_eq_ite_even` sum to `3`. -/
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
    rw [show (2 : ℕ) = 1 + 1 from rfl, gammaSeq_succ g ε le_rfl]
    exact hg.eval_congr (by rw [gammaSeq_one, mul_pow, hε, one_mul, h0, one_pow])
  | succ k hk ih =>
    rw [gammaSeq_succ g ε (by lia), ih]
    exact hg.eval_congr (by rw [h1, one_pow])

/-- Consecutive terms of the eventually constant sequence of `gammaSeq_eq_eval_one` sum to
`2·g(1)` (`n ≥ 2`). -/
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
    rw [show (2 : ℕ) = 1 + 1 from rfl, gammaSeq_succ g ε le_rfl, gammaSeq_succ g 1 le_rfl]
    exact hg.eval_congr (by rw [gammaSeq_one, gammaSeq_one, mul_pow, mul_pow, hε, one_pow])
  | succ k hk ih => rw [gammaSeq_succ g ε (by lia), gammaSeq_succ g 1 (by lia), ih]

/-- For a unit `ε`, `γ_1 = ε · g(0)` is associated to `g(0)`. -/
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
  | succ j ih =>
    rw [← add_assoc, gammaSeq_one_succ, gammaSeq_one_succ]
    exact ih.trans (sub_dvd_eval_sub _ _ g)

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

/-- For even `g`, `γ_n ^ 2` divides `γ_{n+1} - g(0)` (`n ≥ 1`). -/
lemma sq_dvd_gammaSeq_succ_sub (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε n ^ 2 ∣ gammaSeq g ε (n + 1) - g.eval 0 := by
  rw [gammaSeq_succ g ε hn]
  exact hg.dvd_eval_sub (by simp)

/-- Sharpening of `sq_dvd_gammaSeq_succ_sub`: a prime power `p^E` with `E ≥ 1` dividing `γ_n`
already forces `p^{E+1} ∣ γ_{n+1} - g(0)` (`n ≥ 1`). -/
lemma pow_succ_dvd_gammaSeq_succ_sub (hg : EvenPoly g) {ε : R} {n : ℕ} (hn : 1 ≤ n) {p : R}
    {E : ℕ} (hE : 1 ≤ E) (hpE : p ^ E ∣ gammaSeq g ε n) :
    p ^ (E + 1) ∣ gammaSeq g ε (n + 1) - g.eval 0 :=
  calc p ^ (E + 1) ∣ p ^ (2 * E) := pow_dvd_pow p (by lia)
    _ ∣ gammaSeq g ε n ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hpE 2
    _ ∣ gammaSeq g ε (n + 1) - g.eval 0 := sq_dvd_gammaSeq_succ_sub hg ε hn

/-- A divisor `q` of `γ_{m+1} - g(0)` is a period divisor of `γ` from index `2` on, i.e.
`q ∣ γ_{n+m} - γ_n` for all `n ≥ 2` (for even `g` and `ε² = 1`, so that `γ_1² = g(0)²`). -/
lemma gammaSeq_period_of_dvd_succ_sub_eval_zero (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    {m : ℕ} {q : R} (hq : q ∣ gammaSeq g ε (m + 1) - g.eval 0) :
    ∀ n ≥ 2, q ∣ gammaSeq g ε (n + m) - gammaSeq g ε n := by
  refine gammaSeq_period one_le_two ?_
  rw [show 2 + m = m + 1 + 1 by ring, gammaSeq_succ g ε (by lia), show (2 : ℕ) = 1 + 1 from rfl,
    gammaSeq_succ g ε le_rfl]
  refine hg.dvd_eval_sub ?_
  have hsq : gammaSeq g ε (m + 1) ^ 2 - gammaSeq g ε 1 ^ 2
      = (gammaSeq g ε (m + 1) - g.eval 0) * (gammaSeq g ε (m + 1) + g.eval 0) := by
    rw [gammaSeq_one]
    linear_combination (-(g.eval 0) ^ 2) * hε
  rw [hsq]
  exact hq.mul_right _

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

/-- If `γ_k + γ_{2k} = 0`, then a product `∏_{t ∈ S} γ_{kt}` over positive indices `t` collapses
to `γ_{2k} ^ |S|` up to a sign recording whether `1 ∈ S` (over any ring, for even `g`). -/
theorem prod_gammaSeq_mul_eq (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0)
    {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) :
    (∏ t ∈ S, gammaSeq g ε (k * t))
      = gammaSeq g ε (2 * k) ^ S.card * (if 1 ∈ S then -1 else 1) := by
  have hγk_neg : gammaSeq g ε k = -gammaSeq g ε (2 * k) := by linear_combination hzero
  have hf (t : ℕ) (ht : t ∈ S) :
      gammaSeq g ε (k * t) = gammaSeq g ε (2 * k) * (if t = 1 then -1 else 1) := by
    rcases eq_or_ne t 1 with rfl | h
    · rw [mul_one, if_pos rfl, mul_neg, mul_one, hγk_neg]
    · have := hS t ht
      rw [if_neg h, mul_one, mul_comm k t, gammaSeq_mul_eq_two_mul hg hk hzero t (by lia)]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_eq' S 1 (fun _ ↦ (-1 : R))]

/-- If `γ_k + γ_{2k} = 0`, then for disjoint sets `Sp`, `Sm` of positive indices of the same
size, one of which contains `1`, `∏_{t ∈ Sp} γ_{kt} = -∏_{t ∈ Sm} γ_{kt}` (over any ring, for
even `g`): both products are `±γ_{2k}^{#Sp}`, and the index `1` decides the sign. -/
theorem prod_gammaSeq_mul_eq_neg_prod (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) {Sp Sm : Finset ℕ}
    (hdisj : Disjoint Sp Sm) (hcard : Sp.card = Sm.card) (hS : ∀ t ∈ Sp ∪ Sm, 1 ≤ t)
    (h1 : 1 ∈ Sp ∪ Sm) :
    ∏ t ∈ Sp, gammaSeq g ε (k * t) = -∏ t ∈ Sm, gammaSeq g ε (k * t) := by
  rw [prod_gammaSeq_mul_eq hg hk hzero fun t ht ↦ hS t (Finset.mem_union_left _ ht),
    prod_gammaSeq_mul_eq hg hk hzero fun t ht ↦ hS t (Finset.mem_union_right _ ht), hcard]
  rcases Finset.mem_union.mp h1 with h | h
  · simp [h, Finset.disjoint_left.mp hdisj h]
  · simp [h, Finset.disjoint_right.mp hdisj h]

/-- If `γ_k + γ_{2k} = 0` and `γ_{2k}` is a unit, then `∏_{t ∈ S} γ_{kt}` is a unit for every set
`S` of positive indices (over any ring, for even `g`). -/
theorem isUnit_prod_gammaSeq_mul (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) (hu : IsUnit (gammaSeq g ε (2 * k)))
    {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) : IsUnit (∏ t ∈ S, gammaSeq g ε (k * t)) := by
  rw [prod_gammaSeq_mul_eq hg hk hzero hS]
  exact (hu.pow _).mul (by split_ifs <;> simp)

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

/-- If `p ∣ g(0)`, the valuation `v_p(γ_n)` is the constant `v_p(g(0))`. -/
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
  obtain ⟨m, ⟨hm1, hpm⟩, hmin⟩ : ∃ m, (1 ≤ m ∧ p ∣ gammaSeq g ε m) ∧
      ∀ k < m, ¬(1 ≤ k ∧ p ∣ gammaSeq g ε k) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hk ↦ Nat.find_min hex hk⟩
  have hm2 : 2 ≤ m := by
    have : m ≠ 1 := by
      rintro rfl
      exact hpg ((gammaSeq_one_associated_eval_zero
        (IsUnit.of_pow_eq_one hε two_ne_zero)).dvd_iff_dvd_right.mp hpm)
    lia
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

variable (g : ℤ[X])

/-- The image in a ring `S` of the `ε`-sequence over `ℤ` is the `ε`-sequence of the image of `g`:
`(γ_n : S) = γ_n(g.map (· : ℤ → S), ε)`. -/
lemma intCast_gammaSeq (ε : ℤ) (S : Type*) [CommRing S] (i : ℕ) : ((gammaSeq g ε i : ℤ) : S)
    = gammaSeq (g.map (Int.castRingHom S)) (ε : S) i :=
  map_gammaSeq g (Int.castRingHom S) ε i

variable {g}

/-- **Strong divisibility** over `ℤ`, for even `g` and `ε = ±1`:
`gcd (γ_m) (γ_n) = |γ_{gcd m n}|`. -/
theorem gammaSeq_gcd (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1) (m n : ℕ) :
    Int.gcd (gammaSeq g ε m) (gammaSeq g ε n) = (gammaSeq g ε (m.gcd n)).natAbs := by
  have h := Int.associated_iff_natAbs.mp (gammaSeq_associated_gcd hg hε m n)
  rw [← h, ← Int.coe_gcd, Int.natAbs_natCast]

/-- The image of `β_n` in `ℚ` is the Möbius product `∏_{ed = n} γ_d^{μ(e)}` (for even `g`,
`ε = ±1`, and `γ` nowhere zero on positive indices): the specialization of
`algebraMap_moebiusFactorR` to `ℤ ⊆ ℚ`, by strong divisibility. -/
lemma intCast_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ((betaSeq g ε n : ℤ) : ℚ) = moebiusFactorK (gammaSeq g ε) n :=
  algebraMap_moebiusFactorR hγ (gammaSeq_associated_gcd hg hε) n hn

/-- Lemma 2.1: if for each `n ≥ 1` the modulus `m n` divides `γ_n + γ_{2n}`, is prime to `γ_n`,
and `-1` is not a square mod `m n`, then `β_n` is not a square in `ℚ` for `n ≥ 2`. -/
theorem not_isSquare_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0) {m : ℕ → ℕ}
    (hdvd : ∀ n ≥ 1, (m n : ℤ) ∣ gammaSeq g ε n + gammaSeq g ε (2 * n))
    (hcop : ∀ n ≥ 1, IsCoprime (m n : ℤ) (gammaSeq g ε n))
    (hnsq : ∀ n ≥ 1, ¬IsSquare (-1 : ZMod (m n))) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  intro n hn2
  set n' := UniqueFactorizationMonoid.radical n
  obtain ⟨k, hk⟩ : n' ∣ n := UniqueFactorizationMonoid.radical_dvd_self
  rw [mul_comm] at hk
  have hn'1 : 1 < n' := Nat.one_lt_radical_iff.mpr (by lia)
  have hkpos : 1 ≤ k := by grind
  obtain ⟨Sp, Sm, hdisj, hunion, hcard, hSp, hSm⟩ :=
    moebius_sign_partition n' hn'1 UniqueFactorizationMonoid.squarefree_radical
  have hS (t : ℕ) (ht : t ∈ Sp ∪ Sm) : 1 ≤ t := Nat.pos_of_mem_divisors (hunion ▸ ht)
  have h1 : 1 ∈ Sp ∪ Sm := hunion ▸ Nat.one_mem_divisors.mpr (by lia)
  rw [intCast_betaSeq hg hε hγ (by lia), moebiusFactorK_eq_prod]
  simp only [eq_intCast]
  rw [prod_pow_moebius_eq_div n k n' (by lia) rfl hk (fun d ↦ ((gammaSeq g ε d : ℤ) : ℚ)) hdisj
    hunion hSp hSm, ← Int.cast_prod, ← Int.cast_prod]
  -- the two products are `P ≡ -Q` with `Q` a unit modulo `m k`, computed in `ZMod (m k)`
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (m k)).mpr (hdvd k hkpos)
  have hu := ZMod.isUnit_intCast_of_isCoprime_of_dvd_add (hcop k hkpos) (hdvd k hkpos)
  simp only [Int.cast_add, intCast_gammaSeq] at hz hu
  refine fun hsq ↦ hnsq k hkpos (ZMod.isSquare_neg_one_of_isSquare_div ?_ ?_ hsq) <;>
    simp only [Int.cast_prod, intCast_gammaSeq]
  · exact prod_gammaSeq_mul_eq_neg_prod (hg.map _) hkpos hz hdisj hcard hS h1
  · exact isUnit_prod_gammaSeq_mul (hg.map _) hkpos hz hu fun t ht ↦
      hS t (Finset.mem_union_right _ ht)

/-- The `ZMod 4` specialization of `gammaSeq_add_succ_eq_three` via `intCast_gammaSeq`. -/
lemma gammaSeq_add_succ_zmod_four_eq_three (hg : EvenPoly g) (h0 : g.eval 0 = 1)
    (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 2) :
    ∀ n ≥ 1, ((gammaSeq g 1 n + gammaSeq g 1 (n + 1) : ℤ) : ZMod 4) = 3 := by
  intro n hn
  push_cast
  simp only [intCast_gammaSeq, Int.cast_one]
  exact gammaSeq_add_succ_eq_three (hg.map _) (by decide) (by rw [eval_zero_map, h0, map_one])
    (by rwa [eval_one_map]) n hn

/-- The `ZMod 8` specialization of `gammaSeq_add_succ_eq_two_mul_eval_one` via
`intCast_gammaSeq`; the mod-4 hypothesis on `g(1)` transfers through the canonical map
`ZMod 8 → ZMod 4`. -/
lemma gammaSeq_add_succ_zmod_eight_eq_six (hg : EvenPoly g) {ε : ℤ} (hε : ε ^ 2 = 1)
    (h0 : g.eval 0 ^ 2 = 1) (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 3) :
    ∀ n ≥ 2, ((gammaSeq g ε n + gammaSeq g ε (n + 1) : ℤ) : ZMod 8) = 6 := by
  have hfiber : ∀ x : ZMod 8, ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4) x = 3 →
      x ^ 2 = 1 ∧ 2 * x = 6 := by decide
  obtain ⟨hsq1, h2x⟩ := hfiber ((g.eval 1 : ℤ) : ZMod 8) (by rw [map_intCast]; exact h1)
  intro n hn
  push_cast
  simp only [intCast_gammaSeq]
  rw [gammaSeq_add_succ_eq_two_mul_eval_one (hg.map _) (by rw [← Int.cast_pow, hε, Int.cast_one])
      (by rw [eval_zero_map, eq_intCast, ← Int.cast_pow, h0, Int.cast_one])
      (by rwa [eval_one_map]) n hn, eval_one_map]
  exact h2x

/-- Over `ℤ`, if `ε² = g(0)² = 1` and `γ_1 > 0`, then `γ_1 = 1`. -/
lemma gammaSeq_one_eq_one_of_pos {ε : ℤ} (hε : ε ^ 2 = 1) (h0 : g.eval 0 ^ 2 = 1)
    (hpos : 0 < gammaSeq g ε 1) : gammaSeq g ε 1 = 1 := by
  rw [gammaSeq_one] at hpos ⊢
  have := sq_eq_one_iff.mp (show (ε * g.eval 0) ^ 2 = 1 by rw [mul_pow, hε, h0, one_mul])
  lia

/-- The reduction of Lemma 2.2 to Lemma 2.1: for positive `γ` and a unit `g(0)`, the positive
integer `m := γ_n + γ_{n+1}` divides `γ_n + γ_{2n}` and is prime to `γ_n`, so `β_n` is not a
square in `ℚ` for `n ≥ 2` as soon as `-1` is not a square modulo `γ_n + γ_{n+1}` for all
`n ≥ 1`. -/
theorem not_isSquare_betaSeq_of_pos_of_not_isSquare_neg_one (hg : EvenPoly g) {ε : ℤ}
    (hε : ε ^ 2 = 1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n) (h0 : IsUnit (g.eval 0))
    (hnsq : ∀ n ≥ 1, ¬IsSquare (-1 : ZMod (gammaSeq g ε n + gammaSeq g ε (n + 1)).toNat)) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have hdtn (n : ℕ) (hn : 1 ≤ n) : ((gammaSeq g ε n + gammaSeq g ε (n + 1)).toNat : ℤ)
      = gammaSeq g ε n + gammaSeq g ε (n + 1) :=
    Int.toNat_of_nonneg (add_pos (hpos n hn) (hpos (n + 1) (by lia))).le
  exact not_isSquare_betaSeq hg hε (fun n hn ↦ (hpos n hn).ne')
    (fun n hn ↦ by rw [hdtn n hn]; exact gammaSeq_add_succ_dvd hg ε hn)
    (fun n hn ↦ by rw [hdtn n hn]; exact isCoprime_gammaSeq_add_succ ε hn h0) hnsq

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
  have h1' : ((g.eval 1 : ℤ) : ZMod 4) = 2 :=
    (ZMod.intCast_eq_intCast_iff' (g.eval 1) 2 4).mpr (by lia)
  have hsum := gammaSeq_add_succ_zmod_four_eq_three hg h0 h1' n hn
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
  · have h1' : ((g.eval 1 : ℤ) : ZMod 4) = 3 :=
      (ZMod.intCast_eq_intCast_iff' (g.eval 1) 3 4).mpr (by lia)
    have hsum := gammaSeq_add_succ_zmod_eight_eq_six hg hε h0 h1' n hn2
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
