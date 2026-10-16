/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.Iterates
public import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Mathlib.RingTheory.Multiplicity
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Patterns.Primes
import QuadraticIterates.Patterns.Sign
import QuadraticIterates.Sequence.Signs
import QuadraticIterates.Sequence.SquareClasses
import QuadraticIterates.Sequence.WSeq

/-!
# Three lists of criteria

For `a = r/s` with `r, s` coprime and `s > 0`, three lists of elementary conditions on `r` and `s`,
each condition giving one of the patterns `φ₀ = (-1, -1, …)`, `φ₁ = (-1, 1, 1, …)` and
`τ = (1, -1, -1, …)` along `(c_n)`; by
`QuadraticIterates.hasCharPattern_neg_mulSingle_of_neg_of_mulSingle` and its siblings, any two of
these patterns give the third. The conditions are stated with
Mathlib's notions only (Jacobi symbols, `p`-parts written as `r = p^k m` with `p ∤ m`), so that
they can be restated in a comparator challenge.

## Main definitions

* `QuadraticIterates.NegAllCriterion r s`: (Z1)–(Z4), giving `φ₀`.
* `QuadraticIterates.NegFirstCriterion r s`: (O1)–(O5), giving `φ₁`.
* `QuadraticIterates.NegTailCriterion r s`: (T1)–(T4), giving `τ`.

## Main statements

* `QuadraticIterates.hasCharPattern_neg_one_of_negAllCriterion`,
  `QuadraticIterates.hasCharPattern_mulSingle_one_of_negFirstCriterion`,
  `QuadraticIterates.hasCharPattern_neg_mulSingle_one_of_negTailCriterion`.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

variable {r s : ℤ}

/-- Criteria (Z1)–(Z4) for `φ₀` (the pattern `(-1, -1, -1, …)`), for `a = r/s`. -/
inductive NegAllCriterion (r s : ℤ) : Prop
  /-- (Z1) `r ≠ ±□`. -/
  | not_isSquare (h : ¬IsSquare r) (h' : ¬IsSquare (-r))
  /-- (Z2) A prime `p ≡ ±3 (mod 8)` divides `r + 2s`. -/
  | dvd_add_two_mul (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
      (hdvd : (p : ℤ) ∣ r + 2 * s)
  /-- (Z3) An odd prime `p` divides `r² + s²`, and `(-rs / p) = ((r - s)s / p) = -1`. -/
  | dvd_sq_add_sq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2)
      (h₁ : jacobiSym (-(r * s)) p = -1) (h₂ : jacobiSym ((r - s) * s) p = -1)
  /-- (Z4) A prime `p ≡ 1 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(m s / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 1) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- (Z4) `r = 2^k m` with `k ≥ 3` and `m s ≡ ±3 (mod 8)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 3 ≤ k) (hr : r = 2 ^ k * m)
      (h : m * s % 8 = 3 ∨ m * s % 8 = 5)

/-- Criteria (O1)–(O5) for `φ₁` (the pattern `(-1, 1, 1, …)`), for `a = r/s` with `s > 0`. -/
inductive NegFirstCriterion (r s : ℤ) : Prop
  /-- (O1) `a > 0`. -/
  | pos (h : 0 < r)
  /-- (O2) `a ≡ 1 mod 4`: `s` is odd and `r ≡ s (mod 4)`. -/
  | modEq_four (hs : Odd s) (h : r ≡ s [ZMOD 4])
  /-- (O3) An odd prime `p` divides `s = p^k m` (`p ∤ m`) with `k` odd or `(-rm / p) = -1`. -/
  | dvd_right (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) (hs : s = p ^ k * m)
      (hm : ¬(p : ℤ) ∣ m) (h : Odd k ∨ jacobiSym (-(r * m)) p = -1)
  /-- (O4) `s = 2^k m` with `m` odd, and `k` is odd, or `k = 2` and `rm ≡ 1 (mod 4)`, or `k ≥ 4`
  is even and `rm ≢ -1 (mod 8)`. -/
  | dvd_right_two (k : ℕ) (m : ℤ) (hs : s = 2 ^ k * m) (hm : Odd m)
      (h : Odd k ∨ (k = 2 ∧ r * m % 4 = 1) ∨ (Even k ∧ 4 ≤ k ∧ r * m % 8 ≠ 7))
  /-- (O5) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = 1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = 1)
  /-- (O5) `r = 2^k m` with `k ≥ 2` and `ms ≡ 1 (mod 4)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 1)

/-- Criteria (T1)–(T4) for `τ` (the pattern `(1, -1, -1, …)`), for `a = r/s` with `s > 0`. -/
inductive NegTailCriterion (r s : ℤ) : Prop
  /-- (T1) `-1 < a < 0`. -/
  | neg_one_lt (h₁ : -s < r) (h₀ : r < 0)
  /-- (T2) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- (T2) `r = 2^k m` with `k ≥ 2` and `ms ≡ 3 (mod 4)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 3)
  /-- (T3) A prime `p ≡ 3 (mod 4)` divides `r + s = p^k m` (`p ∤ m`) with `(sm / p) = 1`. -/
  | dvd_add (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hrs : r + s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (s * m) p = 1)
  /-- (T3) `r + s = 2^k m` with `k ≥ 2` and `sm ≡ 1 (mod 4)`. -/
  | dvd_add_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hrs : r + s = 2 ^ k * m) (h : s * m % 4 = 1)
  /-- (T3) `r + s ≠ ±□`, and `r + s` is divisible by `4` or by a prime `p ≡ 3 (mod 4)`. -/
  | not_isSquare_add (h : ¬IsSquare (r + s)) (h' : ¬IsSquare (-(r + s)))
      (hdvd : 4 ∣ r + s ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ r + s)
  /-- (T4) `a < -1`, `c_3 < 0 < c_4` (that is, `r w_3 < 0 < r w_4`), and `r + s ≠ ±□`. -/
  | window (hr : r < -s) (h₃ : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0)
      (h₄ : 0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) (h : ¬IsSquare (r + s))
      (h' : ¬IsSquare (-(r + s)))

/-! ### Auxiliary facts -/

private lemma hasCharPattern_mulSingle_one_of_apply {M : Type*} [CommMonoid M] {v : ℕ → M}
    (χ : MulChar M ℤ) (h₁ : χ (v 1) = -1) (h : ∀ n ≥ 2, χ (v n) = 1) :
    HasCharPattern v 1 (Pi.mulSingle 1 (-1)) :=
  ⟨χ, fun n hn ↦ by
    rcases hn.eq_or_lt with rfl | hn
    · simpa using h₁
    · rw [h n hn, Pi.mulSingle_eq_of_ne (by lia)]⟩

private lemma hasCharPattern_neg_mulSingle_one_of_apply {M : Type*} [CommMonoid M] {v : ℕ → M}
    (χ : MulChar M ℤ) (h₁ : χ (v 1) = 1) (h : ∀ n ≥ 2, χ (v n) = -1) :
    HasCharPattern v 1 (-Pi.mulSingle 1 (-1)) :=
  ⟨χ, fun n hn ↦ by
    rcases hn.eq_or_lt with rfl | hn
    · simpa using h₁
    · rw [h n hn, Pi.neg_apply, Pi.mulSingle_eq_of_ne (by lia)]⟩

private lemma exists_prime_odd_factorization (h : ¬IsSquare r) (h' : ¬IsSquare (-r)) :
    ∃ p, p.Prime ∧ Odd (r.natAbs.factorization p) := by
  rw [Int.isSquare_iff_nonneg_even_factorization] at h h'
  push Not at h h'
  rcases le_total 0 r with hr | hr
  · obtain ⟨p, hp, hodd⟩ := h hr
    exact ⟨p, hp, Nat.not_even_iff_odd.mp hodd⟩
  · obtain ⟨p, hp, hodd⟩ := h' (neg_nonneg.mpr hr)
    exact ⟨p, hp, Nat.not_even_iff_odd.mp (by simpa using hodd)⟩

private lemma exists_prime_dvd_valChar_eq_neg_one {x : ℤ} (h : ¬IsSquare x) (h' : ¬IsSquare (-x)) :
    ∃ q : ℕ, ∃ _ : Fact q.Prime, (q : ℤ) ∣ x ∧ valChar q (x : ℚ) = -1 := by
  obtain ⟨q, hq, hodd⟩ := exists_prime_odd_factorization h h'
  have := Fact.mk hq
  have hx0 : x ≠ 0 := by rintro rfl; exact h ⟨0, by simp⟩
  refine ⟨q, this, Int.natCast_dvd.mpr (Nat.dvd_of_factorization_pos
    (Nat.pos_of_ne_zero hodd.pos.ne').ne'), ?_⟩
  rw [valChar_intCast hx0, padicValInt, ← Nat.factorization_def _ hq, hodd.neg_one_pow]

private lemma odd_of_mul_emod_two {x y : ℤ} (h : x * y % 2 = 1) : Odd x ∧ Odd y :=
  Int.odd_mul.mp (Int.odd_iff.mpr h)

private lemma χ₄_intCast_of_emod_four_eq_one {x : ℤ} (h : x % 4 = 1) : ZMod.χ₄ (x : ZMod 4) = 1 :=
  ZMod.χ₄_int_one_mod_four h

private lemma χ₄_intCast_of_emod_four_eq_three {x : ℤ} (h : x % 4 = 3) :
    ZMod.χ₄ (x : ZMod 4) = -1 :=
  ZMod.χ₄_int_three_mod_four h

/-- For `N = 2^j ∣ s` (`j ≥ 1`) and odd `r`, every `χ_ψ`, `ψ` modulo `N`, is `1` at
`c_2 ∼ r(r + s)`, as `r + s ≡ r (mod N)`. -/
private lemma unitPartChar_two_cSeq_two (hs : s ≠ 0) {N j : ℕ} (hN : N = 2 ^ j) (hj : j ≠ 0)
    (hNs : (N : ℤ) ∣ s) (hr : Odd r) (ψ : MulChar (ZMod N) ℤ) :
    unitPartChar 2 ψ (cSeq ((r : ℚ) / s) 2) = 1 := by
  have hs2 : Even s := even_iff_two_dvd.mpr ((dvd_pow_self 2 hj).trans (mod_cast hN ▸ hNs))
  have h0 : (s : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNs
  rw [mulChar_cSeq_of_two_le _ hs le_rfl, wSeq_two, ← Int.cast_mul, unitPartChar_intCast hN
    (by simpa [← even_iff_two_dvd] using hr.mul (hr.add_even hs2)), Int.cast_mul, Int.cast_add, h0,
    add_zero, ← sq, ψ.apply_sq_of_isUnit (ZMod.isUnit_intCast_of_not_dvd hN
      (by simpa [← even_iff_two_dvd] using hr))]

private lemma quadraticChar_intCast {p : ℕ} [Fact p.Prime] (a : ℤ) :
    quadraticChar (ZMod p) a = jacobiSym a p :=
  jacobiSym.legendreSym.to_jacobiSym p a

private lemma quadraticChar_neg_one_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadraticChar (ZMod p) (-1) = ZMod.χ₄ p := by
  have h := legendreSym.at_neg_one hp2
  rwa [legendreSym, Int.cast_neg, Int.cast_one] at h

private lemma quadraticChar_two {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    quadraticChar (ZMod p) 2 = -1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp8
  have h := legendreSym.at_two hp2
  rw [legendreSym, Int.cast_ofNat] at h
  rw [h, ZMod.χ₈_nat_eq_if_mod_eight]
  split_ifs <;> lia

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- At `r = p^k m` (`p ∤ m`) and a power `N` of `p` dividing `r`, `χ_ψ(c_n) = ψ(ms)` for
`n ≥ 2`. -/
private lemma unitPartChar_cSeq_of_eq_pow_mul (hrs : IsCoprime r s) (hs : s ≠ 0) {N j k : ℕ}
    (hN : N = p ^ j) (hj : j ≠ 0) (hNr : (N : ℤ) ∣ r) {m : ℤ} (hr : r = p ^ k * m)
    (hm : ¬(p : ℤ) ∣ m) (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 2 ≤ n) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = ψ (m * s) := by
  rw [unitPartChar_cSeq_of_dvd_left hrs hs hN hj hNr ψ hn, hr,
    unitPartChar_intCast_pow_mul hN ψ k hm, ← map_mul, mul_comm]

/-- At `r = p^k m` (`k ≥ 1`, `p ∤ m`), `χ_ψ(c_1) = ψ(-1) ψ(ms)`. -/
private lemma unitPartChar_cSeq_one_of_eq_pow_mul (hrs : IsCoprime r s) (hs : s ≠ 0) {N j k : ℕ}
    (hN : N = p ^ j) (hk : k ≠ 0) {m : ℤ} (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (ψ : MulChar (ZMod N) ℤ) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) 1) = ψ (-1) * ψ (m * s) := by
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit
    (hrs.isUnit_of_dvd' (hr ▸ (dvd_pow_self _ hk).mul_right m) h)
  rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hps, hr,
    unitPartChar_intCast_pow_mul hN ψ k hm, mul_assoc, ← map_mul]


/-! ### Criteria for `φ₀` -/

/-- (Z2) If a prime `p ≡ ±3 (mod 8)` divides `r + 2s`, then `χ_p` is a `φ₀`: it is `(2 / p) = -1`
at every `c_n`. -/
theorem hasCharPattern_neg_one_of_dvd_add_two_mul (hrs : IsCoprime r s)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hdvd : (p : ℤ) ∣ r + 2 * s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp8
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_dvd_add_two_mul hrs (pow_one p).symm one_ne_zero hp2
    (by simpa using hdvd) _ hn, quadraticChar_two hp8]
  rfl

/-- (Z3) If an odd prime `p` divides `r² + s²` and `(-rs / p) = ((r - s)s / p) = -1`, then
`χ_p` is a `φ₀`: modulo `p` the sequence alternates between `-a` and `a - 1`, `a² = -1`. -/
theorem hasCharPattern_neg_one_of_dvd_sq_add_sq (hrs : IsCoprime r s) (hp2 : p ≠ 2)
    (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2) (h₁ : jacobiSym (-(r * s)) p = -1)
    (h₂ : jacobiSym ((r - s) * s) p = -1) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [unitPartChar_cSeq_two_mul_of_dvd_sq_add_sq hrs hN one_ne_zero hp2 (by simpa using hdvd) _
      (by lia), show ((r : ZMod p) - s) * s = (((r - s) * s : ℤ) : ZMod p) by push_cast; ring,
      quadraticChar_intCast, h₂]
    rfl
  · rw [unitPartChar_cSeq_two_mul_add_one_of_dvd_sq_add_sq hrs hN one_ne_zero
      (by simpa using hdvd), show -((r : ZMod p) * s) = ((-(r * s) : ℤ) : ZMod p) by
        push_cast; ring, quadraticChar_intCast, h₁]
    rfl

/-- (Z4) If a prime `p ≡ 1 (mod 4)` divides `r = p^k m` (`p ∤ m`) and `(ms / p) = -1`, then `χ_p`
is a `φ₀`: `χ_p(c_n) = (-1 / p)^{[n = 1]} (ms / p)` with `(-1 / p) = 1`. -/
theorem hasCharPattern_neg_one_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ} {m : ℤ}
    (hp4 : p % 4 = 1) (hk : 0 < k) (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (m * s) p = -1) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  have hpr : (p : ℤ) ∣ r := hr ▸ (dvd_pow_self _ hk.ne').mul_right m
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit
    (hrs.isUnit_of_dvd' hpr h)
  set ψ := quadraticChar (ZMod p)
  have hχr : unitPartChar p ψ r = ψ m := by
    rw [hr]
    exact_mod_cast unitPartChar_intCast_pow_mul hN ψ k hm
  have hms : ψ s * ψ m = -1 := by rw [← map_mul, mul_comm, ← Int.cast_mul, quadraticChar_intCast, h]
  have h₁ : ψ (-1) = 1 := by rw [quadraticChar_neg_one_eq (by lia), ZMod.χ₄_nat_one_mod_four hp4]
  refine ⟨unitPartChar p ψ, fun n hn ↦ ?_⟩
  rcases hn.eq_or_lt with rfl | hn
  · rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hps, hχr,
      h₁, one_mul, mul_comm, hms]
    rfl
  · rw [unitPartChar_cSeq_of_dvd_left hrs hs hN one_ne_zero (by simpa using hpr) ψ hn, hχr, hms]
    rfl


/-! ### Criteria for `φ₁` -/

/-- (O5) If a prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) and `(ms / p) = 1`, then `χ_p`
is a `φ₁`: its pattern is `((-1 / p), 1, 1, …)`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ}
    {m : ℤ} (hp4 : p % 4 = 3) (hk : 0 < k) (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (m * s) p = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  have hms : quadraticChar (ZMod p) (m * s) = 1 := by
    rw [← Int.cast_mul, ← h]
    exact jacobiSym.legendreSym.to_jacobiSym p _
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar p (quadraticChar (ZMod p))) ?_
    fun n hn ↦ ?_
  · rw [unitPartChar_cSeq_one_of_eq_pow_mul hrs hs hN hk.ne' hr hm,
      ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4, hms, mul_one]
  · rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs hN one_ne_zero
      (by simpa [hr] using (dvd_pow_self (p : ℤ) hk.ne').mul_right m) hr hm _ hn, hms]

/-- (O5) If `r = 2^k m` with `k ≥ 2` and `ms ≡ 1 (mod 4)`, then `χ₄` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_left_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hN : 4 = 2 ^ 2 := rfl
  have hm : ¬((2 : ℕ) : ℤ) ∣ m := by rintro ⟨t, rfl⟩; lia
  have hms : ZMod.χ₄ ((m : ZMod 4) * s) = 1 := by
    rw [← Int.cast_mul, χ₄_intCast_of_emod_four_eq_one h]
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar 2 ZMod.χ₄) ?_ fun n hn ↦ ?_
  · rw [unitPartChar_cSeq_one_of_eq_pow_mul hrs hs hN (by lia : k ≠ 0) (mod_cast hr) hm, hms,
      show ZMod.χ₄ (-1) = -1 by decide, mul_one]
  · rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs hN two_ne_zero
      (hr ▸ (pow_dvd_pow 2 hk).mul_right m) (mod_cast hr) hm _ hn, hms]

/-- (O3), (O4) If `s = p^k m` with `k` odd (`p ∤ m`), then `val_p` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_of_odd (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : Odd k) (hsm : s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hps : (p : ℤ) ∣ s := hsm ▸ (dvd_pow_self _ (Nat.pos_of_ne_zero hk.pos.ne').ne').mul_right m
  have hpr : ¬(p : ℤ) ∣ r := fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit
    (hrs.isUnit_of_dvd' h hps)
  refine hasCharPattern_mulSingle_one_of_apply (valChar p) ?_
    fun n hn ↦ valChar_cSeq_of_dvd_right hrs hs hps hn
  rw [mulChar_cSeq_one_eq_mul _ hs, valChar_neg_one, valChar_intCast_of_not_dvd hpr, hsm,
    valChar_intCast_pow_mul k hm, hk.neg_one_pow, one_mul, one_mul]

/-- (O3) If an odd prime `p` divides `s = p^k m` (`p ∤ m`) and `(-rm / p) = -1`, then `χ_p` is
a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ}
    {m : ℤ} (hk : 0 < k) (hsm : s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (-(r * m)) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  have hps : (p : ℤ) ∣ s := hsm ▸ (dvd_pow_self _ hk.ne').mul_right m
  have hpr : ¬(p : ℤ) ∣ r := fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit
    (hrs.isUnit_of_dvd' h hps)
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar p (quadraticChar (ZMod p))) ?_
    fun n hn ↦ unitPartChar_cSeq_of_dvd_right hrs hs hN one_ne_zero (by simpa using hps) _ hn
  rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hpr, hsm,
    unitPartChar_intCast_pow_mul hN _ k hm, ← map_mul, ← map_mul,
    show (-1 : ZMod p) * r * m = ((-(r * m) : ℤ) : ZMod p) by push_cast; ring, ← h]
  exact jacobiSym.legendreSym.to_jacobiSym p _

/-- (O4) If `s = 2^k m` with `k ≥ 2` and `rm ≡ 1 (mod 4)`, then `χ₄` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hsm : s = 2 ^ k * m) (h : r * m % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hN : 4 = 2 ^ 2 := rfl
  obtain ⟨hr, hm⟩ := odd_of_mul_emod_two (by lia : r * m % 2 = 1)
  have hNs : ((4 : ℕ) : ℤ) ∣ s := hsm ▸ (pow_dvd_pow 2 hk).mul_right m
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar 2 ZMod.χ₄) ?_ fun n hn ↦ ?_
  · rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN
      (by simpa [← even_iff_two_dvd] using hr), hsm, show (2 : ℤ) ^ k = ((2 : ℕ) : ℤ) ^ k by simp,
      unitPartChar_intCast_pow_mul hN _ k (by simpa [← even_iff_two_dvd] using hm), mul_assoc,
      ← map_mul, ← Int.cast_mul, χ₄_intCast_of_emod_four_eq_one h]
    decide
  · rcases hn.eq_or_lt with rfl | hn
    · exact unitPartChar_two_cSeq_two hs hN two_ne_zero hNs hr _
    · exact unitPartChar_two_cSeq_of_even hrs hs
        (hsm ▸ (even_two.pow_of_ne_zero (by lia)).mul_right m) hN (by norm_num) _ hn

/-- (O4) If `s = 2^k m` with `k ≥ 3` and `rm ≡ ±3 (mod 8)`, then `χ₈` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_eight (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 3 ≤ k) (hsm : s = 2 ^ k * m) (h : r * m % 8 = 3 ∨ r * m % 8 = 5) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hN : 8 = 2 ^ 3 := rfl
  obtain ⟨hr, hm⟩ := odd_of_mul_emod_two (by lia : r * m % 2 = 1)
  have hNs : ((8 : ℕ) : ℤ) ∣ s := hsm ▸ (pow_dvd_pow 2 hk).mul_right m
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar 2 ZMod.χ₈) ?_ fun n hn ↦ ?_
  · rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN
      (by simpa [← even_iff_two_dvd] using hr), hsm, show (2 : ℤ) ^ k = ((2 : ℕ) : ℤ) ^ k by simp,
      unitPartChar_intCast_pow_mul hN _ k (by simpa [← even_iff_two_dvd] using hm), mul_assoc,
      ← map_mul, ← Int.cast_mul, ZMod.χ₈_int_eq_if_mod_eight, show ZMod.χ₈ (-1) = 1 by decide]
    split_ifs <;> lia
  · rcases hn.eq_or_lt with rfl | hn
    · exact unitPartChar_two_cSeq_two hs hN (by norm_num) hNs hr _
    · exact unitPartChar_two_cSeq_of_even hrs hs
        (hsm ▸ (even_two.pow_of_ne_zero (by lia)).mul_right m) hN le_rfl _ hn

/-- (O4): the three cases `k` odd (`val₂`), `rm ≡ 1 (mod 4)` (`χ₄`), `rm ≡ 3 (mod 8)` (`χ₈`). -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_two (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hsm : s = 2 ^ k * m) (hm : Odd m)
    (h : Odd k ∨ (k = 2 ∧ r * m % 4 = 1) ∨ (Even k ∧ 4 ≤ k ∧ r * m % 8 ≠ 7)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  rcases h with h | ⟨rfl, h⟩ | ⟨-, hk, h⟩
  · exact hasCharPattern_mulSingle_one_of_dvd_right_of_odd (p := 2) hrs hs h (mod_cast hsm)
      (by simpa [← even_iff_two_dvd] using hm)
  · exact hasCharPattern_mulSingle_one_of_dvd_right_four hrs hs le_rfl hsm h
  · have hr : Odd r := Int.not_even_iff_odd.mp fun he ↦
      (Nat.prime_iff_prime_int.mp Nat.prime_two).not_isUnit (hrs.isUnit_of_dvd'
        (even_iff_two_dvd.mp he) (hsm ▸ (dvd_pow_self 2 (by lia)).mul_right m))
    have h2 := Int.odd_iff.mp (hr.mul hm)
    rcases (by lia : r * m % 8 = 3 ∨ r * m % 4 = 1) with h' | h'
    · exact hasCharPattern_mulSingle_one_of_dvd_right_eight hrs hs (by lia) hsm (.inl h')
    · exact hasCharPattern_mulSingle_one_of_dvd_right_four hrs hs (by lia) hsm h'

/-- **Criteria for `φ₁`** (Proposition O): each of (O1)–(O5) gives a character that is `-1` at
`c_1` and `1` at all later terms. -/
theorem hasCharPattern_mulSingle_one_of_negFirstCriterion (hrs : IsCoprime r s) (hs : 0 < s)
    (h : NegFirstCriterion r s) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  cases h with
  | pos h => exact hasCharPattern_mulSingle_one_of_pos (div_pos (mod_cast h) (mod_cast hs))
  | modEq_four hs' h => exact hasCharPattern_mulSingle_one_of_modEq_four hrs hs' h
  | dvd_right p k m hp hp2 hk hsm hm h =>
    have := Fact.mk hp
    rcases h with h | h
    · exact hasCharPattern_mulSingle_one_of_dvd_right_of_odd hrs hs.ne' h hsm hm
    · exact hasCharPattern_mulSingle_one_of_dvd_right hrs hs.ne' hk hsm hm h
  | dvd_right_two k m hsm hm h =>
    exact hasCharPattern_mulSingle_one_of_dvd_right_two hrs hs.ne' hsm hm h
  | dvd_left p k m hp hp4 hk hr hm h =>
    have := Fact.mk hp
    exact hasCharPattern_mulSingle_one_of_dvd_left hrs hs.ne' hp4 hk hr hm h
  | dvd_left_two k m hk hr h =>
    exact hasCharPattern_mulSingle_one_of_dvd_left_four hrs hs.ne' hk hr h


/-! ### Criteria for `τ` -/

/-- (T2) If a prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) and `(ms / p) = -1`, then `χ_p`
is a `τ`: its pattern is `(1, -1, -1, …)`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ}
    {m : ℤ} (hp4 : p % 4 = 3) (hk : 0 < k) (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (m * s) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  have hms : quadraticChar (ZMod p) (m * s) = -1 := by
    rw [← Int.cast_mul, ← h]
    exact jacobiSym.legendreSym.to_jacobiSym p _
  refine hasCharPattern_neg_mulSingle_one_of_apply (unitPartChar p (quadraticChar (ZMod p))) ?_
    fun n hn ↦ ?_
  · rw [unitPartChar_cSeq_one_of_eq_pow_mul hrs hs hN hk.ne' hr hm,
      ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4, hms]
    rfl
  · rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs hN one_ne_zero
      (by simpa [hr] using (dvd_pow_self (p : ℤ) hk.ne').mul_right m) hr hm _ hn, hms]

/-- (T2) If `r = 2^k m` with `k ≥ 2` and `ms ≡ 3 (mod 4)`, then `χ₄` is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_left_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 3) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hN : 4 = 2 ^ 2 := rfl
  have hm : ¬((2 : ℕ) : ℤ) ∣ m := by rintro ⟨t, rfl⟩; lia
  have hms : ZMod.χ₄ ((m : ZMod 4) * s) = -1 := by
    rw [← Int.cast_mul, χ₄_intCast_of_emod_four_eq_three h]
  refine hasCharPattern_neg_mulSingle_one_of_apply (unitPartChar 2 ZMod.χ₄) ?_ fun n hn ↦ ?_
  · rw [unitPartChar_cSeq_one_of_eq_pow_mul hrs hs hN (by lia : k ≠ 0) (mod_cast hr) hm, hms,
      show ZMod.χ₄ (-1) = -1 by decide]
    rfl
  · rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs hN two_ne_zero
      (hr ▸ (pow_dvd_pow 2 hk).mul_right m) (mod_cast hr) hm _ hn, hms]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`, `χ_ψ` has the
pattern `(1, y, -1, y, -1, …)` with `y = -ψ(s) χ_ψ(r + s)`; it is a `τ` if `y = -1`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0) {N j : ℕ}
    (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s) {ψ : MulChar (ZMod N) ℤ}
    (hψ : ψ (-1) = -1) (hy : ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  refine ⟨unitPartChar p ψ, fun n hn ↦ ?_⟩
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [unitPartChar_cSeq_two_mul_of_dvd_add hrs hs hN hj hNrs ψ (by lia), mul_assoc, hy, hψ,
      Pi.neg_apply, Pi.mulSingle_eq_of_ne (by lia)]
    rfl
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using unitPartChar_cSeq_one_of_dvd_add hrs hs hN hj hNrs ψ
    · rw [unitPartChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hN hj hNrs ψ hi, hψ, Pi.neg_apply,
        Pi.mulSingle_eq_of_ne (by lia)]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`: if
`ψ(s) χ_ψ(r + s) = -1` and `v_q(r + s)` is odd, then `χ_ψ val_q` is a `τ`:
`(1, 1, -1, 1, -1, …) · (1, -1, 1, -1, …) = (1, -1, -1, …)`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_of_valChar (hrs : IsCoprime r s)
    (hs : s ≠ 0) {N j : ℕ} (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s)
    {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) (hy : ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = -1)
    {q : ℕ} [Fact q.Prime] (hq : (q : ℤ) ∣ r + s) (hv : valChar q ((r + s : ℤ) : ℚ) = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  refine ⟨unitPartChar p ψ * valChar q, fun n hn ↦ ?_⟩
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [MulChar.coeToFun_mul, Pi.mul_apply, unitPartChar_cSeq_two_mul_of_dvd_add hrs hs hN hj hNrs
      ψ (by lia), valChar_cSeq_two_mul_of_dvd_add hrs hs hq (by lia), hψ, hv, Pi.neg_apply,
      Pi.mulSingle_eq_of_ne (by lia)]
    linear_combination hy
  · rw [MulChar.coeToFun_mul, Pi.mul_apply, valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hq,
      mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using unitPartChar_cSeq_one_of_dvd_add hrs hs hN hj hNrs ψ
    · rw [unitPartChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hN hj hNrs ψ hi, hψ, Pi.neg_apply,
        Pi.mulSingle_eq_of_ne (by lia)]

/-- (T3) At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`: if
`r + s ≠ ±□`, then `χ_ψ` or `χ_ψ val_q`, `v_q(r + s)` odd, is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_of_not_isSquare (hrs : IsCoprime r s)
    (hs : s ≠ 0) {N j : ℕ} (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s)
    {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) (h : ¬IsSquare (r + s))
    (h' : ¬IsSquare (-(r + s))) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hp : (p : ℤ) ∣ r + s := (dvd_pow_self (p : ℤ) hj).trans (mod_cast hN ▸ hNrs)
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit
    ((by simpa using hrs.add_mul_left_left 1 : IsCoprime (r + s) s).isUnit_of_dvd' hp h)
  have hrs0 : ((r + s : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast fun h0 : r + s = 0 ↦ h ⟨0, by simp [h0]⟩
  have hy : ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = 1 ∨
      ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = -1 := by
    rcases ψ.apply_eq_one_or_eq_neg_one (ZMod.isUnit_intCast_of_not_dvd hN hps) with h1 | h1 <;>
    rcases (unitPartChar p ψ).apply_eq_one_or_eq_neg_one hrs0.isUnit with h2 | h2 <;>
    rw [h1, h2] <;> norm_num
  rcases hy with hy | hy
  · exact hasCharPattern_neg_mulSingle_one_of_dvd_add hrs hs hN hj hNrs hψ hy
  · obtain ⟨q, _, hq, hv⟩ := exists_prime_dvd_valChar_eq_neg_one h h'
    exact hasCharPattern_neg_mulSingle_one_of_dvd_add_of_valChar hrs hs hN hj hNrs hψ hy hq hv

/-- (T3) If a prime `p ≡ 3 (mod 4)` divides `r + s = p^k m` (`p ∤ m`) and `(sm / p) = 1`, then
`χ_p` is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_prime (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hp4 : p % 4 = 3) (hk : 0 < k) (hrsm : r + s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (s * m) p = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  refine hasCharPattern_neg_mulSingle_one_of_dvd_add hrs hs (pow_one p).symm one_ne_zero
    (by simpa [hrsm] using (dvd_pow_self (p : ℤ) hk.ne').mul_right m)
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) ?_
  rw [hrsm, unitPartChar_intCast_pow_mul (pow_one p).symm _ k hm, ← map_mul, ← Int.cast_mul, ← h]
  exact jacobiSym.legendreSym.to_jacobiSym p _

/-- (T3) If `r + s = 2^k m` with `k ≥ 2` and `sm ≡ 1 (mod 4)`, then `χ₄` is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hrsm : r + s = 2 ^ k * m) (h : s * m % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hm : ¬((2 : ℕ) : ℤ) ∣ m := by rintro ⟨t, rfl⟩; lia
  refine hasCharPattern_neg_mulSingle_one_of_dvd_add (p := 2) hrs hs rfl two_ne_zero
    (hrsm ▸ (pow_dvd_pow 2 hk).mul_right m) (show ZMod.χ₄ (-1) = -1 by decide) ?_
  rw [show r + s = ((2 : ℕ) : ℤ) ^ k * m by simpa using hrsm,
    unitPartChar_intCast_pow_mul (N := 4) (j := 2) rfl _ k hm, ← map_mul, ← Int.cast_mul,
    χ₄_intCast_of_emod_four_eq_one h]

/-- (T4) In the window `a < -1`, `c_3 < 0 < c_4`, with `v_q(r + s)` odd, `sgn · val_q` is a `τ`:
`(+, +, -, +, -, …) · (+, -, +, -, …) = (+, -, -, …)`. -/
theorem hasCharPattern_neg_mulSingle_one_of_window (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r < -s) (h₃ : cSeq ((r : ℚ) / s) 3 < 0) (h₄ : 0 < cSeq ((r : ℚ) / s) 4) {q : ℕ}
    [Fact q.Prime] (hq : (q : ℤ) ∣ r + s) (hv : valChar q ((r + s : ℤ) : ℚ) = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have ha' : (r : ℚ) / s < -1 := by
    rw [div_lt_iff₀ (mod_cast hs)]
    exact_mod_cast (by lia : r < -1 * s)
  refine ⟨signChar * valChar q, fun n hn ↦ ?_⟩
  rw [MulChar.coeToFun_mul, Pi.mul_apply]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [signChar_apply_of_pos (h₄.trans_le (cSeq_mem_Icc_of_even ha' h₃ h₄ (by lia)
      (even_two_mul i)).1), valChar_cSeq_two_mul_of_dvd_add hrs hs.ne' hq (by lia), hv,
      Pi.neg_apply, Pi.mulSingle_eq_of_ne (by lia)]
    rfl
  · rw [valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs.ne' hq, mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using signChar_apply_of_pos (by linarith : 0 < -((r : ℚ) / s))
    · rw [signChar_apply_of_neg ((cSeq_mem_Icc_of_odd ha' h₃ h₄ (by lia)
        (odd_two_mul_add_one i)).2.trans_lt h₃), Pi.neg_apply, Pi.mulSingle_eq_of_ne (by lia)]

/-- (T4) In the window `a < -1`, `r w_3 < 0 < r w_4`, with `r + s ≠ ±□`, `a` has `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_window' (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r < -s) (h₃ : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0)
    (h₄ : 0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) (h : ¬IsSquare (r + s))
    (h' : ¬IsSquare (-(r + s))) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  obtain ⟨q, _, hq, hv⟩ := exists_prime_dvd_valChar_eq_neg_one h h'
  have hs' : (0 : ℚ) < s := mod_cast hs
  refine hasCharPattern_neg_mulSingle_one_of_window hrs hs ha ?_ ?_ hq hv
  · rw [cSeq_div_eq r hs.ne' (by norm_num)]
    exact div_neg_of_neg_of_pos (mod_cast mul_wSeq_three r s ▸ h₃) (by positivity)
  · rw [cSeq_div_eq r hs.ne' (by norm_num)]
    exact div_pos (mod_cast mul_wSeq_four r s ▸ h₄) (by positivity)

/-- (T1) For `-1 < a < 0` the sign is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_neg_lt (hs : 0 < s) (h₁ : -s < r) (h₀ : r < 0) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hs' : (0 : ℚ) < s := mod_cast hs
  refine hasCharPattern_neg_mulSingle_one_of_neg_one_lt ?_ (div_neg_of_neg_of_pos (mod_cast h₀) hs')
  rw [lt_div_iff₀ hs']
  exact_mod_cast (by lia : -1 * s < r)

/-- (T3) If `r + s ≠ ±□` is divisible by `4` or by a prime `p ≡ 3 (mod 4)`, then `a` has `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_not_isSquare_add (hrs : IsCoprime r s) (hs : s ≠ 0)
    (h : ¬IsSquare (r + s)) (h' : ¬IsSquare (-(r + s)))
    (hdvd : 4 ∣ r + s ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ r + s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  rcases hdvd with h4 | ⟨p, hp, hp4, hpd⟩
  · exact hasCharPattern_neg_mulSingle_one_of_dvd_add_of_not_isSquare (p := 2) hrs hs
      (N := 4) rfl two_ne_zero h4 (show ZMod.χ₄ (-1) = -1 by decide) h h'
  · have := Fact.mk hp
    exact hasCharPattern_neg_mulSingle_one_of_dvd_add_of_not_isSquare hrs hs
      (pow_one p).symm one_ne_zero (by simpa using hpd)
      (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) h h'

/-- **Criteria for `τ`** (Proposition T): each of (T1)–(T4) gives a character that is `1` at
`c_1` and `-1` at all later terms. -/
theorem hasCharPattern_neg_mulSingle_one_of_negTailCriterion (hrs : IsCoprime r s) (hs : 0 < s)
    (h : NegTailCriterion r s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  cases h with
  | neg_one_lt h₁ h₀ => exact hasCharPattern_neg_mulSingle_one_of_neg_lt hs h₁ h₀
  | dvd_left p k m hp hp4 hk hr hm h =>
    have := Fact.mk hp
    exact hasCharPattern_neg_mulSingle_one_of_dvd_left hrs hs.ne' hp4 hk hr hm h
  | dvd_left_two k m hk hr h =>
    exact hasCharPattern_neg_mulSingle_one_of_dvd_left_four hrs hs.ne' hk hr h
  | dvd_add p k m hp hp4 hk hrsm hm h =>
    have := Fact.mk hp
    exact hasCharPattern_neg_mulSingle_one_of_dvd_add_prime hrs hs.ne' hp4 hk hrsm hm h
  | dvd_add_two k m hk hrsm h =>
    exact hasCharPattern_neg_mulSingle_one_of_dvd_add_four hrs hs.ne' hk hrsm h
  | not_isSquare_add h h' hdvd =>
    exact hasCharPattern_neg_mulSingle_one_of_not_isSquare_add hrs hs.ne' h h' hdvd
  | window hr h₃ h₄ h h' => exact hasCharPattern_neg_mulSingle_one_of_window' hrs hs hr h₃ h₄ h h'

end Prime

/-- (Z1) If `r ≠ ±□`, then `val_p` is a `φ₀` for a prime `p` with `v_p(r)` odd. -/
theorem hasCharPattern_neg_one_of_not_isSquare (hrs : IsCoprime r s) (hs : s ≠ 0)
    (h : ¬IsSquare r) (h' : ¬IsSquare (-r)) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  obtain ⟨p, hp, hodd⟩ := exists_prime_odd_factorization h h'
  have := Fact.mk hp
  have hr0 : r ≠ 0 := by rintro rfl; exact h ⟨0, by simp⟩
  have hpr : (p : ℤ) ∣ r :=
    Int.natCast_dvd.mpr (Nat.dvd_of_factorization_pos (Nat.pos_of_ne_zero hodd.pos.ne').ne')
  have hv : valChar p (r : ℚ) = -1 := by
    rw [valChar_intCast hr0, padicValInt, ← Nat.factorization_def _ hp, hodd.neg_one_pow]
  exact ⟨valChar p, fun n hn ↦ by rw [valChar_cSeq_of_dvd_left hrs hs hpr hn, hv]; rfl⟩

/-- (Z4) If `r = 2^k m` with `k ≥ 3` and `ms ≡ ±3 (mod 8)`, then `χ₈` is a `φ₀`:
`χ₈(c_n) = χ₈(ms)` for all `n`, as `χ₈(-1) = 1`. -/
theorem hasCharPattern_neg_one_of_dvd_left_two (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ} {m : ℤ}
    (hk : 3 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 8 = 3 ∨ m * s % 8 = 5) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hN : 8 = 2 ^ 3 := rfl
  have hm : ¬((2 : ℕ) : ℤ) ∣ m := by rintro ⟨t, rfl⟩; lia
  have hs2 : ¬((2 : ℕ) : ℤ) ∣ s := by rintro ⟨t, rfl⟩; lia
  have hχr : unitPartChar 2 ZMod.χ₈ r = ZMod.χ₈ m := by
    rw [hr]
    exact_mod_cast unitPartChar_intCast_pow_mul hN ZMod.χ₈ k hm
  have hms : ZMod.χ₈ s * ZMod.χ₈ m = -1 := by
    rw [← map_mul, mul_comm, ← Int.cast_mul, ZMod.χ₈_int_eq_if_mod_eight]
    split_ifs <;> lia
  refine ⟨unitPartChar 2 ZMod.χ₈, fun n hn ↦ ?_⟩
  rcases hn.eq_or_lt with rfl | hn
  · rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hs2, hχr,
      show ZMod.χ₈ (-1) = 1 by decide, one_mul, mul_comm, hms]
    rfl
  · rw [unitPartChar_cSeq_of_dvd_left hrs hs hN (by norm_num)
      (hr ▸ (pow_dvd_pow 2 hk).mul_right m) _ hn, hχr, hms]
    rfl

/-- **Criteria for `φ₀`** (Proposition Z): each of (Z1)–(Z4) gives a character that is `-1` at
every `c_n`. -/
theorem hasCharPattern_neg_one_of_negAllCriterion (hrs : IsCoprime r s) (hs : s ≠ 0)
    (h : NegAllCriterion r s) : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  cases h with
  | not_isSquare h h' => exact hasCharPattern_neg_one_of_not_isSquare hrs hs h h'
  | dvd_add_two_mul p hp hp8 hdvd =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_add_two_mul hrs hp8 hdvd
  | dvd_sq_add_sq p hp hp2 hdvd h₁ h₂ =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_sq_add_sq hrs hp2 hdvd h₁ h₂
  | dvd_left p k m hp hp4 hk hr hm h =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_left hrs hs hp4 hk hr hm h
  | dvd_left_two k m hk hr h => exact hasCharPattern_neg_one_of_dvd_left_two hrs hs hk hr h

/-- A prime `p ≡ 3 (mod 4)` dividing `r ≠ 0` gives `φ₁` from `φ₀`: by (O5) or (T2), according to
the Jacobi symbol `(ms/p)` for `r = p^k m`, and `φ₀ τ = φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_prime_dvd (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hr : r ≠ 0) {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hpr : (p : ℤ) ∣ r)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  obtain ⟨k, m, hk, hrm, hm⟩ := Int.exists_pow_mul_of_dvd Fact.out hr hpr
  have hp := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hps : ¬(p : ℤ) ∣ s := fun h ↦ hp.not_isUnit (hrs.isUnit_of_dvd' hpr h)
  have hgcd : (m * s).gcd p = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    (hp.coprime_iff_not_dvd.mpr fun h ↦ (hp.dvd_or_dvd h).elim hm hps).symm
  rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
  · exact hasCharPattern_mulSingle_one_of_dvd_left hrs hs hp4 hk hrm hm h
  · exact hasCharPattern_mulSingle_of_neg_of_neg_mulSingle h₀
      (hasCharPattern_neg_mulSingle_one_of_dvd_left hrs hs hp4 hk hrm hm h)

end QuadraticIterates
