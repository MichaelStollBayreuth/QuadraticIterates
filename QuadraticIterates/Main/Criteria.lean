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

import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Data.Nat.Factorization.Basic
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticIterates.Mathlib.RingTheory.Coprime.Basic
import QuadraticIterates.Mathlib.RingTheory.Int.Basic
import QuadraticIterates.Mathlib.RingTheory.Multiplicity
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Patterns.Primes
import QuadraticIterates.Patterns.Sign
import QuadraticIterates.Sequence.Signs
import QuadraticIterates.Sequence.SquareClasses

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
  `QuadraticIterates.hasCharPattern_neg_mulSingle_one_of_negTailCriterion`: each list gives its
  pattern.
* `QuadraticIterates.negFirstCriterion_of_not_isSquare_right`,
  `QuadraticIterates.negFirstCriterion_or_negTailCriterion_of_prime_dvd`,
  `QuadraticIterates.negFirstCriterion_or_negTailCriterion_of_four_dvd`,
  `QuadraticIterates.negTailCriterion_of_emod_four`: (O3)/(O4) from a non-square `s`, (O5) or (T2)
  from a prime `p ≡ 3 (mod 4)` or from `4` dividing `r`, and (T3) from the residue of `r + s`
  modulo `4`.
* `QuadraticIterates.hasCharPattern_mulSingle_one_of_prime_dvd`: `φ₁` from `φ₀` and a prime
  `p ≡ 3 (mod 4)` dividing `r`.
* `QuadraticIterates.negAllCriterion_of_modEq_four`,
  `QuadraticIterates.hasCharPattern_neg_one_of_modEq_four`: `a ≡ 1 mod 4` has `φ₀`, by (Z1)
  or (Z2); with `QuadraticIterates.hasCharPattern_mulSingle_one_of_modEq_four` ((O2)) it has `φ₀`
  and `φ₁`.

## Notation

In the docstrings, `(x / p)` is the Jacobi symbol `jacobiSym x p`, and the characters of `ℚ` at a
prime `p` are `val_p = Rat.valChar p` and, for odd `p`,
`χ_p = Rat.unitPartChar p (quadraticChar (ZMod p))`; at `p = 2` they are `val₂ = Rat.valChar 2`,
`χ₄ = Rat.unitPartChar 2 ZMod.χ₄` and `χ₈ = Rat.unitPartChar 2 ZMod.χ₈`.
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
  /-- (Z3) A prime `p ≡ 5 (mod 8)` divides `r² + s²`, and `((r - s)s / p) = -1`. -/
  | dvd_sq_add_sq (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 5) (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2)
      (h : jacobiSym ((r - s) * s) p = -1)
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

private lemma exists_prime_odd_factorization (h : ¬IsSquare r) (h' : ¬IsSquare (-r)) :
    ∃ p, p.Prime ∧ Odd (r.natAbs.factorization p) := by
  rw [Int.isSquare_iff_nonneg_even_factorization] at h h'
  push Not at h h'
  rcases le_total 0 r with hr | hr
  · obtain ⟨p, hp, hodd⟩ := h hr
    exact ⟨p, hp, Nat.not_even_iff_odd.mp hodd⟩
  · obtain ⟨p, hp, hodd⟩ := h' (neg_nonneg.mpr hr)
    exact ⟨p, hp, Nat.not_even_iff_odd.mp (by simpa using hodd)⟩

/-- An integer `x ≠ ±□` has a prime `q` with `v_q(x)` odd, that is, with `val_q(x) = -1`. -/
theorem exists_prime_dvd_valChar_eq_neg_one {x : ℤ} (h : ¬IsSquare x) (h' : ¬IsSquare (-x)) :
    ∃ q : ℕ, ∃ _ : Fact q.Prime, (q : ℤ) ∣ x ∧ valChar q (x : ℚ) = -1 := by
  obtain ⟨q, hq, hodd⟩ := exists_prime_odd_factorization h h'
  have := Fact.mk hq
  have hx0 : x ≠ 0 := fun h0 ↦ h (h0 ▸ .zero)
  refine ⟨q, this, Int.natCast_dvd.mpr (Nat.dvd_of_factorization_pos hodd.pos.ne'), ?_⟩
  rw [valChar_intCast hx0, padicValInt, ← Nat.factorization_def _ hq, hodd.neg_one_pow]

private lemma quadraticChar_intCast {p : ℕ} [Fact p.Prime] (a : ℤ) :
    quadraticChar (ZMod p) a = jacobiSym a p :=
  jacobiSym.legendreSym.to_jacobiSym p a

private lemma quadraticChar_two {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    quadraticChar (ZMod p) 2 = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr fun h ↦ by
    lia [(ZMod.exists_sq_eq_two_iff (by lia)).mp h]

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `r = p^k m` (`p ∤ m`), `χ_ψ` has the pattern
`(ψ(-1) x, x, x, …)` with `x = ψ(ms)`. -/
private lemma unitPartChar_cSeq_of_eq_pow_mul (hrs : IsCoprime r s) (hs : s ≠ 0) {N j k : ℕ}
    (hN : N = p ^ j) (hj : j ≠ 0) (hjk : j ≤ k) {m : ℤ} (hr : r = p ^ k * m)
    (hm : ¬(p : ℤ) ∣ m) (ψ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : 1 ≤ n) :
    unitPartChar p ψ (cSeq ((r : ℚ) / s) n) = (Pi.mulSingle 1 (ψ (-1)) : ℕ → ℤ) n * ψ (m * s) := by
  rcases hn.eq_or_lt with rfl | hn
  · have hps : ¬(p : ℤ) ∣ s :=
      Int.Prime.not_dvd_of_isCoprime Fact.out hrs.symm (hr ▸ (dvd_pow_self _ (by lia)).mul_right m)
    rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hps, hr,
      unitPartChar_intCast_pow_mul hN ψ k hm, mul_assoc, ← map_mul, Pi.mulSingle_eq_same]
  · have hNr : (N : ℤ) ∣ r := by
      rw [hN, hr, Nat.cast_pow]
      exact (pow_dvd_pow _ hjk).mul_right m
    rw [unitPartChar_cSeq_of_dvd_left hrs hs hN hj hNr ψ hn, hr,
      unitPartChar_intCast_pow_mul hN ψ k hm, Pi.mulSingle_eq_of_ne (by lia), one_mul, ← map_mul,
      mul_comm]

/-! ### Criteria for `φ₀` -/

/-- (Z1) If `r ≠ ±□`, then `val_p` is a `φ₀` for a prime `p` with `v_p(r)` odd. -/
theorem hasCharPattern_neg_one_of_not_isSquare (hrs : IsCoprime r s) (hs : s ≠ 0)
    (h : ¬IsSquare r) (h' : ¬IsSquare (-r)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  obtain ⟨p, _, hpr, hv⟩ := exists_prime_dvd_valChar_eq_neg_one h h'
  exact ⟨valChar p, fun n hn ↦ (valChar_cSeq_of_dvd_left hrs hs hpr hn).trans hv⟩

/-- (Z2) If a prime `p ≡ ±3 (mod 8)` divides `r + 2s`, then `χ_p` is a `φ₀`: it is `(2 / p) = -1`
at every `c_n`. -/
theorem hasCharPattern_neg_one_of_dvd_add_two_mul (hrs : IsCoprime r s)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hdvd : (p : ℤ) ∣ r + 2 * s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) :=
  ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ (unitPartChar_cSeq_of_dvd_add_two_mul hrs
    (pow_one p).symm one_ne_zero (by lia) hdvd _ hn).trans (quadraticChar_two hp8)⟩

/-- At a prime `p ≡ 5 (mod 8)` dividing `r² + s²` but not `s`, `(-rs / p) = -1`: modulo `p`,
`-rs = -(r/s) s²`, and `r/s` is a square root of `-1`
(`ZMod.quadraticChar_eq_neg_one_of_sq_eq_neg_one`). -/
private lemma jacobiSym_neg_mul_of_dvd_sq_add_sq (hp8 : p % 8 = 5)
    (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2) (hs : ¬(p : ℤ) ∣ s) : jacobiSym (-(r * s)) p = -1 := by
  have hs0 : (s : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have ht : ((r : ZMod p) / s) ^ 2 = -1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at this
    field_simp
    linear_combination this
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_neg, Int.cast_mul,
    show -((r : ZMod p) * s) = -1 * (r / s) * s ^ 2 by field, map_mul, map_mul,
    quadraticChar_sq_one' hs0, ZMod.quadraticChar_eq_neg_one_of_sq_eq_neg_one hp8 ht,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_one (by lia)]
  rfl

/-- (Z3) If a prime `p ≡ 5 (mod 8)` divides `r² + s²` and `((r - s)s / p) = -1`, then `χ_p` is a
`φ₀`: modulo `p` the sequence alternates between `-a` and `a - 1`, `a² = -1`, and
`(-a / p) = -1`. -/
theorem hasCharPattern_neg_one_of_dvd_sq_add_sq (hrs : IsCoprime r s) (hp8 : p % 8 = 5)
    (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2) (h₂ : jacobiSym ((r - s) * s) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hs : ¬(p : ℤ) ∣ s := fun hps ↦ by
    rw [← jacobiSym.legendreSym.to_jacobiSym, (legendreSym.eq_zero_iff p _).mpr (by
      simp [(ZMod.intCast_zmod_eq_zero_iff_dvd s p).mpr hps])] at h₂
    exact absurd h₂ (by decide)
  have h₁ := jacobiSym_neg_mul_of_dvd_sq_add_sq hp8 hdvd hs
  have hp2 : p ≠ 2 := by lia
  have hN : p = p ^ 1 := (pow_one p).symm
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [unitPartChar_cSeq_two_mul_of_dvd_sq_add_sq hrs hN one_ne_zero hp2 hdvd _ (by lia),
      ← Int.cast_sub, ← Int.cast_mul, quadraticChar_intCast, h₂]
    rfl
  · rw [unitPartChar_cSeq_two_mul_add_one_of_dvd_sq_add_sq hrs hN one_ne_zero hdvd, ← Int.cast_mul,
      ← Int.cast_neg, quadraticChar_intCast, h₁]
    rfl

/-- (Z4) If a prime `p ≡ 1 (mod 4)` divides `r = p^k m` (`p ∤ m`) and `(ms / p) = -1`, then `χ_p`
is a `φ₀`: `χ_p(c_n) = (-1 / p)^{[n = 1]} (ms / p)` with `(-1 / p) = 1`. -/
theorem hasCharPattern_neg_one_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ} {m : ℤ}
    (hp4 : p % 4 = 1) (hk : 0 < k) (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (m * s) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hms : quadraticChar (ZMod p) (m * s) = -1 := by rw [← Int.cast_mul, quadraticChar_intCast, h]
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (pow_one p).symm one_ne_zero hk hr hm _ hn,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_one hp4, Pi.mulSingle_one, hms]
  rfl

/-- (Z4) If `r = 2^k m` with `k ≥ 3` and `ms ≡ ±3 (mod 8)`, then `χ₈` is a `φ₀`:
`χ₈(c_n) = χ₈(ms)` for all `n`, as `χ₈(-1) = 1`. -/
theorem hasCharPattern_neg_one_of_dvd_left_two (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ} {m : ℤ}
    (hk : 3 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 8 = 3 ∨ m * s % 8 = 5) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  have hms : ZMod.χ₈ ((m : ZMod 8) * s) = -1 := by
    rw [← Int.cast_mul, ZMod.χ₈_int_eq_if_mod_eight]
    split_ifs <;> lia
  refine ⟨unitPartChar 2 ZMod.χ₈, fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (rfl : 8 = 2 ^ 3) three_ne_zero hk (mod_cast hr)
    (by rintro ⟨t, rfl⟩; lia) _ hn, hms, show ZMod.χ₈ (-1) = 1 by decide, Pi.mulSingle_one]
  rfl

/-- **Criteria for `φ₀`**: each of (Z1)–(Z4) gives a character that is `-1` at every `c_n`. -/
theorem hasCharPattern_neg_one_of_negAllCriterion (hrs : IsCoprime r s) (hs : s ≠ 0)
    (h : NegAllCriterion r s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) := by
  cases h with
  | not_isSquare h h' => exact hasCharPattern_neg_one_of_not_isSquare hrs hs h h'
  | dvd_add_two_mul p hp hp8 hdvd =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_add_two_mul hrs hp8 hdvd
  | dvd_sq_add_sq p hp hp8 hdvd h =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_sq_add_sq hrs hp8 hdvd h
  | dvd_left p k m hp hp4 hk hr hm h =>
    have := Fact.mk hp
    exact hasCharPattern_neg_one_of_dvd_left hrs hs hp4 hk hr hm h
  | dvd_left_two k m hk hr h => exact hasCharPattern_neg_one_of_dvd_left_two hrs hs hk hr h

/-! ### Criteria for `φ₁` -/

/-- (O5) If a prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) and `(ms / p) = 1`, then `χ_p`
is a `φ₁`: its pattern is `((-1 / p), 1, 1, …)`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ}
    {m : ℤ} (hp4 : p % 4 = 3) (hk : 0 < k) (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (m * s) p = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hms : quadraticChar (ZMod p) (m * s) = 1 := by rw [← Int.cast_mul, quadraticChar_intCast, h]
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (pow_one p).symm one_ne_zero hk hr hm _ hn,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4, hms, mul_one]

/-- (O5) If `r = 2^k m` with `k ≥ 2` and `ms ≡ 1 (mod 4)`, then `χ₄` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_left_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hms : ZMod.χ₄ ((m : ZMod 4) * s) = 1 := mod_cast ZMod.χ₄_int_one_mod_four h
  refine ⟨unitPartChar 2 ZMod.χ₄, fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (rfl : 4 = 2 ^ 2) two_ne_zero hk (mod_cast hr)
    (by rintro ⟨t, rfl⟩; lia) _ hn, hms, show ZMod.χ₄ (-1) = -1 by decide, mul_one]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `s = p^k m` (`p ∤ m`), `χ_ψ` is `ψ(-rm)` at `c_1`
and `1` at all later terms: it is a `φ₁` if `ψ(-rm) = -1`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_of_apply (hrs : IsCoprime r s) (hs : s ≠ 0)
    {N j k : ℕ} (hN : N = p ^ j) (hj : j ≠ 0) (hjk : j ≤ k) {m : ℤ} (hsm : s = p ^ k * m)
    (hm : ¬(p : ℤ) ∣ m) (ψ : MulChar (ZMod N) ℤ) (h : ψ (-(r * m)) = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hNs : (N : ℤ) ∣ s := by
    rw [hN, hsm, Nat.cast_pow]
    exact (pow_dvd_pow _ hjk).mul_right m
  have hpr : ¬(p : ℤ) ∣ r :=
    Int.Prime.not_dvd_of_isCoprime Fact.out hrs (hsm ▸ (dvd_pow_self _ (by lia)).mul_right m)
  refine hasCharPattern_mulSingle_one_of_apply (unitPartChar p ψ) ?_
    fun n hn ↦ unitPartChar_cSeq_of_dvd_right hrs hs hN hj hNs ψ hn
  rw [mulChar_cSeq_one_eq_mul _ hs, unitPartChar_neg_one hN, unitPartChar_intCast hN hpr, hsm,
    unitPartChar_intCast_pow_mul hN ψ k hm, ← map_mul, ← map_mul, neg_one_mul, neg_mul, h]

/-- (O3), (O4) If `s = p^k m` with `k` odd (`p ∤ m`), then `val_p` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_of_odd (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : Odd k) (hsm : s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  have hps : (p : ℤ) ∣ s := hsm ▸ (dvd_pow_self _ hk.pos.ne').mul_right m
  have hpr : ¬(p : ℤ) ∣ r := Int.Prime.not_dvd_of_isCoprime Fact.out hrs hps
  refine hasCharPattern_mulSingle_one_of_apply (valChar p) ?_
    fun n hn ↦ valChar_cSeq_of_dvd_right hrs hs hps hn
  rw [mulChar_cSeq_one_eq_mul _ hs, valChar_neg_one, valChar_intCast_of_not_dvd hpr, hsm,
    valChar_intCast_pow_mul k hm, hk.neg_one_pow, one_mul, one_mul]

/-- (O3) If an odd prime `p` divides `s = p^k m` (`p ∤ m`) and `(-rm / p) = -1`, then `χ_p` is
a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right (hrs : IsCoprime r s) (hs : s ≠ 0) {k : ℕ}
    {m : ℤ} (hk : 0 < k) (hsm : s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m)
    (h : jacobiSym (-(r * m)) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) :=
  hasCharPattern_mulSingle_one_of_dvd_right_of_apply hrs hs (pow_one p).symm one_ne_zero hk hsm hm
    (quadraticChar (ZMod p)) (by rw [← Int.cast_mul, ← Int.cast_neg, quadraticChar_intCast, h])

/-- (O4) If `s = 2^k m` with `k ≥ 2` and `rm ≡ 1 (mod 4)`, then `χ₄` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hsm : s = 2 ^ k * m) (h : r * m % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) :=
  hasCharPattern_mulSingle_one_of_dvd_right_of_apply hrs hs (rfl : 4 = 2 ^ 2) two_ne_zero hk
    (mod_cast hsm) (by rintro ⟨t, rfl⟩; lia) ZMod.χ₄
    (by rw [← Int.cast_mul, ← Int.cast_neg, ZMod.χ₄_int_three_mod_four (by lia)])

/-- (O4) If `s = 2^k m` with `k ≥ 3` and `rm ≡ ±3 (mod 8)`, then `χ₈` is a `φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_eight (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 3 ≤ k) (hsm : s = 2 ^ k * m) (h : r * m % 8 = 3 ∨ r * m % 8 = 5) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) :=
  hasCharPattern_mulSingle_one_of_dvd_right_of_apply hrs hs (rfl : 8 = 2 ^ 3) three_ne_zero hk
    (mod_cast hsm) (by rintro ⟨t, rfl⟩; lia) ZMod.χ₈ (by
      rw [← Int.cast_mul, ← Int.cast_neg, ZMod.χ₈_int_eq_if_mod_eight]
      split_ifs <;> lia)

/-- (O4): the three cases `k` odd (`val₂`), `rm ≡ 1 (mod 4)` (`χ₄`), `rm ≡ 3 (mod 8)` (`χ₈`). -/
theorem hasCharPattern_mulSingle_one_of_dvd_right_two (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hsm : s = 2 ^ k * m) (hm : Odd m)
    (h : Odd k ∨ (k = 2 ∧ r * m % 4 = 1) ∨ (Even k ∧ 4 ≤ k ∧ r * m % 8 ≠ 7)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  rcases h with h | ⟨rfl, h⟩ | ⟨-, hk, h⟩
  · exact hasCharPattern_mulSingle_one_of_dvd_right_of_odd (p := 2) hrs hs h (mod_cast hsm)
      (by simpa [← even_iff_two_dvd] using hm)
  · exact hasCharPattern_mulSingle_one_of_dvd_right_four hrs hs le_rfl hsm h
  · have hr : Odd r := Int.isCoprime_two_right.mp
      (hrs.of_isCoprime_of_dvd_right (hsm ▸ (dvd_pow_self 2 (by lia)).mul_right m))
    rcases (by lia [Int.odd_iff.mp (hr.mul hm)] : r * m % 8 = 3 ∨ r * m % 4 = 1) with h' | h'
    · exact hasCharPattern_mulSingle_one_of_dvd_right_eight hrs hs (by lia) hsm (.inl h')
    · exact hasCharPattern_mulSingle_one_of_dvd_right_four hrs hs (by lia) hsm h'

/-- **Criteria for `φ₁`**: each of (O1)–(O5) gives a character that is `-1` at `c_1` and `1` at
all later terms. -/
theorem hasCharPattern_mulSingle_one_of_negFirstCriterion (hrs : IsCoprime r s) (hs : 0 < s)
    (h : NegFirstCriterion r s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
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
  have hms : quadraticChar (ZMod p) (m * s) = -1 := by rw [← Int.cast_mul, quadraticChar_intCast, h]
  refine ⟨unitPartChar p (quadraticChar (ZMod p)), fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (pow_one p).symm one_ne_zero hk hr hm _ hn,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4, hms, mul_neg_one]
  rfl

/-- (T2) If `r = 2^k m` with `k ≥ 2` and `ms ≡ 3 (mod 4)`, then `χ₄` is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_left_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 3) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hms : ZMod.χ₄ ((m : ZMod 4) * s) = -1 := mod_cast ZMod.χ₄_int_three_mod_four h
  refine ⟨unitPartChar 2 ZMod.χ₄, fun n hn ↦ ?_⟩
  rw [unitPartChar_cSeq_of_eq_pow_mul hrs hs (rfl : 4 = 2 ^ 2) two_ne_zero hk (mod_cast hr)
    (by rintro ⟨t, rfl⟩; lia) _ hn, hms, show ZMod.χ₄ (-1) = -1 by decide, mul_neg_one]
  rfl

/-- A character that is `1` at `v 1` and `-1` at `v (2j)` and `v (2j + 1)` for `j ≥ 1` realizes
`τ` from `1` on. -/
private lemma hasCharPattern_neg_mulSingle_one_of_parity {M : Type*} [CommMonoid M] {v : ℕ → M}
    (χ : MulChar M ℤ) (h₁ : χ (v 1) = 1) (hodd : ∀ j ≥ 1, χ (v (2 * j + 1)) = -1)
    (heven : ∀ j ≥ 1, χ (v (2 * j)) = -1) :
    HasCharPattern v 1 (-Pi.mulSingle 1 (-1)) :=
  hasCharPattern_neg_mulSingle_one_of_apply χ h₁ fun n hn ↦ by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    exacts [heven j (by lia), hodd j (by lia)]

/-- If `χ` has the pattern `(1, 1, -1, 1, -1, …)` along `(c_n)` and `v_q(r + s)` is odd, then
`χ val_q` is a `τ`: `val_q` has the pattern `(1, -1, 1, -1, …)`. -/
private lemma hasCharPattern_neg_mulSingle_one_of_mul_valChar (hrs : IsCoprime r s) (hs : s ≠ 0)
    {q : ℕ} [Fact q.Prime] (hq : (q : ℤ) ∣ r + s) (hv : valChar q ((r + s : ℤ) : ℚ) = -1)
    {χ : MulChar ℚ ℤ} (h₁ : χ (cSeq ((r : ℚ) / s) 1) = 1)
    (hodd : ∀ j ≥ 1, χ (cSeq ((r : ℚ) / s) (2 * j + 1)) = -1)
    (heven : ∀ j ≥ 1, χ (cSeq ((r : ℚ) / s) (2 * j)) = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  refine hasCharPattern_neg_mulSingle_one_of_parity (χ * valChar q) ?_ (fun j hj ↦ ?_)
    fun j hj ↦ ?_
  · rw [MulChar.mul_apply, h₁, one_mul]
    exact valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hq 0
  · rw [MulChar.mul_apply, hodd j hj, valChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hq, mul_one]
  · rw [MulChar.mul_apply, heven j hj, valChar_cSeq_two_mul_of_dvd_add hrs hs hq hj, hv, one_mul]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`, `χ_ψ` has the
pattern `(1, y, -1, y, -1, …)` with `y = -ψ(s) χ_ψ(r + s)`; it is a `τ` if `y = -1`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add (hrs : IsCoprime r s) (hs : s ≠ 0) {N j : ℕ}
    (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s) {ψ : MulChar (ZMod N) ℤ}
    (hψ : ψ (-1) = -1) (hy : ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) :=
  hasCharPattern_neg_mulSingle_one_of_parity _
    (unitPartChar_cSeq_one_of_dvd_add hrs hs hN hj hNrs ψ)
    (fun i hi ↦ (unitPartChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hN hj hNrs ψ hi).trans hψ)
    fun i hi ↦ by
      rw [unitPartChar_cSeq_two_mul_of_dvd_add hrs hs hN hj hNrs ψ hi, mul_assoc, hy, hψ, mul_one]

/-- At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`: if
`ψ(s) χ_ψ(r + s) = -1` and `v_q(r + s)` is odd, then `χ_ψ val_q` is a `τ`:
`(1, 1, -1, 1, -1, …) · (1, -1, 1, -1, …) = (1, -1, -1, …)`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_of_valChar (hrs : IsCoprime r s)
    (hs : s ≠ 0) {N j : ℕ} (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s)
    {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) (hy : ψ s * unitPartChar p ψ ((r + s : ℤ) : ℚ) = -1)
    {q : ℕ} [Fact q.Prime] (hq : (q : ℤ) ∣ r + s) (hv : valChar q ((r + s : ℤ) : ℚ) = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) :=
  hasCharPattern_neg_mulSingle_one_of_mul_valChar hrs hs hq hv
    (unitPartChar_cSeq_one_of_dvd_add hrs hs hN hj hNrs ψ)
    (fun i hi ↦ (unitPartChar_cSeq_two_mul_add_one_of_dvd_add hrs hs hN hj hNrs ψ hi).trans hψ)
    fun i hi ↦ by rw [unitPartChar_cSeq_two_mul_of_dvd_add hrs hs hN hj hNrs ψ hi, mul_assoc, hy,
      hψ, neg_one_mul, neg_neg]

/-- (T3) At a power `N = p^j` (`j ≥ 1`) dividing `r + s` and `ψ` with `ψ(-1) = -1`: if
`r + s ≠ ±□`, then `χ_ψ` or `χ_ψ val_q`, `v_q(r + s)` odd, is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_of_not_isSquare (hrs : IsCoprime r s)
    (hs : s ≠ 0) {N j : ℕ} (hN : N = p ^ j) (hj : j ≠ 0) (hNrs : (N : ℤ) ∣ r + s)
    {ψ : MulChar (ZMod N) ℤ} (hψ : ψ (-1) = -1) (h : ¬IsSquare (r + s))
    (h' : ¬IsSquare (-(r + s))) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hp : (p : ℤ) ∣ r + s := (dvd_pow_self (p : ℤ) hj).trans (mod_cast hN ▸ hNrs)
  have hps : ¬(p : ℤ) ∣ s := Int.Prime.not_dvd_of_isCoprime Fact.out hrs.symm.add_self_right hp
  have hrs0 : ((r + s : ℤ) : ℚ) ≠ 0 := mod_cast fun h0 : r + s = 0 ↦ h (h0 ▸ .zero)
  rcases Int.isUnit_iff.mp (((ZMod.isUnit_intCast_of_not_dvd hN hps).map ψ).mul
    (hrs0.isUnit.map (unitPartChar p ψ))) with hy | hy
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
    (hrsm ▸ (dvd_pow_self (p : ℤ) hk.ne').mul_right m)
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) ?_
  rw [hrsm, unitPartChar_intCast_pow_mul (pow_one p).symm _ k hm, ← map_mul, ← Int.cast_mul,
    quadraticChar_intCast, h]

/-- (T3) If `r + s = 2^k m` with `k ≥ 2` and `sm ≡ 1 (mod 4)`, then `χ₄` is a `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_add_four (hrs : IsCoprime r s) (hs : s ≠ 0)
    {k : ℕ} {m : ℤ} (hk : 2 ≤ k) (hrsm : r + s = 2 ^ k * m) (h : s * m % 4 = 1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have hm : ¬((2 : ℕ) : ℤ) ∣ m := by rintro ⟨t, rfl⟩; lia
  refine hasCharPattern_neg_mulSingle_one_of_dvd_add (p := 2) hrs hs rfl two_ne_zero
    (hrsm ▸ (pow_dvd_pow 2 hk).mul_right m) (show ZMod.χ₄ (-1) = -1 by decide) ?_
  rw [(mod_cast hrsm : r + s = ((2 : ℕ) : ℤ) ^ k * m),
    unitPartChar_intCast_pow_mul (N := 4) (j := 2) rfl _ k hm, ← map_mul, ← Int.cast_mul,
    ZMod.χ₄_int_one_mod_four h]

/-- (T4) In the window `a < -1`, `c_3 < 0 < c_4`, with `v_q(r + s)` odd, `sgn · val_q` is a `τ`:
`(+, +, -, +, -, …) · (+, -, +, -, …) = (+, -, -, …)`. -/
theorem hasCharPattern_neg_mulSingle_one_of_window (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r < -s) (h₃ : cSeq ((r : ℚ) / s) 3 < 0) (h₄ : 0 < cSeq ((r : ℚ) / s) 4) {q : ℕ}
    [Fact q.Prime] (hq : (q : ℤ) ∣ r + s) (hv : valChar q ((r + s : ℤ) : ℚ) = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  have ha' : (r : ℚ) / s < -1 := (div_lt_iff₀ (mod_cast hs)).mpr (mod_cast (by lia : r < -1 * s))
  refine hasCharPattern_neg_mulSingle_one_of_mul_valChar hrs hs.ne' hq hv
    (signChar_apply_of_pos (by rw [cSeq_one]; linarith)) (fun j hj ↦ signChar_apply_of_neg ?_)
    fun j hj ↦ signChar_apply_of_pos ?_
  · exact (cSeq_mem_Icc_of_odd ha' h₃ h₄ (by lia) (odd_two_mul_add_one j)).2.trans_lt h₃
  · exact h₄.trans_le (cSeq_mem_Icc_of_even ha' h₃ h₄ (by lia) (even_two_mul j)).1

/-- (T4) In the window `a < -1`, `r w_3 < 0 < r w_4`, with `r + s ≠ ±□`, `a` has `τ`. -/
theorem hasCharPattern_neg_mulSingle_one_of_window' (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r < -s) (h₃ : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0)
    (h₄ : 0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) (h : ¬IsSquare (r + s))
    (h' : ¬IsSquare (-(r + s))) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
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
  exact hasCharPattern_neg_mulSingle_one_of_neg_one_lt
    ((lt_div_iff₀ hs').mpr (mod_cast (by lia : -1 * s < r)))
    (div_neg_of_neg_of_pos (mod_cast h₀) hs')

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
      (pow_one p).symm one_ne_zero hpd (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) h h'

/-- **Criteria for `τ`**: each of (T1)–(T4) gives a character that is `1` at `c_1` and `-1` at
all later terms. -/
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

/-! ### Criteria from divisibility -/

/-- A prime `p ≡ 3 (mod 4)` dividing `r ≠ 0` gives `φ₁` from `φ₀`: by (O5) or (T2), according to
the Jacobi symbol `(ms/p)` for `r = p^k m`, and `φ₀ τ = φ₁`. -/
theorem hasCharPattern_mulSingle_one_of_prime_dvd (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hr : r ≠ 0) {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hpr : (p : ℤ) ∣ r)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  obtain ⟨k, m, hk, hrm, hm⟩ := Int.exists_pow_mul_of_dvd Fact.out hr hpr
  have hp := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hps : ¬(p : ℤ) ∣ s := Int.Prime.not_dvd_of_isCoprime Fact.out hrs.symm hpr
  rcases jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp
    (hp.coprime_iff_not_dvd.mpr (hp.not_dvd_mul hm hps)).symm) with h | h
  · exact hasCharPattern_mulSingle_one_of_dvd_left hrs hs hp4 hk hrm hm h
  · exact hasCharPattern_mulSingle_of_neg_of_neg_mulSingle h₀
      (hasCharPattern_neg_mulSingle_one_of_dvd_left hrs hs hp4 hk hrm hm h)

/-- (O3) or (O4): a positive non-square `s` has a prime with odd exponent. -/
theorem negFirstCriterion_of_not_isSquare_right (hs : 0 ≤ s) (h : ¬IsSquare s) :
    NegFirstCriterion r s := by
  obtain ⟨p, k, m, hp, hk, hsm, hm⟩ := Int.exists_prime_pow_mul_of_not_isSquare hs h
  rcases eq_or_ne p 2 with rfl | hp2
  · exact .dvd_right_two k m (mod_cast hsm)
      (Int.not_even_iff_odd.mp fun he ↦ hm (mod_cast he.two_dvd)) (.inl hk)
  · exact .dvd_right p k m hp hp2 hk.pos hsm hm (.inl hk)

/-- (O5) or (T2): a prime `p ≡ 3 (mod 4)` dividing `r ≠ 0` and not `s`. -/
theorem negFirstCriterion_or_negTailCriterion_of_prime_dvd (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 3) (hpr : (p : ℤ) ∣ r) (hps : ¬(p : ℤ) ∣ s) :
    NegFirstCriterion r s ∨ NegTailCriterion r s := by
  obtain ⟨k, m, hk, hrm, hm⟩ := Int.exists_pow_mul_of_dvd hp hr hpr
  have hp' := Nat.prime_iff_prime_int.mp hp
  exact (jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp
    (hp'.coprime_iff_not_dvd.mpr (hp'.not_dvd_mul hm hps)).symm)).imp
    (.dvd_left p k m hp hp4 hk hrm hm) (.dvd_left p k m hp hp4 hk hrm hm)

/-- (O5) or (T2) at `2`: `4 ∣ r ≠ 0` with `s` odd. -/
theorem negFirstCriterion_or_negTailCriterion_of_four_dvd (hr : r ≠ 0) (h4 : 4 ∣ r) (hs : Odd s) :
    NegFirstCriterion r s ∨ NegTailCriterion r s := by
  obtain ⟨k, m, hk, hrm, hm⟩ := Int.exists_pow_mul_of_dvd Nat.prime_two hr (by push_cast; lia)
  push_cast at hrm hm
  have hk2 : 2 ≤ k := Nat.lt_of_le_of_ne hk fun h ↦ by subst h; lia
  exact (by lia [Int.odd_iff.mp hs, Int.mul_emod m s 2] : m * s % 4 = 1 ∨ m * s % 4 = 3).imp
    (.dvd_left_two k m hk2 hrm) (.dvd_left_two k m hk2 hrm)

/-- (T3) for `r + s ≠ ±□` divisible by `4`, or `> 0` and `≡ 3`, or `< 0` and `≡ 1 (mod 4)`. -/
theorem negTailCriterion_of_emod_four (h : ¬IsSquare (r + s)) (h' : ¬IsSquare (-(r + s)))
    (h4 : (r + s) % 4 = 0 ∨ 0 < r + s ∧ (r + s) % 4 = 3 ∨ r + s < 0 ∧ (r + s) % 4 = 1) :
    NegTailCriterion r s := by
  refine .not_isSquare_add h h' (h4.imp Int.dvd_of_emod_eq_zero fun h ↦ ?_)
  rcases h with ⟨h0, h3⟩ | ⟨h0, h1⟩
  · exact Int.exists_prime_dvd_of_emod_four_eq_three h0 h3
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_four_eq_three (x := -(r + s))
      (by lia) (by lia)
    exact ⟨p, hp, hp4, dvd_neg.mp hpd⟩

/-- For `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`), (Z1) holds, or (Z2) if `|r|` is a square:
`r = t²` gives `r ≡ 1` and `r + 2s ≡ 3 (mod 8)`, `r = -t²` gives `r ≡ 7` and `r + 2s ≡ 5`. -/
theorem negAllCriterion_of_modEq_four (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) : NegAllCriterion r s := by
  rw [Int.ModEq] at h4
  have hs2 := Int.odd_iff.mp hs
  by_cases hsq : IsSquare r ∨ IsSquare (-r)
  · obtain ⟨p, hp, hp8, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_three_or_five
      (x := r + 2 * s) <| by
        obtain ⟨t, ht⟩ | ⟨t, ht⟩ := hsq <;> lia [Int.sq_emod_eight_eq_one_of_odd (x := t)
          (Int.odd_iff.mpr (by lia [Int.sq_emod_four t]))]
    exact .dvd_add_two_mul p hp hp8 hpd
  · push Not at hsq
    exact .not_isSquare hsq.1 hsq.2

/-- **`a ≡ 1 mod 4` has `φ₀`**, for `a = r/s` with `s` odd and `r ≡ s (mod 4)`
(`QuadraticIterates.negAllCriterion_of_modEq_four`); it has `φ₁` by
`QuadraticIterates.hasCharPattern_mulSingle_one_of_modEq_four`. -/
theorem hasCharPattern_neg_one_of_modEq_four (hrs : IsCoprime r s) (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) :=
  hasCharPattern_neg_one_of_negAllCriterion hrs (by rintro rfl; simp at hs)
    (negAllCriterion_of_modEq_four hs h4)

end QuadraticIterates
