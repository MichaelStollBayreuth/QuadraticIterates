/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Galois.TwoIndependent
public import QuadraticIterates.Main.Criteria
public import QuadraticIterates.Main.TwoAdic

import QuadraticIterates.Main.LevelTwo
import QuadraticIterates.Main.Theorem
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Data.Nat.Factorization.Basic
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QuadraticIterates.Mathlib.RingTheory.Multiplicity

/-!
# The interval `α < a < -1`

For `α < a < -1` the main theorem `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`
applies with `ε = 1`. Once `c₁, c₂` are 2-independent, its lists of criteria for `φ₁` and `τ` can
be replaced by the shorter lists `QuadraticIterates.NegFirstCriterion'` and
`QuadraticIterates.NegTailCriterion'`: (O1), (T1) and (T4) do not apply there, for a square `s`
(O3) and (O4) take a simpler form, and (T3) needs no condition on squares, since `|r + s| = □`
forces (Z1) and (O3)/(O4). The list for `φ₀` is unchanged.

In the classes `(r, s) ≡ (1, 1)`, `(1, 3)`, `(3, 2) (mod 4)`, and in the parts of the classes
`(2, 1)`, `(0, 3)`, `(3, 0)` given by congruences modulo `32` and, for `(0, 3)`, by `|r|` not
being a square in `ℚ₂`, two of (Z), (O), (T) hold outright: there the arboreal representation of
`X² + a` is surjective with no further condition.

## Main definitions

* `QuadraticIterates.NegFirstCriterion'`, `QuadraticIterates.NegTailCriterion'`: the lists (O')
  and (T').

## Main statements

* `QuadraticIterates.negFirstCriterion_of_negFirstCriterion'`: (O') implies (O).
* `QuadraticIterates.negTailCriterion_of_negTailCriterion'`: (T') implies (T) when `-(r + s)` is
  not a square.
* `QuadraticIterates.nonempty_mulEquiv_of_lt_neg_one_of_criteria`: two of (Z), (O'), (T') give
  `Ω_n ≅ [C₂]ⁿ` for all `n`.
* `QuadraticIterates.nonempty_mulEquiv_of_lt_neg_one_of_emod`: the classes in which this holds
  outright.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- Criteria for `φ₁` (the pattern `(-1, 1, 1, …)`) for `a = r/s` with `α < a < -1`. -/
inductive NegFirstCriterion' (r s : ℤ) : Prop
  /-- `a ≡ 1 mod 4`: `s` is odd and `r ≡ s (mod 4)`. -/
  | modEq_four (hs : Odd s) (h : r ≡ s [ZMOD 4])
  /-- `s` is not a square. -/
  | not_isSquare_right (h : ¬IsSquare s)
  /-- `-r` is not a square modulo an odd prime `p ∣ s`. -/
  | dvd_right (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ s)
      (h : jacobiSym (-r) p = -1)
  /-- `16 ∣ s` and `r ≡ 3 (mod 8)`. -/
  | dvd_right_sixteen (h : 16 ∣ s) (hr : r % 8 = 3)
  /-- (O5) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = 1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = 1)

/-- Criteria for `τ` (the pattern `(1, -1, -1, …)`) for `a = r/s` with `α < a < -1`. -/
inductive NegTailCriterion' (r s : ℤ) : Prop
  /-- (T2) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- A prime `p ≡ 3 (mod 4)` divides `r + s`. -/
  | dvd_add (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hdvd : (p : ℤ) ∣ r + s)

/-- A positive square divisible by a prime `p` is `p^(2j) m²` with `j > 0` and `p ∤ m`. -/
private lemma exists_eq_pow_mul_sq_of_isSquare (hs : 0 < s) (hsq : IsSquare s) {p : ℕ}
    (hp : p.Prime) (h : (p : ℤ) ∣ s) :
    ∃ j : ℕ, ∃ m : ℤ, 0 < j ∧ s = p ^ (2 * j) * m ^ 2 ∧ ¬(p : ℤ) ∣ m := by
  obtain ⟨u, rfl⟩ := hsq
  rw [← sq] at h ⊢
  exact Int.exists_sq_eq_pow_mul_of_dvd hp (by rintro rfl; simp at hs)
    ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h)

/-- (O3) for a square `s = p^(2j) m²`: `(-rm² / p) = (-r / p)`. -/
private lemma negFirstCriterion_of_jacobiSym (hs : 0 < s) (hsq : IsSquare s) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ s) (h : jacobiSym (-r) p = -1) :
    NegFirstCriterion r s := by
  obtain ⟨j, m, hj, rfl, hm⟩ := exists_eq_pow_mul_sq_of_isSquare hs hsq hp hdvd
  refine .dvd_right p (2 * j) (m ^ 2) hp hp2 (by lia) rfl
    (fun h ↦ hm ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h)) (.inr ?_)
  rw [← neg_mul, jacobiSym.mul_left, h, jacobiSym.sq_one_of_not_dvd hp hm, mul_one]

/-- (O4) for a square `s = 2^(2j) m²` with `16 ∣ s` and `r ≡ 3 (mod 8)`: `j ≥ 2` and
`m² ≡ 1 (mod 8)`. -/
private lemma negFirstCriterion_of_sixteen_dvd (hs : 0 < s) (hsq : IsSquare s) (h16 : 16 ∣ s)
    (hr : r % 8 = 3) : NegFirstCriterion r s := by
  obtain ⟨j, m, hj, rfl, hm⟩ := exists_eq_pow_mul_sq_of_isSquare hs hsq Nat.prime_two
    (by push_cast; exact (by norm_num : (2 : ℤ) ∣ 16).trans h16)
  have hmo : Odd m := Int.odd_iff.mpr (by push_cast at hm; lia)
  have hm8 := Int.sq_emod_eight_eq_one_of_odd hmo
  have hj2 : 2 ≤ j := by
    by_contra
    obtain rfl : j = 1 := by lia
    norm_num at h16
    lia
  refine .dvd_right_two (2 * j) (m ^ 2) (by push_cast; rfl) hmo.pow
    (.inr (.inr ⟨even_two_mul j, by lia, ?_⟩))
  rw [Int.mul_emod, hr, hm8]
  decide

/-- (O') implies (O). -/
theorem negFirstCriterion_of_negFirstCriterion' (hs : 0 < s) (h : NegFirstCriterion' r s) :
    NegFirstCriterion r s := by
  have hO := negFirstCriterion_of_not_isSquare_right (r := r) hs.le
  cases h with
  | modEq_four hs' h => exact .modEq_four hs' h
  | not_isSquare_right h => exact hO h
  | dvd_right p hp hp2 hdvd h =>
    by_cases hsq : IsSquare s
    exacts [negFirstCriterion_of_jacobiSym hs hsq hp hp2 hdvd h, hO hsq]
  | dvd_right_sixteen h16 hr =>
    by_cases hsq : IsSquare s
    exacts [negFirstCriterion_of_sixteen_dvd hs hsq h16 hr, hO hsq]
  | dvd_left p k m hp hp4 hk hr hm h => exact .dvd_left p k m hp hp4 hk hr hm h

/-- (T') implies (T) when `r + s < 0` and `-(r + s)` is not a square. -/
theorem negTailCriterion_of_negTailCriterion' (hrs : r + s < 0) (h' : ¬IsSquare (-(r + s)))
    (h : NegTailCriterion' r s) : NegTailCriterion r s := by
  cases h with
  | dvd_left p k m hp hp4 hk hr hm h => exact .dvd_left p k m hp hp4 hk hr hm h
  | dvd_add p hp hp4 hdvd =>
    exact .not_isSquare_add (fun h ↦ hrs.not_ge h.nonneg) h' (.inr ⟨p, hp, hp4, hdvd⟩)

/-- **The interval** `α < a < -1`: for `a = r/s` in a `2`-adic class with `ε = 1` and `c₁, c₂`
2-independent, two of (Z), (O'), (T') give `Ω_n ≅ [C₂]ⁿ` for all `n`. If `|r + s|` is a square,
then `|r|` and `s` are not, which gives (Z1) and (O3)/(O4) directly. -/
theorem nonempty_mulEquiv_of_lt_neg_one_of_criteria (hrs : IsCoprime r s) (hs : 0 < s)
    (hr : r < -s) (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (hc : TwoAdicClass r s 1)
    (h2 : TwoIndependent fun i : Fin 2 ↦ cSeq ((r : ℚ) / s) ((i : ℕ) + 1))
    (h : NegAllCriterion r s ∧ NegFirstCriterion' r s ∨ NegAllCriterion r s ∧
      NegTailCriterion' r s ∨ NegFirstCriterion' r s ∧ NegTailCriterion' r s) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  obtain ⟨-, h₂, h₁₂⟩ := not_isSquare_of_twoIndependent h2
  refine nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs (.inr ⟨hα, rfl⟩) hc ?_ n
  by_cases hsq : IsSquare (-(r + s))
  · exact .inl ⟨.not_isSquare (fun h ↦ (by lia : r < 0).not_ge h.nonneg)
      fun h ↦ h₂ (neg_mul_neg r (r + s) ▸ h.mul hsq),
      negFirstCriterion_of_not_isSquare_right hs.le fun h ↦ h₁₂ (mul_neg s (r + s) ▸ h.mul hsq)⟩
  have hO := negFirstCriterion_of_negFirstCriterion' (r := r) hs
  have hT := negTailCriterion_of_negTailCriterion' (by lia) hsq
  rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  exacts [.inl ⟨h₀, hO h₁⟩, .inr (.inl ⟨h₀, hT h₁⟩), .inr (.inr ⟨hO h₀, hT h₁⟩)]

/-- In the classes `(1, 1)`, `(1, 3)` and `(3, 2)` modulo `4`, with `r < 0` and `r + s < 0`: (Z1)
and (O2) or (O3)/(O4), as `|r| ≡ 3 (mod 4)`; (O3)/(O4) and (T3), as `s ≡ 2` and
`|r + s| ≡ 3 (mod 4)`. -/
private lemma criteria_of_emod_four (hs : 0 < s) (hr : r < 0) (hrs : r + s < 0)
    (h : r % 4 = 1 ∧ s % 2 = 1 ∨ r % 4 = 3 ∧ s % 4 = 2) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hO := negFirstCriterion_of_not_isSquare_right (r := r) hs.le
  rcases h with ⟨hr4, hs2⟩ | ⟨hr4, hs4⟩
  · refine .inl ⟨.not_isSquare (fun h ↦ hr.not_ge h.nonneg)
      (Int.not_isSquare_of_two_le_emod_four (by lia)), ?_⟩
    rcases (by lia : s % 4 = 1 ∨ s % 4 = 3) with h | h
    exacts [.modEq_four (Int.odd_iff.mpr hs2) (by rw [Int.ModEq]; lia),
      hO (Int.not_isSquare_of_two_le_emod_four (by lia))]
  · exact .inr (.inr ⟨hO (Int.not_isSquare_of_two_le_emod_four (by lia)),
      negTailCriterion_of_emod_four (fun h ↦ hrs.not_ge h.nonneg)
        (Int.not_isSquare_of_two_le_emod_four (by lia)) (.inr (.inr ⟨hrs, by lia⟩))⟩)

/-- In the class `(2, 1)`: (Z1), as `|r| ≡ 2 (mod 4)`; and for `r ≡ 2 (mod 8)` (O5) or (T2) at a
prime `p ≡ 3 (mod 4)` dividing `|r|/2 ≡ 3 (mod 4)`, for `s ≡ 5 (mod 8)` (O3)/(O4). -/
private lemma criteria_of_emod_four_eq_two (hrs : IsCoprime r s) (hs : 0 < s) (hr : r < 0)
    (hr4 : r % 4 = 2) (h : r % 8 = 2 ∨ s % 8 = 5) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  have hZ : NegAllCriterion r s :=
    .not_isSquare (fun h ↦ hr.not_ge h.nonneg) (Int.not_isSquare_of_two_le_emod_four (by lia))
  rcases h with h | h
  · obtain ⟨p, hp, hp4, hpr⟩ := Int.exists_prime_dvd_of_emod_eight_eq_six (x := -r) (by lia)
      (by lia)
    rcases negFirstCriterion_or_negTailCriterion_of_prime_dvd hr.ne hp hp4 (dvd_neg.mp hpr)
      fun hps ↦ (Nat.prime_iff_prime_int.mp hp).not_isUnit (hrs.isUnit_of_dvd' (dvd_neg.mp hpr) hps)
      with h | h
    exacts [.inl ⟨hZ, h⟩, .inr (.inl ⟨hZ, h⟩)]
  · exact .inl ⟨hZ, negFirstCriterion_of_not_isSquare_right hs.le
      (Int.not_isSquare_of_emod_eight_eq_five h)⟩

/-- In the class `(0, 3)`: (O3)/(O4), as `s ≡ 3 (mod 4)`; and (Z1) if `|r|` is not a square in
`ℚ₂`, (Z2) at a prime `p ≡ ±3 (mod 8)` dividing `(r + 2s)/2 ≡ ±3 (mod 8)` if
`r + 2s ≡ ±6 (mod 16)`. -/
private lemma criteria_of_emod_four_eq_three (hs : 0 < s) (hr : r < 0) (h2 : 0 < r + 2 * s)
    (hs4 : s % 4 = 3) (h : (∀ j : ℕ, ∀ m : ℤ, -r = 4 ^ j * m → m % 8 ≠ 1) ∨
      (r + 2 * s) % 16 = 6 ∨ (r + 2 * s) % 16 = 10) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  refine .inl ⟨?_, negFirstCriterion_of_not_isSquare_right hs.le
    (Int.not_isSquare_of_two_le_emod_four (by lia))⟩
  rcases h with h | h
  · refine .not_isSquare (fun h ↦ hr.not_ge h.nonneg) fun hsq ↦ ?_
    obtain ⟨j, m, he, hm⟩ := Int.exists_eq_four_pow_mul_of_isSquare hsq (by lia)
    exact h j m he hm
  · obtain ⟨p, hp, hp8, hpd⟩ :=
      Int.exists_prime_dvd_of_emod_eight_eq_three_or_five (x := (r + 2 * s) / 2) (by lia) (by lia)
    exact .dvd_add_two_mul p hp hp8 (hpd.trans ⟨2, by lia⟩)

/-- In the class `(3, 0)` with `r ≡ 3 (mod 8)` and `s ≢ 4 (mod 32)`: (Z1), as `|r| ≡ 5 (mod 8)`;
and (O3)/(O4) if `s` is not a square, (O4) if `s = 4^j m` with `m ≡ 1 (mod 8)`, where `j ≥ 2`. -/
private lemma criteria_of_emod_eight_eq_three (hs : 0 < s) (hr : r < 0) (hr8 : r % 8 = 3)
    (hs4 : s % 4 = 0) (h32 : s % 32 ≠ 4) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  refine .inl ⟨.not_isSquare (fun h ↦ hr.not_ge h.nonneg)
    (Int.not_isSquare_of_emod_eight_eq_five (by lia)), ?_⟩
  by_cases hsq : IsSquare s
  swap
  · exact negFirstCriterion_of_not_isSquare_right hs.le hsq
  obtain ⟨j, m, rfl, hm⟩ := Int.exists_eq_four_pow_mul_of_isSquare hsq hs.ne'
  rcases j with _ | _ | j
  · lia
  · lia
  refine .dvd_right_two (2 * (j + 2)) m (by rw [pow_mul]; norm_num) (Int.odd_iff.mpr (by lia))
    (.inr (.inr ⟨even_two_mul _, by lia, ?_⟩))
  rw [Int.mul_emod, hr8, hm]
  decide

/-- The classes of the hypothesis of
`QuadraticIterates.nonempty_mulEquiv_of_lt_neg_one_of_emod` lie in `TwoAdicClass r s 1`. -/
private lemma twoAdicClass_one_of_emod
    (h : r % 4 = 1 ∧ s % 2 = 1 ∨ r % 4 = 3 ∧ s % 2 = 0 ∨ r % 4 = 2 ∧ s % 4 = 1 ∨
      r % 4 = 0 ∧ s % 4 = 3) :
    TwoAdicClass r s 1 := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inl ⟨Int.odd_iff.mpr h₂, by rw [Int.ModEq]; lia⟩
  · exact .inr (.inr ⟨Int.even_iff.mpr h₂, by rw [Int.ModEq]; lia⟩)
  all_goals exact .inr (.inl ⟨Int.odd_iff.mpr (by lia), by rw [Int.ModEq]; lia⟩)

/-- **Automatic classes on the interval** `α < a < -1`: for `a = r/s` in one of the following
classes, `Ω_n ≅ [C₂]ⁿ` for all `n`: `(r, s) ≡ (1, 1)`, `(1, 3)` or `(3, 2) (mod 4)`; `(2, 1)` with
`r ≡ 2` or `s ≡ 5 (mod 8)`; `(0, 3)` with `|r|` not a square in `ℚ₂` (not `4^j m` with
`m ≡ 1 (mod 8)`) or `r + 2s ≡ ±6 (mod 16)`; `(3, 0)` with `r ≡ 3 (mod 8)` and `s ≢ 4 (mod 32)`.
Two of (Z), (O), (T) then hold, so no condition on `c₁, c₂` is needed. -/
theorem nonempty_mulEquiv_of_lt_neg_one_of_emod (hrs : IsCoprime r s) (hs : 0 < s) (hr : r < -s)
    (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (h : r % 4 = 1 ∧ s % 2 = 1 ∨ r % 4 = 3 ∧ s % 4 = 2 ∨
      r % 4 = 2 ∧ s % 4 = 1 ∧ (r % 8 = 2 ∨ s % 8 = 5) ∨
      r % 4 = 0 ∧ s % 4 = 3 ∧ ((∀ j : ℕ, ∀ m : ℤ, -r = 4 ^ j * m → m % 8 ≠ 1) ∨
        (r + 2 * s) % 16 = 6 ∨ (r + 2 * s) % 16 = 10) ∨
      r % 8 = 3 ∧ s % 4 = 0 ∧ s % 32 ≠ 4) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  have h2 : 0 < r + 2 * s := by
    by_contra! h2
    linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) h2,
      mul_neg_of_pos_of_neg (pow_pos hs 2) (by lia : r + s < 0)]
  refine nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs (.inr ⟨hα, rfl⟩)
    (twoAdicClass_one_of_emod ?_) ?_ n
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩ <;> lia
  rcases h with h | h | ⟨h₁, -, h₃⟩ | ⟨-, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact criteria_of_emod_four hs (by lia) (by lia) (.inl h)
  · exact criteria_of_emod_four hs (by lia) (by lia) (.inr h)
  · exact criteria_of_emod_four_eq_two hrs hs (by lia) h₁ h₃
  · exact criteria_of_emod_four_eq_three hs (by lia) h2 h₂ h₃
  · exact criteria_of_emod_eight_eq_three hs (by lia) h₁ h₂ h₃

end QuadraticIterates
