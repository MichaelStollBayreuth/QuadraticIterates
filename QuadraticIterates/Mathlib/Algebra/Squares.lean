/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.Int.Basic

/-!
# Lemmas about squares

Criteria for (non-)squareness in `ℚ`, `ℤ` and `ZMod m`; a rational square `P/Q` with `P y ≡ x Q`
modulo `m` makes `x y` a square modulo `m` (`ZMod.isSquare_mul_of_isSquare_div`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

theorem IsUnit.isSquare_mul_sq_iff {α : Type*} [CommMonoid α] {y : α} (hy : IsUnit y) (x : α) :
    IsSquare (x * y ^ 2) ↔ IsSquare x :=
  ⟨fun h ↦ by simpa [mul_assoc, ← mul_pow, hy.mul_val_inv] using h.mul (IsSquare.sq ↑hy.unit⁻¹),
    fun h ↦ h.mul (IsSquare.sq y)⟩

theorem IsUnit.isSquare_mul_pow_iff_of_even {α : Type*} [CommMonoid α] {y : α} (hy : IsUnit y)
    {n : ℕ} (hn : Even n) (x : α) : IsSquare (x * y ^ n) ↔ IsSquare x := by
  obtain ⟨j, rfl⟩ := hn
  rw [← two_mul, pow_mul', (hy.pow j).isSquare_mul_sq_iff]

theorem IsUnit.isSquare_mul_pow_iff_of_odd {α : Type*} [CommMonoid α] {y : α} (hy : IsUnit y)
    {n : ℕ} (hn : Odd n) (x : α) : IsSquare (x * y ^ n) ↔ IsSquare (x * y) := by
  obtain ⟨j, rfl⟩ := hn
  rw [pow_succ', mul_left_comm, ← mul_assoc, pow_mul', (hy.pow j).isSquare_mul_sq_iff,
    mul_comm y x]

theorem IsUnit.isSquare_pow_iff_of_odd {α : Type*} [CommMonoid α] {y : α} (hy : IsUnit y) {n : ℕ}
    (hn : Odd n) : IsSquare (y ^ n) ↔ IsSquare y := by
  simpa using hy.isSquare_mul_pow_iff_of_odd hn 1

/-- If `P/Q` is a rational square, then the integer `P Q = (P/Q) Q²` is a square. -/
theorem Int.isSquare_mul_of_isSquare_div {P Q : ℤ} (hsq : IsSquare ((P : ℚ) / Q)) :
    IsSquare (P * Q) := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  · rw [← Rat.isSquare_intCast_iff, show ((P * Q : ℤ) : ℚ) = (P : ℚ) / Q * Q ^ 2 by
      push_cast; rw [sq, ← mul_assoc, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr hQ)]]
    exact hsq.mul (IsSquare.sq _)

/-- If `P y ≡ x Q mod m` with `Q` a unit mod `m` and `P/Q` a rational square, then `x y` is a
square mod `m`: `x y = P Q (y / Q)²`. -/
theorem ZMod.isSquare_mul_of_isSquare_div {P Q : ℤ} {m : ℕ} {x y : ZMod m}
    (hPQ : (P : ZMod m) * y = x * Q) (hQunit : IsUnit (Q : ZMod m))
    (hsq : IsSquare ((P : ℚ) / (Q : ℚ))) : IsSquare (x * y) := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · rw [Int.cast_zero, isUnit_zero_iff] at hQunit
    have := subsingleton_of_zero_eq_one hQunit
    exact ⟨0, Subsingleton.elim _ _⟩
  have hPQsq : IsSquare ((P * Q : ℤ) : ZMod m) :=
    (Int.isSquare_mul_of_isSquare_div hsq).map (Int.castRingHom (ZMod m))
  obtain ⟨v, hv⟩ := hQunit
  have key : x * y = ((P * Q : ℤ) : ZMod m) * ((y * ↑v⁻¹) * (y * ↑v⁻¹)) := by
    push_cast
    rw [← hv, ← Units.mul_inv_cancel_right x v, hv, ← hPQ, ← hv]
    linear_combination (-(P : ZMod m) * y * y * ↑v⁻¹) * Units.mul_inv v
  exact key ▸ hPQsq.mul (IsSquare.mul_self _)

/-- If `P ≡ -Q mod m` with `Q` a unit mod `m` and `P/Q` a rational square, then `-1` is a
square mod `m`. -/
theorem ZMod.isSquare_neg_one_of_isSquare_div {P Q : ℤ} {m : ℕ}
    (hPnegQ : (P : ZMod m) = -(Q : ZMod m)) (hQunit : IsUnit (Q : ZMod m))
    (hsq : IsSquare ((P : ℚ) / (Q : ℚ))) : IsSquare (-1 : ZMod m) := by
  simpa using isSquare_mul_of_isSquare_div (y := 1) (by rw [mul_one, hPnegQ, neg_one_mul])
    hQunit hsq

/-- A sum of two squares is never congruent to `3` modulo `4`, a square being `0` or `1`. -/
theorem Nat.not_sq_add_sq_modEq_three (x y : ℕ) : ¬x ^ 2 + y ^ 2 ≡ 3 [MOD 4] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  generalize (x : ZMod 4) = a, (y : ZMod 4) = b
  decide +revert

theorem ZMod.not_isSquare_neg_one_of_dvd {m d : ℕ} (hdm : d ∣ m) (hd : d % 4 = 3) :
    ¬IsSquare (-1 : ZMod m) := by
  intro hsq
  obtain ⟨x, y, rfl⟩ :=
    Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hdm hsq)
  exact Nat.not_sq_add_sq_modEq_three x y hd

theorem ZMod.not_isSquare_neg_one_of_emod_four_eq_three {m : ℕ} (hm : m % 4 = 3) :
    ¬IsSquare (-1 : ZMod m) :=
  not_isSquare_neg_one_of_dvd dvd_rfl hm

/-- If `m ≡ 6 mod 8`, then `-1` is not a square in `ZMod m`, as `m / 2 ≡ 3 mod 4` divides `m`. -/
theorem ZMod.not_isSquare_neg_one_of_emod_eight_eq_six {m : ℕ} (hm : m % 8 = 6) :
    ¬IsSquare (-1 : ZMod m) :=
  not_isSquare_neg_one_of_dvd (Nat.div_dvd_of_dvd (show 2 ∣ m by lia)) (by lia)

theorem ZMod.not_isSquare_neg_one_of_four_dvd {m : ℕ} (hm : 4 ∣ m) : ¬IsSquare (-1 : ZMod m) :=
  fun hsq ↦ absurd (ZMod.isSquare_neg_one_of_dvd hm hsq) (by decide)

/-- An odd integer `≢ 1 mod 8` is not a square modulo `8`. -/
theorem ZMod.not_isSquare_intCast_eight_of_odd_of_emod_ne_one {x : ℤ} (hx : Odd x)
    (h1 : x % 8 ≠ 1) : ¬IsSquare (x : ZMod 8) := by
  have hx := Int.odd_iff.mp hx
  rcases (show x % 8 = 3 % 8 ∨ x % 8 = 5 % 8 ∨ x % 8 = 7 % 8 by lia) with h | h | h <;>
    rw [(intCast_eq_intCast_iff' x _ 8).mpr h] <;> decide

/-- The residue of `|N|` modulo `m` is that of `N`, for `N ≥ 0`. -/
theorem Int.natAbs_mod_eq_of_emod_eq {N : ℤ} (hN : 0 ≤ N) {m k : ℕ} (h : N % m = k) :
    N.natAbs % m = k :=
  Nat.cast_injective (R := ℤ) (by rw [Int.natCast_mod, Int.natAbs_of_nonneg hN]; exact_mod_cast h)

/-- For `N ≥ 0` with `N ≡ 6 mod 8`, `-1` is not a square modulo `N`. -/
theorem Int.not_isSquare_neg_one_zmod_natAbs_of_emod_eight_eq_six {N : ℤ} (hN : 0 ≤ N)
    (h : N % 8 = 6) : ¬IsSquare (-1 : ZMod N.natAbs) :=
  ZMod.not_isSquare_neg_one_of_emod_eight_eq_six (Int.natAbs_mod_eq_of_emod_eq hN h)

/-- For `N ≥ 0` with `N ≡ 3 mod 4`, `-1` is not a square modulo `N`. -/
theorem Int.not_isSquare_neg_one_zmod_natAbs_of_emod_four_eq_three {N : ℤ} (hN : 0 ≤ N)
    (h : N % 4 = 3) : ¬IsSquare (-1 : ZMod N.natAbs) :=
  ZMod.not_isSquare_neg_one_of_emod_four_eq_three (Int.natAbs_mod_eq_of_emod_eq hN h)

/-- A square is `0` or `1` modulo `4`. -/
theorem Int.emod_four_eq_zero_or_one_of_isSquare {m : ℤ} (h : IsSquare m) :
    m % 4 = 0 ∨ m % 4 = 1 := by
  obtain ⟨r, rfl⟩ := h
  rw [Int.mul_emod]
  rcases (show r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 by lia) with h | h | h | h <;>
    rw [h] <;> decide

/-- The `IsSquare` form of Mathlib's `Int.sq_ne_two_mod_four`. -/
theorem Int.not_isSquare_of_emod_four_eq_two {m : ℤ} (h : m % 4 = 2) : ¬IsSquare m :=
  fun hs ↦ by have := emod_four_eq_zero_or_one_of_isSquare hs; lia

theorem Int.not_isSquare_of_emod_four_eq_three {m : ℤ} (h : m % 4 = 3) : ¬IsSquare m :=
  fun hs ↦ by have := emod_four_eq_zero_or_one_of_isSquare hs; lia

theorem Int.not_isSquare_of_sq_lt_of_lt_sq (e : ℤ) {m : ℤ} (h1 : e ^ 2 < m)
    (h2 : m < (e + 1) ^ 2) :
    ¬IsSquare m := by
  rintro ⟨r, rfl⟩
  rw [← sq] at h1 h2
  have h1' := sq_lt_sq.mp h1
  have h2' := (sq_lt_sq.mp h2).trans_le (by simpa using abs_add_le e 1)
  lia

theorem isSquare_abs_iff {α : Type*} [Ring α] [LinearOrder α] [IsOrderedRing α] {x : α} :
    IsSquare |x| ↔ IsSquare x ∨ IsSquare (-x) :=
  ⟨fun h ↦ (abs_choice x).imp (fun e ↦ (congrArg IsSquare e).mp h)
      fun e ↦ (congrArg IsSquare e).mp h,
    fun h ↦ h.elim (fun h ↦ (congrArg IsSquare (abs_of_nonneg h.nonneg)).mpr h) fun h ↦
      (congrArg IsSquare (abs_of_nonpos (neg_nonneg.mp h.nonneg))).mpr h⟩

theorem Int.isSquare_abs_of_isSquare_mul_of_isCoprime {a b : ℤ} (h : IsCoprime a b)
    (hsq : IsSquare (a * b)) : IsSquare |a| := by
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨a0, ha0⟩ := Int.sq_of_isCoprime h (hc.trans (sq c).symm)
  refine ⟨|a0|, ?_⟩
  rcases ha0 with h | h <;> simpa [sq, abs_mul, abs_neg] using congrArg abs h

open Function in
/-- For a pairwise coprime family `f` on `S` and `u` coprime to every `f i`, `i ∈ S`: if
`u ∏_{i ∈ S} f i` is a square, then so is every `|f i|`, `i ∈ S`. -/
theorem Int.isSquare_abs_of_isSquare_mul_prod_of_pairwise_isCoprime {ι : Type*} {f : ι → ℤ}
    {S : Finset ι} {u : ℤ} (hcop : (S : Set ι).Pairwise (IsCoprime on f))
    (hu : ∀ i ∈ S, IsCoprime (f i) u) (hsq : IsSquare (u * ∏ i ∈ S, f i)) {i : ι} (hi : i ∈ S) :
    IsSquare |f i| := by
  classical
  refine isSquare_abs_of_isSquare_mul_of_isCoprime ((hu i hi).mul_right (IsCoprime.prod_right
    fun j hj ↦ hcop hi (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm)) ?_
  rwa [mul_left_comm, Finset.mul_prod_erase S f hi]

open Function in
/-- If a family `f` is pairwise coprime on a finite set `S` and `∏_{i ∈ S} f i` is a square, then
`|f i|` is a square for every `i ∈ S`. -/
theorem Int.isSquare_abs_of_isSquare_prod_of_pairwise_isCoprime {ι : Type*} {f : ι → ℤ}
    {S : Finset ι} (hcop : (S : Set ι).Pairwise (IsCoprime on f)) (hsq : IsSquare (∏ i ∈ S, f i))
    {i : ι} (hi : i ∈ S) : IsSquare |f i| :=
  isSquare_abs_of_isSquare_mul_prod_of_pairwise_isCoprime hcop (fun _ _ ↦ isCoprime_one_right)
    (by rwa [one_mul]) hi

