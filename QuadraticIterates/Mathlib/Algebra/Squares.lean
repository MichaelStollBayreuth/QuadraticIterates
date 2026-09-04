module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.Int.Basic

/-!
# Lemmas about squares

Criteria for (non-)squareness in `ℚ`, `ℤ` and `ZMod m`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- If `P ≡ -Q mod m` with `Q` a unit mod `m` and `P/Q` a rational square, then `-1` is a
square mod `m`. -/
theorem ZMod.isSquare_neg_one_of_isSquare_div {P Q : ℤ} {m : ℕ}
    (hPnegQ : (P : ZMod m) = -(Q : ZMod m)) (hQunit : IsUnit (Q : ZMod m))
    (hsq : IsSquare ((P : ℚ) / (Q : ℚ))) : IsSquare (-1 : ZMod m) := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · rw [Int.cast_zero, isUnit_zero_iff] at hQunit
    exact ⟨0, by rw [← hQunit]; ring⟩
  have hPQ : IsSquare ((P * Q : ℤ) : ZMod m) := by
    have hQ : (Q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hQ0
    refine (Rat.isSquare_intCast_iff.mp ?_).map (Int.castRingHom (ZMod m))
    rw [show ((P * Q : ℤ) : ℚ) = (P : ℚ) / Q * Q ^ 2 by
      push_cast; rw [sq, ← mul_assoc, div_mul_cancel₀ _ hQ]]
    exact hsq.mul (IsSquare.sq _)
  obtain ⟨u, hu⟩ := hQunit
  have key : (-1 : ZMod m) = ((P * Q : ℤ) : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) * (u⁻¹ : (ZMod m)ˣ)) := by
    push_cast
    rw [hPnegQ, ← hu, mul_mul_mul_comm, neg_mul, Units.mul_inv, mul_one]
  rw [key]
  exact hPQ.mul (IsSquare.mul_self _)

/-- A sum of two squares is never congruent to `3` modulo `4`, a square being `0` or `1`. -/
theorem Nat.not_sq_add_sq_modEq_three (x y : ℕ) : ¬x ^ 2 + y ^ 2 ≡ 3 [MOD 4] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  generalize (x : ZMod 4) = a, (y : ZMod 4) = b
  decide +revert

/-- If `d ∣ m` with `d ≡ 3 mod 4`, then `-1` is not a square in `ZMod m`. -/
theorem ZMod.not_isSquare_neg_one_of_dvd {m d : ℕ} (hdm : d ∣ m) (hd : d % 4 = 3) :
    ¬IsSquare (-1 : ZMod m) := by
  intro hsq
  obtain ⟨x, y, rfl⟩ :=
    Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hdm hsq)
  exact Nat.not_sq_add_sq_modEq_three x y hd

/-- If `m ≡ 3 mod 4`, then `-1` is not a square in `ZMod m`. -/
theorem ZMod.not_isSquare_neg_one_of_emod_four_eq_three {m : ℕ} (hm : m % 4 = 3) :
    ¬IsSquare (-1 : ZMod m) :=
  not_isSquare_neg_one_of_dvd dvd_rfl hm

/-- If `m ≡ 6 mod 8`, then `-1` is not a square in `ZMod m`, as `m / 2 ≡ 3 mod 4` divides `m`. -/
theorem ZMod.not_isSquare_neg_one_of_emod_eight_eq_six {m : ℕ} (hm : m % 8 = 6) :
    ¬IsSquare (-1 : ZMod m) :=
  not_isSquare_neg_one_of_dvd (Nat.div_dvd_of_dvd (show 2 ∣ m by omega)) (by omega)

/-- If `4 ∣ m`, then `-1` is not a square in `ZMod m`. -/
theorem ZMod.not_isSquare_neg_one_of_four_dvd {m : ℕ} (hm : 4 ∣ m) : ¬IsSquare (-1 : ZMod m) :=
  fun hsq ↦ absurd (ZMod.isSquare_neg_one_of_dvd hm hsq) (by decide)

/-- An integer strictly between the consecutive squares `e ^ 2` and `(e + 1) ^ 2` is not a
square. -/
theorem Int.not_isSquare_of_sq_lt_of_lt_sq (e : ℤ) {m : ℤ} (h1 : e ^ 2 < m)
    (h2 : m < (e + 1) ^ 2) :
    ¬IsSquare m := by
  rintro ⟨r, rfl⟩
  rw [← sq] at h1 h2
  have h1' := sq_lt_sq.mp h1
  have h2' := (sq_lt_sq.mp h2).trans_le (by simpa using abs_add_le e 1)
  lia

/-- `|x|` is a square iff `x` or `-x` is. -/
theorem isSquare_abs_iff {α : Type*} [Ring α] [LinearOrder α] [IsOrderedRing α] {x : α} :
    IsSquare |x| ↔ IsSquare x ∨ IsSquare (-x) :=
  ⟨fun h ↦ (abs_choice x).imp (fun e ↦ (congrArg IsSquare e).mp h)
      fun e ↦ (congrArg IsSquare e).mp h,
    fun h ↦ h.elim (fun h ↦ (congrArg IsSquare (abs_of_nonneg h.nonneg)).mpr h) fun h ↦
      (congrArg IsSquare (abs_of_nonpos (neg_nonneg.mp h.nonneg))).mpr h⟩

open Function in
/-- If a family `f` is pairwise coprime on a finite set `S` and `∏_{i ∈ S} f i` is a square, then
`|f i|` is a square for every `i ∈ S`. -/
theorem Int.isSquare_abs_of_isSquare_prod_of_pairwise_isCoprime {ι : Type*} {f : ι → ℤ}
    {S : Finset ι} (hcop : (S : Set ι).Pairwise (IsCoprime on f)) (hsq : IsSquare (∏ i ∈ S, f i))
    {i : ι} (hi : i ∈ S) : IsSquare |f i| := by
  classical
  have hcopb : IsCoprime (f i) (∏ j ∈ S.erase i, f j) := IsCoprime.prod_right fun j hj ↦
    hcop hi (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨a0, ha0⟩ := Int.sq_of_isCoprime hcopb (by rw [Finset.mul_prod_erase S f hi, hc, sq])
  refine ⟨|a0|, ?_⟩
  rcases ha0 with h | h <;> simpa [sq, abs_mul, abs_neg] using congrArg abs h

