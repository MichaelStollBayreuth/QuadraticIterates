/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Radical.NatInt

/-!
# The radical of a natural number

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open UniqueFactorizationMonoid

/-- A natural number is squarefree if and only if it is its own radical. -/
theorem Nat.squarefree_iff_radical_eq_self {n : ℕ} : Squarefree n ↔ radical n = n :=
  ⟨fun hsf ↦ associated_iff_eq.mp (radical_associated hsf.isRadical hsf.ne_zero),
    fun h ↦ h ▸ squarefree_radical⟩

/-- If `n ≠ 0` is not squarefree, then `n / rad n ≥ 2`. -/
theorem Nat.two_le_div_radical_of_not_squarefree {n : ℕ} (hn : n ≠ 0) (h : ¬Squarefree n) :
    2 ≤ n / radical n := by
  by_contra! hlt
  have hd := Nat.div_mul_cancel (radical_dvd_self (a := n))
  have h1 : n / radical n = 1 :=
    le_antisymm (by lia) ((Nat.one_le_div_iff (Nat.radical_pos n)).mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) radical_dvd_self))
  rw [h1, one_mul] at hd
  exact h (Nat.squarefree_iff_radical_eq_self.mpr hd)

/-- For `n ≠ 0`, the cofactor `n / rad n` is even if and only if `4 ∣ n`. -/
theorem Nat.even_div_radical_iff_four_dvd {n : ℕ} (hn : n ≠ 0) :
    Even (n / radical n) ↔ 4 ∣ n := by
  have hmul := Nat.div_mul_cancel (radical_dvd_self (a := n))
  refine ⟨fun ⟨j, hj⟩ ↦ ?_, fun h4 ↦ ?_⟩
  · obtain ⟨r, hr⟩ : 2 ∣ radical n := (dvd_radical_iff Nat.prime_two.squarefree.isRadical hn).mpr
      ⟨j * radical n, hmul.symm.trans (by rw [hj]; ring)⟩
    exact ⟨j * r, hmul.symm.trans (by rw [hj, hr]; ring)⟩
  · rcases Nat.even_or_odd (n / radical n) with h | h
    · exact h
    · have h4' : 2 ^ 2 ∣ radical n :=
        ((Nat.coprime_two_right.mpr h).pow_right 2).symm.dvd_of_dvd_mul_left
          (by rw [hmul]; exact h4)
      exact absurd (Nat.isUnit_iff.mp (squarefree_radical (a := n) 2 (by simpa [sq] using h4')))
        (by decide)
