/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Galois.Iterates

import QuadraticIterates.Main.LevelTwo
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity

/-!
# Integer parameters

For `a ∈ ℤ`, that is `s = 1`, the square class `c₂ ∼ a(a + 1)` is never trivial
(`Int.not_isSquare_mul_add_one`), so for `a > 0` or `a ≤ -2` in a `2`-adic class the level-two
criterion `QuadraticIterates.forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass` says that
the arboreal representation of `X² + a` is surjective if and only if neither `-a` nor `-a - 1` is a
square. The classes are `a ≡ 1, 2 mod 4` with `a > 0` and `a ≡ 0, 3 mod 4` with `a ≤ -2`; in the
first three, `-a - 1` is negative or `≡ 3 mod 4`. This contains the main result of Section 3 of
[Stoll 1992] and Theorem 3.5 of [Li 2020].

## Main statements

* `QuadraticIterates.nonempty_mulEquiv_of_pos_of_emod_four_eq_one`,
  `QuadraticIterates.nonempty_mulEquiv_of_pos_of_emod_four_eq_two`,
  `QuadraticIterates.nonempty_mulEquiv_of_neg_of_emod_four_eq_zero` and
  `QuadraticIterates.nonempty_mulEquiv_of_neg_of_emod_four_eq_three`: the four classes.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three`: Theorem 3.5 of
  [Li 2020], the last class with its converse.

## References

* [M. Stoll, *Galois groups over ℚ of some iterated polynomials*, Arch. Math. 59 (1992)]
* [H.-C. Li, Arch. Math. 114 (2020), 265-269]
-/

@[expose] public section

namespace QuadraticIterates

variable {a : ℤ}

/-- The level-two criterion at `s = 1`: as `c₂ ∼ a(a + 1)` is not a square, only `c₁ ∼ -a` and
`c₁ c₂ ∼ -a - 1` remain. -/
private lemma forall_nonempty_mulEquiv_intCast_iff_of_twoAdicClass {ε : ℤ}
    (ha : a ≤ -2 ∧ ε = -1 ∨ 0 < a ∧ ε = 1) (hc : TwoAdicClass a 1 ε) :
    (∀ n, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔
      ¬IsSquare (-a) ∧ ¬IsSquare (-a - 1) := by
  have h := forall_nonempty_mulEquiv_iff_not_isSquare_of_twoAdicClass isCoprime_one_right one_pos
    (ha.imp (fun ⟨h, hε⟩ ↦ ⟨by lia, hε⟩) fun ⟨h, hε⟩ ↦ ⟨.inl (by lia), hε⟩) hc
  rw [Int.cast_one, div_one] at h
  simp only [mul_one, one_mul, neg_add'] at h
  refine h.trans (and_congr_right fun _ ↦ and_iff_right (Int.not_isSquare_mul_add_one ?_ ?_)) <;>
    lia

/-- For `a > 0` with `a ≡ 1 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`: the class (C1), and `-a`, `-a - 1`
are negative. This is case a) of the main result of Section 3 of [Stoll 1992]. -/
theorem nonempty_mulEquiv_of_pos_of_emod_four_eq_one (ha : 0 < a) (ha4 : a % 4 = 1) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_intCast_iff_of_twoAdicClass (.inr ⟨ha, rfl⟩)
    (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩)).mpr
    ⟨not_isSquare_of_neg (by lia), not_isSquare_of_neg (by lia)⟩ n

/-- For `a > 0` with `a ≡ 2 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`: the class (C2), and `-a`, `-a - 1`
are negative. This is case b) of the main result of Section 3 of [Stoll 1992]. -/
theorem nonempty_mulEquiv_of_pos_of_emod_four_eq_two (ha : 0 < a) (ha4 : a % 4 = 2) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_intCast_iff_of_twoAdicClass (.inr ⟨ha, rfl⟩)
    (.inr (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩))).mpr
    ⟨not_isSquare_of_neg (by lia), not_isSquare_of_neg (by lia)⟩ n

/-- For `a < 0` with `a ≡ 0 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ` for all `n`: the class
(C2), and `-a - 1 ≡ 3 mod 4`. This is case c) of the main result of Section 3 of [Stoll 1992]. -/
theorem nonempty_mulEquiv_of_neg_of_emod_four_eq_zero (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_intCast_iff_of_twoAdicClass (.inl ⟨by lia, rfl⟩)
    (.inr (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩))).mpr
    ⟨hsq, Int.not_isSquare_of_two_le_emod_four (by lia)⟩ n

/-- **Theorem 3.5 of [Li 2020]**: for `a < 0` with `a ≡ 3 mod 4` and `-a` not a square, the
arboreal representation of `X² + a` is surjective if and only if `-a - 1` is not a square; the
class (C1), with `a ≤ -2` as `a = -1` has `-a = 1`. -/
theorem forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) := by
  have ha2 : a ≤ -2 := by_contra fun _ ↦ hsq ⟨1, by lia⟩
  exact (forall_nonempty_mulEquiv_intCast_iff_of_twoAdicClass (.inl ⟨ha2, rfl⟩)
    (.inl ⟨odd_one, by rw [Int.ModEq]; lia⟩)).trans (and_iff_right hsq)

/-- For `a < 0` with `a ≡ 3 mod 4` and neither `-a` nor `-a - 1` a square, `Ω_n ≅ [C₂]ⁿ` for all
`n`. -/
theorem nonempty_mulEquiv_of_neg_of_emod_four_eq_three (ha : a < 0) (ha4 : a % 4 = 3)
    (h₁ : ¬IsSquare (-a)) (h₂ : ¬IsSquare (-a - 1)) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  (forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three ha ha4 h₁).mpr h₂ n

end QuadraticIterates
