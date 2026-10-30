/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Galois.Iterates

import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat
import QuadraticIterates.Sequence.Signs

/-!
# The sign pattern

For `a > 0` the signs of `c_1, c_2, …` are `(-, +, +, …)`, so the sign character realizes `φ₁`;
for `-1 < a < 0` they are `(+, -, -, …)`, the pattern `τ`.

## Main statements

* `QuadraticIterates.hasCharPattern_mulSingle_one_of_pos`: `φ₁` for `a > 0`.
* `QuadraticIterates.hasCharPattern_neg_mulSingle_one_of_neg_one_lt`: `τ` for `-1 < a < 0`.
-/

@[expose] public section

namespace QuadraticIterates

open Rat

theorem hasCharPattern_mulSingle_one_of_pos {a : ℚ} (ha : 0 < a) :
    HasCharPattern (cSeq a) 1 (Pi.mulSingle 1 (-1)) := by
  refine ⟨signChar, fun m hm ↦ ?_⟩
  rcases hm.eq_or_lt with rfl | hm
  · simp [signChar_apply_of_neg (neg_neg_of_pos ha)]
  · simp [signChar_apply_of_pos (cSeq_pos_of_pos ha hm), hm.ne']

theorem hasCharPattern_neg_mulSingle_one_of_neg_one_lt {a : ℚ} (h₁ : -1 < a) (h₀ : a < 0) :
    HasCharPattern (cSeq a) 1 (-Pi.mulSingle 1 (-1)) := by
  refine ⟨signChar, fun m hm ↦ ?_⟩
  rcases hm.eq_or_lt with rfl | hm
  · simp [signChar_apply_of_pos (neg_pos_of_neg h₀)]
  · simp [signChar_apply_of_neg (cSeq_neg_of_neg_one_lt h₁ h₀ hm), hm.ne']

end QuadraticIterates
