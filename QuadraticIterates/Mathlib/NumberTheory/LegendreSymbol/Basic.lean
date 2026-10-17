/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The quadratic character modulo `p` at `-1`

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace ZMod

theorem quadraticChar_neg_one_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr fun h ↦ exists_sq_eq_neg_one_iff.mp h hp

theorem quadraticChar_neg_one_of_mod_four_eq_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    quadraticChar (ZMod p) (-1) = 1 :=
  (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (exists_sq_eq_neg_one_iff.mpr (by lia))

end ZMod
