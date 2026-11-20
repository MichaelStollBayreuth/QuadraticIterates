/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.Algebra.Group.Subgroup.Ker`: `IsSquare` lives in `Group.Even`,
-- which the sibling does not import; a Mathlib PR would add that import there.
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Subgroup.Ker

import Mathlib.Algebra.Ring.Parity

/-!
# Squares and the range of `powMonoidHom 2`

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

theorem mem_mrange_powMonoidHom_two_iff {M : Type*} [CommMonoid M] (a : M) :
    a ∈ MonoidHom.mrange (powMonoidHom 2 : M →* M) ↔ IsSquare a := by
  simp [isSquare_iff_exists_sq, eq_comm]

theorem Units.mem_range_powMonoidHom_two_iff {M : Type*} [CommMonoid M] (u : Mˣ) :
    u ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range ↔ IsSquare (u : M) :=
  MonoidHom.mem_range.trans <| MonoidHom.mem_mrange.symm.trans <|
    (mem_mrange_powMonoidHom_two_iff u).trans Units.isSquare_coe_iff.symm
