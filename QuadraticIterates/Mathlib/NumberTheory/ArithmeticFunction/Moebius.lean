/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import Mathlib.Data.ZMod.Basic

/-!
# The Möbius function modulo `2`

`μ(d) ≡ [d squarefree] (mod 2)`, and every `n ≠ 1` has an even number of squarefree divisors.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace ArithmeticFunction

open Finset
open scoped ArithmeticFunction.Moebius

/-- `μ(d) ≡ [d squarefree] (mod 2)`. -/
theorem intCast_moebius_zmod_two (d : ℕ) :
    ((μ d : ℤ) : ZMod 2) = if Squarefree d then 1 else 0 := by
  split_ifs with h
  · rw [moebius_apply_of_squarefree h]
    push_cast
    simp [show (-1 : ZMod 2) = 1 from rfl]
  · simp [moebius_eq_zero_of_not_squarefree h]

/-- An integer `n ≠ 1` has an even number of squarefree divisors: modulo `2`, their number is
`Σ_{d ∣ n} μ(d) = 0`. -/
theorem even_card_filter_squarefree_divisors {n : ℕ} (hn : n ≠ 1) :
    Even #{d ∈ n.divisors | Squarefree d} := by
  rw [← ZMod.natCast_eq_zero_iff_even, card_filter, Nat.cast_sum]
  have h := congr(($(moebius_mul_coe_zeta) n : ZMod 2))
  rw [coe_mul_zeta_apply, one_apply, ite_eq_right hn, Int.cast_sum, Int.cast_zero] at h
  simpa [intCast_moebius_zmod_two] using h

end ArithmeticFunction
