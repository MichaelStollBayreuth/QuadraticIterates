/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.RingTheory.Multiplicity

/-!
# The `p`-part of an integer divisible by `p`

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Int

/-- An integer `r ≠ 0` divisible by a prime `p` is `p^k m` with `k > 0` and `p ∤ m`. -/
theorem exists_pow_mul_of_dvd {p : ℕ} (hp : p.Prime) {r : ℤ} (hr : r ≠ 0) (h : (p : ℤ) ∣ r) :
    ∃ k : ℕ, ∃ m : ℤ, 0 < k ∧ r = p ^ k * m ∧ ¬(p : ℤ) ∣ m := by
  obtain ⟨m, hm, hpm⟩ := (Int.finiteMultiplicity_iff (a := p) (b := r)).mpr
    ⟨by simpa using hp.one_lt.ne', hr⟩ |>.exists_eq_pow_mul_and_not_dvd
  refine ⟨_, m, Nat.pos_of_ne_zero fun h0 ↦ hpm ?_, hm, hpm⟩
  rw [h0, pow_zero, one_mul] at hm
  exact hm ▸ h

end Int
