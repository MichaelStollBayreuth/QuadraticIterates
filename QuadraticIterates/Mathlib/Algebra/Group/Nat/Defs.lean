/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The exponents `2^n - 1`

`2^n - 1 = 2 (2^(n-1) - 1) + 1`, the identity between the exponents of consecutive terms of a
sequence `x^(2^n - 1)`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Nat

lemma two_pow_sub_one_eq {n : ℕ} (hn : 1 ≤ n) : 2 ^ n - 1 = 2 * (2 ^ (n - 1) - 1) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have := Nat.one_le_two_pow (n := m)
  rw [Nat.add_sub_cancel, pow_succ]
  lia

end Nat

end
