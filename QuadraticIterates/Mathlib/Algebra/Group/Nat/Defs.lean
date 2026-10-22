/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Mathlib.Algebra.Group.Nat.Defs

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
  lia [Nat.one_le_two_pow (n := n - 1), pow_succ 2 (n - 1), Nat.sub_add_cancel hn]

end Nat

end
