/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Powers with a shifted exponent

`x^(n-1) = x · x^(n-2)` for `n ≥ 2`, the sibling of `mul_pow_sub_one`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- `x^(n-1) = x · x^(n-2)` for `n ≥ 2`. -/
lemma pow_sub_one_eq_mul_pow_sub_two {M : Type*} [Monoid M] (x : M) {n : ℕ} (hn : 2 ≤ n) :
    x ^ (n - 1) = x * x ^ (n - 2) := by
  rw [← mul_pow_sub_one (by lia : n - 1 ≠ 0) x, Nat.sub_sub]

end
