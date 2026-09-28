/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# A quadratic on an interval

A quadratic with nonnegative leading coefficient is convex, hence bounded on an interval by its
values at the endpoints.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- A quadratic `a * (x * x) + b * x + c` with `0 ≤ a` is convex, so on an interval it is bounded
by its value at one of the endpoints. -/
theorem quadratic_le_max_of_nonneg_of_mem_Icc {a l u x : R} (ha : 0 ≤ a) (b c : R)
    (hx : x ∈ Set.Icc l u) :
    a * (x * x) + b * x + c ≤ max (a * (l * l) + b * l + c) (a * (u * u) + b * u + c) := by
  obtain ⟨hl, hu⟩ := hx
  rcases le_or_gt (a * (x + l) + b) 0 with h | h
  · refine le_max_of_le_left ?_
    linear_combination mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl) h
  · refine le_max_of_le_right ?_
    have h' : 0 ≤ a * (u + x) + b := by
      linear_combination h.le + mul_nonneg ha (sub_nonneg.2 (hl.trans hu))
    linear_combination mul_nonneg (sub_nonneg.2 hu) h'
