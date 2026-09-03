module

public import Mathlib.Algebra.Field.ZMod

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Big-operator lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Finset

/-- Factor a constant out of an indicator-weighted sum: `∑ g x · [p x]·c = c · ∑_{p x} g x`. -/
theorem sum_mul_ite_const {ι R : Type*} [CommSemiring R] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → R) (c : R) :
    ∑ x ∈ s, g x * (if p x then c else 0) = c * ∑ x ∈ s with p x, g x := by
  simp [mul_ite, sum_filter, mul_sum, mul_comm]

/-- An `𝔽₂`-linear combination is the sum over the support of the coefficient function. -/
theorem sum_zmod_two_smul_eq_sum_filter {ι M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {s : Finset ι} (m : ι → M) (g : ι → ZMod 2) :
    ∑ i ∈ s, g i • m i = ∑ i ∈ s with g i = 1, m i := by
  rw [sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases (show g i = 0 ∨ g i = 1 by generalize g i = z; revert z; decide) with h | h <;> simp [h]

end Finset
