module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Tactic.ToAdditive

/-!
# Products over a filtered finset, indexed by the finset as a type

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Finset

variable {ι M : Type*} [CommMonoid M]

/-- A product over the elements of `s` satisfying `p`, indexed by the type `↥s`, is the product
over `s.filter p`. -/
@[to_additive /-- A sum over the elements of `s` satisfying `p`, indexed by the type `↥s`, is the
sum over `s.filter p`. -/]
theorem prod_filter_coe_sort (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → M) :
    ∏ x : ↥s with p x.1, f x = ∏ x ∈ s with p x, f x := by
  rw [prod_filter, prod_filter, prod_coe_sort s fun x ↦ if p x then f x else 1]

end Finset
