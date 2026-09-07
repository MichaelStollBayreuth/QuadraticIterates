/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.ToAdditive

/-!
# Products over a filtered finset, indexed by the finset as a type; sums of integer multiples

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

/-- `∑ i ∈ s, f i • x = (∑ i ∈ s, f i) • x` for integer multiples, the sibling of
`Finset.sum_nsmul_assoc`. -/
theorem sum_zsmul_assoc {A : Type*} [AddCommGroup A] (s : Finset ι) (f : ι → ℤ) (x : A) :
    ∑ i ∈ s, f i • x = (∑ i ∈ s, f i) • x :=
  (map_sum (zmultiplesHom A x) f s).symm

end Finset
