module

public import Mathlib.Algebra.Polynomial.Roots

import Mathlib.Tactic.ToAdditive

/-!
# Root-set lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- For a polynomial without repeated roots in `E`, a product over the (coerced) `rootSet` equals
the corresponding multiset product over `aroots`. -/
@[to_additive /-- For a polynomial without repeated roots in `E`, a sum over the (coerced)
`rootSet` equals the corresponding multiset sum over `aroots`. -/]
lemma Polynomial.prod_rootSet_eq_prod_aroots {K E M : Type*} [CommRing K] [CommRing E]
    [IsDomain E] [Algebra K E] [CommMonoid M] {p : Polynomial K} (hnodup : (p.aroots E).Nodup)
    (f : E → M) : ∏ β : p.rootSet E, f β = ((p.aroots E).map f).prod := by
  classical
  rw [← Finset.prod_subtype (p.aroots E).toFinset
    (fun x ↦ by rw [Multiset.mem_toFinset, mem_aroots', mem_rootSet']) f,
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
