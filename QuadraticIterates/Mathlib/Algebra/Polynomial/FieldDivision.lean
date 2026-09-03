module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Divisibility descends along composition

Over a field, `p ∘ r ∣ q ∘ r` is equivalent to `p ∣ q` for every nonconstant `r`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Divisibility descends along composition with a nonconstant polynomial: `p ∘ r ∣ q ∘ r` iff
`p ∣ q`. The remainder of `q` modulo `p` composed with `r` is divisible by `p ∘ r` but has
smaller degree, so it vanishes. -/
theorem comp_dvd_comp_iff {p q r : K[X]} (hr : 0 < r.natDegree) : p.comp r ∣ q.comp r ↔ p ∣ q := by
  have hcomp (s : K[X]) (hs : s ≠ 0) : s.comp r ≠ 0 := fun h ↦
    hr.ne' (by rw [((comp_eq_zero_iff.mp h).resolve_left hs).2, natDegree_C])
  refine ⟨fun h ↦ ?_, (_root_.map_dvd (compRingHom r) ·)⟩
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, zero_dvd_iff] at h
    exact zero_dvd_iff.mpr (not_imp_not.mp (hcomp q) h)
  have hmod : p.comp r ∣ (q % p).comp r := by
    rw [EuclideanDomain.mod_eq_sub_mul_div, sub_comp, mul_comp]
    exact dvd_sub h (dvd_mul_right _ _)
  refine EuclideanDomain.mod_eq_zero.mp (by_contra fun hne ↦ ?_)
  have h1 := natDegree_le_of_dvd hmod (hcomp _ hne)
  have h2 := natDegree_lt_natDegree hne (degree_mod_lt q hp)
  simp only [natDegree_comp] at h1
  exact absurd h1 ((Nat.mul_lt_mul_right hr).mpr h2).not_ge

end Polynomial
