module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluation lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Evaluating the `L`-reduction of an integer polynomial at an integer point of an `L`-algebra
yields the cast of the integral value. -/
lemma Polynomial.aeval_intCast_map {L K : Type*} [CommRing L] [CommRing K] [Algebra L K]
    (p : Polynomial ℤ) (m : ℤ) :
    Polynomial.aeval (m : K) (p.map (Int.castRingHom L)) = ((p.eval m : ℤ) : K) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_intCast, Polynomial.eval_intCast_map]
  simp
