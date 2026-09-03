module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluation lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial in
/-- Evaluating the `L`-reduction of an integer polynomial at an integer point of an `L`-algebra
yields the cast of the integral value. -/
lemma Polynomial.aeval_intCast_map {L K : Type*} [CommRing L] [CommRing K] [Algebra L K]
    (p : ℤ[X]) (m : ℤ) : aeval (m : K) (p.map (Int.castRingHom L)) = ((p.eval m : ℤ) : K) := by
  rw [aeval_def, eval₂_at_intCast, eval_intCast_map]
  simp
