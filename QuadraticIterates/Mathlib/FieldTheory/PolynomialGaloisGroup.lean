module

public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Splitting in an algebraically closed extension, as a `Fact`

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

/-- Every polynomial over `F` splits in an algebraically closed extension `E`, as a `Fact`
instance: this makes `Polynomial.Gal.galAction`, the action of `p.Gal` on the roots of `p` in
`E`, available with no hypothesis to discharge. (Mathlib has `Polynomial.Gal.splits_ℚ_ℂ`, the
special case `F = ℚ`, `E = ℂ`, as a local instance.) -/
instance Polynomial.Gal.instFactSplitsOfIsAlgClosed {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] {p : F[X]} : Fact (p.map (algebraMap F E)).Splits :=
  ⟨IsAlgClosed.splits _⟩
