module

public import Mathlib.LinearAlgebra.Pi

/-!
# Injectivity of extension by zero

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Extension by zero along an injective map is injective. -/
theorem Function.ExtendByZero.linearMap_injective (R : Type*) [Semiring R] {ι η : Type*}
    {s : ι → η} (hs : Function.Injective s) :
    Function.Injective (Function.ExtendByZero.linearMap R s) :=
  Function.extend_injective hs (0 : η → R)
