module

public import Mathlib.LinearAlgebra.Pi

/-!
# Injectivity of extension by zero

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Function.ExtendByZero

/-- Extension by zero along an injective map is injective. -/
theorem linearMap_injective (R : Type*) [Semiring R] {ι η : Type*} {s : ι → η} (hs : Injective s) :
    Injective (linearMap R s) :=
  extend_injective hs (0 : η → R)

end Function.ExtendByZero
