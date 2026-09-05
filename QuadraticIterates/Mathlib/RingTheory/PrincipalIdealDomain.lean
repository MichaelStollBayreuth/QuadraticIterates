module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coprimality in Bézout domains

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- If `m` divides `a + b` and is coprime to `gcd a b`, then `m` is coprime to `a`: a common
divisor of `m` and `a` divides `b`, hence `gcd a b`. -/
theorem isCoprime_of_isCoprime_gcd_of_dvd_add {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    [GCDMonoid R] {m a b : R} (hcop : IsCoprime m (gcd a b)) (hdvd : m ∣ a + b) :
    IsCoprime m a :=
  IsRelPrime.isCoprime fun _ hdm hda ↦
    hcop.isRelPrime hdm (dvd_gcd hda (by simpa using dvd_sub (hdm.trans hdvd) hda))
