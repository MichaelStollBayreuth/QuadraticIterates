/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

import QuadraticIterates.Mathlib.Algebra.GCDMonoid.Basic

/-!
# Coprimality in Bézout domains

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- If `m` divides `a + b` and is coprime to `gcd a b`, then `m` is coprime to `a` (the
`IsCoprime` form of `IsRelPrime.of_gcd_right_of_dvd_add`, in a Bézout domain). -/
theorem isCoprime_of_isCoprime_gcd_of_dvd_add {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    [GCDMonoid R] {m a b : R} (hcop : IsCoprime m (gcd a b)) (hdvd : m ∣ a + b) :
    IsCoprime m a :=
  (hcop.isRelPrime.of_gcd_right_of_dvd_add hdvd).isCoprime
