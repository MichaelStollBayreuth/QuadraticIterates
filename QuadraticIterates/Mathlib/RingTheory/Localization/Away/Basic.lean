/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

import QuadraticIterates.Mathlib.RingTheory.Localization.Basic

/-!
# Localization away from an element: domains, primes, divisibility

The localization of a domain away from a nonzero element is a domain, as an instance for
`[NeZero x]`; a prime not dividing `x` stays prime in it
(`IsLocalization.Away.prime_algebraMap_of_not_dvd`); and divisibility by an element coprime
to `x` descends from it (`IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- The localization of a domain away from a nonzero element is a domain. -/
instance Localization.Away.instIsDomain {R : Type*} [CommRing R] [IsDomain R] (x : R)
    [NeZero x] : IsDomain (Localization.Away x) :=
  Localization.Away.isDomain (NeZero.ne x)

namespace IsLocalization.Away

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {x : R}
  [IsLocalization.Away x S]

/-- Divisibility descends from a localization away from `x` to a divisor coprime to `x`. -/
theorem dvd_of_algebraMap_dvd_of_isCoprime {a b : R} (h : algebraMap R S a ∣ algebraMap R S b)
    (hax : IsCoprime a x) : a ∣ b :=
  IsLocalization.dvd_of_algebraMap_dvd (Submonoid.powers x) h fun _ ⟨_, hn⟩ ↦ hn ▸ hax.pow_right

variable [IsDomain R]

/-- A prime not dividing `x` stays prime in a localization away from `x`. -/
theorem prime_algebraMap_of_not_dvd (hx : x ≠ 0) {p : R} (hp : Prime p) (hpx : ¬p ∣ x) :
    Prime (algebraMap R S p) :=
  IsLocalization.prime_algebraMap_of_prime (Submonoid.powers x) hp
    (fun h ↦ hp.ne_zero (IsLocalization.injective S
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx) (h.trans (map_zero _).symm)))
    fun h ↦ hpx (((IsLocalization.Away.algebraMap_isUnit_iff x).mp h).elim
      fun _ hn ↦ hp.dvd_of_dvd_pow hn)

end IsLocalization.Away

end
