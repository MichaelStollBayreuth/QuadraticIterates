/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import QuadraticIterates.Mathlib.RingTheory.Localization.Basic

/-!
# Localization away from an element: domains, primes, divisibility

The localization of a domain away from a nonzero element is a domain, of characteristic zero if
the domain is, as instances for `[NeZero x]`; a prime not dividing `x` stays prime in it
(`IsLocalization.Away.prime_algebraMap_of_not_dvd`); divisibility by an element coprime to `x`
descends from it (`IsLocalization.Away.dvd_of_algebraMap_dvd_of_isCoprime`), and so does
relative primality when one of the elements is coprime to `x`
(`IsLocalization.Away.isRelPrime_of_isRelPrime_algebraMap`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- The localization of a domain away from a nonzero element is a domain. -/
instance Localization.Away.instIsDomain {R : Type*} [CommRing R] [IsDomain R] (x : R)
    [NeZero x] : IsDomain (Localization.Away x) :=
  Localization.Away.isDomain (NeZero.ne x)

/-- The localization of a domain of characteristic zero away from a nonzero element has
characteristic zero. -/
instance Localization.Away.instCharZero {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (x : R)
    [NeZero x] : CharZero (Localization.Away x) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (NeZero.ne x)))

namespace IsLocalization.Away

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {x : R}
  [IsLocalization.Away x S]

/-- Divisibility descends from a localization away from `x` to a divisor coprime to `x`. -/
theorem dvd_of_algebraMap_dvd_of_isCoprime {a b : R} (h : algebraMap R S a ∣ algebraMap R S b)
    (hax : IsCoprime a x) : a ∣ b :=
  IsLocalization.dvd_of_algebraMap_dvd (Submonoid.powers x) h fun _ ⟨_, hn⟩ ↦ hn ▸ hax.pow_right

variable [IsDomain R] [NeZero x]

/-- A prime not dividing `x` stays prime in a localization away from `x`. -/
theorem prime_algebraMap_of_not_dvd {p : R} (hp : Prime p) (hpx : ¬p ∣ x) :
    Prime (algebraMap R S p) :=
  IsLocalization.prime_algebraMap_of_prime (Submonoid.powers x) hp
    (fun h ↦ hp.ne_zero (IsLocalization.injective S
      (powers_le_nonZeroDivisors_of_noZeroDivisors (NeZero.ne x)) (h.trans (map_zero _).symm)))
    fun h ↦ hpx (((IsLocalization.Away.algebraMap_isUnit_iff x).mp h).elim
      fun _ hn ↦ hp.dvd_of_dvd_pow hn)

variable [UniqueFactorizationMonoid R]

/-- Relative primality descends from a localization away from `x` to elements the first of which
is coprime to `x`: a common prime factor would stay prime in the localization. -/
theorem isRelPrime_of_isRelPrime_algebraMap {a b : R}
    (h : IsRelPrime (algebraMap R S a) (algebraMap R S b)) (hax : IsCoprime a x) :
    IsRelPrime a b := by
  rcases eq_or_ne a 0 with rfl | ha
  · obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff x).mp
      (isRelPrime_zero_left.mp (by simpa using h))
    exact isRelPrime_zero_left.mpr (isUnit_of_dvd_unit hn ((isCoprime_zero_left.mp hax).pow n))
  refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha).mpr fun p hpa hpb hp ↦ ?_
  have hpx : ¬p ∣ x := fun hpx ↦ hp.not_isUnit (hax.isUnit_of_dvd' hpa hpx)
  exact (prime_algebraMap_of_not_dvd hp hpx).not_isUnit (h (map_dvd _ hpa) (map_dvd _ hpb))

end IsLocalization.Away

end
