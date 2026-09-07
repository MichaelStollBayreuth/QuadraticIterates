/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Localization.Basic

import Mathlib.GroupTheory.MonoidLocalization.Divisibility
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Primes and divisibility under localization

A prime whose image in a localization is a nonzero non-unit stays prime
(`IsLocalization.prime_algebraMap_of_prime`), and divisibility by an element coprime to the
submonoid descends from the localization (`IsLocalization.dvd_of_algebraMap_dvd`). Both are
ring-level forms of `Submonoid.LocalizationMap.map_prime` and
`Submonoid.LocalizationMap.map_dvd_map`; the first is stated as in Mathlib PR #37247, to be
deleted once that lands.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IsLocalization

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem prime_algebraMap_of_prime (M : Submonoid R) [IsLocalization M S] {x : R} (hx : Prime x)
    (hx0 : algebraMap R S x ≠ 0) (hxu : ¬IsUnit (algebraMap R S x)) :
    Prime (algebraMap R S x) :=
  (toLocalizationMap M S).map_prime hx hx0 hxu

/-- Divisibility descends from a localization to a divisor coprime to the submonoid. -/
theorem dvd_of_algebraMap_dvd (M : Submonoid R) [IsLocalization M S] {a b : R}
    (h : algebraMap R S a ∣ algebraMap R S b) (hM : ∀ m ∈ M, IsCoprime a m) : a ∣ b := by
  obtain ⟨m, hm, hab⟩ := (toLocalizationMap M S).map_dvd_map.mp h
  exact (hM m hm).dvd_of_dvd_mul_left hab

end IsLocalization

end
