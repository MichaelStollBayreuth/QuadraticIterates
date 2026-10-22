/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Int.Basic

/-!
# Natural primes dividing integers

A prime `p ∈ ℕ` dividing one of two coprime integers does not divide the other
(`Int.Prime.not_dvd_of_isCoprime`), and an odd one does not divide `2` (`Int.Prime.not_dvd_two`),
in the form of `Int.Prime.dvd_mul'` and `Int.Prime.dvd_pow'`.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

theorem Int.Prime.not_dvd_of_isCoprime {p : ℕ} (hp : p.Prime) {x y : ℤ} (h : IsCoprime x y)
    (hy : (p : ℤ) ∣ y) :
    ¬(p : ℤ) ∣ x :=
  fun hx ↦ (Nat.prime_iff_prime_int.mp hp).not_isUnit (h.isUnit_of_dvd' hx hy)

theorem Int.Prime.not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬(p : ℤ) ∣ 2 :=
  fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (mod_cast h))
