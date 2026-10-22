/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime factors in residue classes

A natural number `≡ 3 (mod 4)` or `≡ 6 (mod 8)` has a prime factor `≡ 3 (mod 4)`, and one
`≡ ±3 (mod 8)` has a prime factor `≡ ±3 (mod 8)`: the residues of odd numbers `≡ 1 (mod 4)`, resp.
`≡ ±1 (mod 8)`, are closed under multiplication.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Nat

/-- Splitting off the least prime factor `p` of `m ≠ 1`: `m = p * q` with `q < m`. -/
private lemma exists_minFac_mul {m : ℕ} (hm : m ≠ 1) (hm0 : m ≠ 0) :
    ∃ q, m = m.minFac * q ∧ q < m := by
  obtain ⟨q, hq⟩ := minFac_dvd m
  have hq0 : 0 < q := Nat.pos_of_ne_zero fun h ↦ hm0 (by rw [hq, h, mul_zero])
  exact ⟨q, hq, by lia [Nat.mul_le_mul_right q (minFac_prime hm).two_le]⟩

/-- A natural number `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`: a product of odd numbers
`≡ 1 (mod 4)` is `≡ 1 (mod 4)`. -/
theorem exists_prime_dvd_of_mod_four_eq_three {m : ℕ} (hm : m % 4 = 3) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨q, hq, hqm⟩ := exists_minFac_mul (m := m) (by lia) (by lia)
    have hp2 : m.minFac % 2 = 1 := by
      have := Nat.mul_mod m.minFac q 2
      rcases Nat.mod_two_eq_zero_or_one m.minFac with h | h <;> simp [h, ← hq] at this <;> lia
    have h4 := Nat.mul_mod m.minFac q 4
    rw [← hq, hm] at h4
    rcases (by lia : m.minFac % 4 = 1 ∨ m.minFac % 4 = 3) with h | h
    · obtain ⟨p, hp, hp3, hpq⟩ := ih q hqm (by rw [h, one_mul, Nat.mod_mod] at h4; lia)
      exact ⟨p, hp, hp3, hpq.trans (Dvd.intro_left _ hq.symm)⟩
    · exact ⟨_, minFac_prime (by lia), h, minFac_dvd m⟩

/-- A natural number `≡ 6 (mod 8)` has a prime factor `≡ 3 (mod 4)`, one of `m / 2 ≡ 3 (mod 4)`. -/
theorem exists_prime_dvd_of_mod_eight_eq_six {m : ℕ} (hm : m % 8 = 6) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ m := by
  obtain ⟨p, hp, hp3, hpm⟩ := exists_prime_dvd_of_mod_four_eq_three (m := m / 2) (by lia)
  exact ⟨p, hp, hp3, hpm.trans (Nat.div_dvd_of_dvd (by lia))⟩

/-- A natural number `≡ ±3 (mod 8)` has a prime factor `≡ ±3 (mod 8)`: a product of odd numbers
`≡ ±1 (mod 8)` is `≡ ±1 (mod 8)`. -/
theorem exists_prime_dvd_of_mod_eight_eq_three_or_five {m : ℕ} (hm : m % 8 = 3 ∨ m % 8 = 5) :
    ∃ p, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ p ∣ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨q, hq, hqm⟩ := exists_minFac_mul (m := m) (by lia) (by lia)
    have hp2 : m.minFac % 2 = 1 := by
      have := Nat.mul_mod m.minFac q 2
      rcases Nat.mod_two_eq_zero_or_one m.minFac with h | h <;> simp [h, ← hq] at this <;> lia
    have h8 := Nat.mul_mod m.minFac q 8
    rw [← hq] at h8
    rcases (by lia : m.minFac % 8 = 1 ∨ m.minFac % 8 = 7 ∨ m.minFac % 8 = 3 ∨ m.minFac % 8 = 5)
      with h | h | h
    · obtain ⟨p, hp, hp3, hpq⟩ := ih q hqm (by rw [h, one_mul, Nat.mod_mod] at h8; lia)
      exact ⟨p, hp, hp3, hpq.trans (Dvd.intro_left _ hq.symm)⟩
    · obtain ⟨p, hp, hp3, hpq⟩ := ih q hqm (by rw [h] at h8; lia)
      exact ⟨p, hp, hp3, hpq.trans (Dvd.intro_left _ hq.symm)⟩
    · exact ⟨_, minFac_prime (by lia), h, minFac_dvd m⟩

end Nat

namespace Int

theorem exists_prime_dvd_of_emod_four_eq_three {x : ℤ} (hx : 0 < x) (h : x % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ x :=
  let ⟨p, hp, hp4, hpd⟩ := Nat.exists_prime_dvd_of_mod_four_eq_three (m := x.natAbs) (by lia)
  ⟨p, hp, hp4, Int.ofNat_dvd_left.mpr hpd⟩

theorem exists_prime_dvd_of_emod_eight_eq_six {x : ℤ} (hx : 0 < x) (h : x % 8 = 6) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ x :=
  let ⟨p, hp, hp4, hpd⟩ := Nat.exists_prime_dvd_of_mod_eight_eq_six (m := x.natAbs) (by lia)
  ⟨p, hp, hp4, Int.ofNat_dvd_left.mpr hpd⟩

/-- An integer `≡ ±3 (mod 8)` has a prime factor `≡ ±3 (mod 8)`, whatever its sign: `|x| ≡ ±3`
as well. -/
theorem exists_prime_dvd_of_emod_eight_eq_three_or_five {x : ℤ} (h : x % 8 = 3 ∨ x % 8 = 5) :
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ (p : ℤ) ∣ x :=
  let ⟨p, hp, hp8, hpd⟩ :=
    Nat.exists_prime_dvd_of_mod_eight_eq_three_or_five (m := x.natAbs) (by lia)
  ⟨p, hp, hp8, Int.ofNat_dvd_left.mpr hpd⟩

end Int
