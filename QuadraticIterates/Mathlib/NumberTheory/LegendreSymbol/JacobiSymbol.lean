/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Squares modulo `M` from squares modulo prime powers

A square root modulo an odd prime `p`, prime to `p`, lifts to every power of `p`
(`Int.exists_sq_modEq_prime_pow`), and an integer `≡ 1 (mod 8)` is a square modulo every power
of `2` (`Int.exists_sq_modEq_two_pow`); by the Chinese remainder theorem
(`ZMod.isSquare_intCast_mul`) an integer is a square modulo `M ≠ 0` once these local conditions
hold at the prime powers dividing `M` (`ZMod.isSquare_intCast_of_forall`). Hence an integer `x`
prime to `M ≠ 0` that is not a square modulo `M` is not a square modulo an odd prime `p ∣ M`, or
`4 ∣ M` and `x ≡ 3 (mod 4)`, or `8 ∣ M` and `x ≢ 1 (mod 8)`
(`ZMod.exists_of_not_isSquare_intCast`).

## Main statements

* `Int.exists_sq_modEq_prime_pow`, `Int.exists_sq_modEq_two_pow`: lifting square roots.
* `ZMod.isSquare_intCast_of_forall`: the local criterion for squares modulo `M`.
* `ZMod.exists_of_not_isSquare_intCast`: a non-square modulo `M` is a non-square locally.

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Int

/-- **Lifting a square root**: if `z² ≡ x (mod m)` and `2z` is invertible modulo a divisor `n` of
`m`, then `(z + t m)² ≡ x (mod m n)` for some `t`. -/
theorem exists_add_mul_sq_modEq_mul {x z m n : ℤ} (hnm : n ∣ m) (hz : z ^ 2 ≡ x [ZMOD m])
    (hcop : IsCoprime (2 * z) n) : ∃ t, (z + t * m) ^ 2 ≡ x [ZMOD m * n] := by
  obtain ⟨d, hd⟩ := hz.dvd
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨e, rfl⟩ := hnm
  exact ⟨d * u, Int.modEq_iff_dvd.mpr ⟨d * v - d ^ 2 * u ^ 2 * e, by
    linear_combination hd - (d * n * e) * huv⟩⟩

/-- **Lifting a square root at `2`**: if `z` is odd, `4 ∣ m` and `z² ≡ x (mod 2m)`, then
`(z + t m)² ≡ x (mod 4m)` for some `t`. -/
theorem exists_add_mul_sq_modEq_four_mul {x z m : ℤ} (hz : Odd z) (hm : 4 ∣ m)
    (h : z ^ 2 ≡ x [ZMOD 2 * m]) : ∃ t, (z + t * m) ^ 2 ≡ x [ZMOD 4 * m] := by
  obtain ⟨d, hd⟩ := h.dvd
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨e, rfl⟩ := hm
  exact ⟨d, Int.modEq_iff_dvd.mpr ⟨-(d * w) - d ^ 2 * e, by linear_combination hd⟩⟩

/-- A square root of `x` modulo an odd prime `p`, prime to `p`, lifts to every power of `p`. -/
theorem exists_sq_modEq_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : ℤ}
    (hy : ¬(p : ℤ) ∣ y) (h : y ^ 2 ≡ x [ZMOD p]) (k : ℕ) : ∃ z, z ^ 2 ≡ x [ZMOD p ^ k] := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  have key (k : ℕ) : ∃ z, z ≡ y [ZMOD p] ∧ z ^ 2 ≡ x [ZMOD p ^ (k + 1)] := by
    induction k with
    | zero => exact ⟨y, .refl _, by simpa using h⟩
    | succ k ih =>
      obtain ⟨z, hzy, hz⟩ := ih
      have hcop : IsCoprime (2 * z) p := .mul_left
        (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm))
        (hp'.coprime_iff_not_dvd.mpr fun hz' ↦ hy ((hzy.dvd_iff ..).mp hz')).symm
      obtain ⟨t, ht⟩ := exists_add_mul_sq_modEq_mul (dvd_pow_self _ k.succ_ne_zero) hz hcop
      refine ⟨z + t * p ^ (k + 1), Int.ModEq.trans ?_ hzy, by rwa [← pow_succ] at ht⟩
      exact Int.modEq_iff_dvd.mpr ⟨-(t * p ^ k), by ring⟩
  obtain ⟨z, -, hz⟩ := key k
  exact ⟨z, hz.of_dvd (pow_dvd_pow _ k.le_succ)⟩

/-- An integer `≡ 1 (mod 8)` is a square modulo every power of `2`. -/
theorem exists_sq_modEq_two_pow {x : ℤ} (hx : x ≡ 1 [ZMOD 8]) (k : ℕ) :
    ∃ z, z ^ 2 ≡ x [ZMOD 2 ^ k] := by
  have key (k : ℕ) : ∃ z, Odd z ∧ z ^ 2 ≡ x [ZMOD 2 ^ (k + 3)] := by
    induction k with
    | zero => exact ⟨1, odd_one, by simpa using hx.symm⟩
    | succ k ih =>
      obtain ⟨z, hz, hzx⟩ := ih
      obtain ⟨t, ht⟩ := exists_add_mul_sq_modEq_four_mul hz ⟨2 ^ k, by ring⟩
        (show z ^ 2 ≡ x [ZMOD 2 * 2 ^ (k + 2)] by rwa [← pow_succ'])
      refine ⟨z + t * 2 ^ (k + 2), hz.add_even ⟨t * 2 ^ (k + 1), by ring⟩, ?_⟩
      rwa [show (4 : ℤ) * 2 ^ (k + 2) = 2 ^ (k + 1 + 3) by ring] at ht
  obtain ⟨z, -, hz⟩ := key k
  exact ⟨z, hz.of_dvd (pow_dvd_pow 2 (k.le_add_right 3))⟩

end Int

namespace ZMod

/-- An integer that is a square modulo coprime `m` and `n` is a square modulo `m n`; this
generalizes `ZMod.isSquare_neg_one_mul` from `-1` to any integer. -/
theorem isSquare_intCast_mul {m n : ℕ} (hmn : m.Coprime n) {x : ℤ}
    (hm : IsSquare (x : ZMod m)) (hn : IsSquare (x : ZMod n)) : IsSquare (x : ZMod (m * n)) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  refine ⟨(chineseRemainder hmn).symm (a, b), (chineseRemainder hmn).injective ?_⟩
  rw [map_mul, RingEquiv.apply_symm_apply, map_intCast]
  ext <;> simp [ha, hb]

/-- `x` is a square modulo `m` when `z² ≡ x (mod m)`. -/
private lemma isSquare_intCast_of_modEq {x z : ℤ} {m : ℕ} (h : z ^ 2 ≡ x [ZMOD m]) :
    IsSquare (x : ZMod m) :=
  ⟨z, by rw [← sq, ← Int.cast_pow, (ZMod.intCast_eq_intCast_iff _ _ m).mpr h.symm]⟩

/-- An integer with Jacobi symbol `1` modulo an odd prime `p` is a square modulo every power
of `p`. -/
theorem isSquare_intCast_prime_pow_of_jacobiSym_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {x : ℤ} (h : jacobiSym x p = 1) (k : ℕ) : IsSquare (x : ZMod (p ^ k)) := by
  obtain ⟨y, hy⟩ := ZMod.isSquare_of_jacobiSym_eq_one h
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
  have hx : (x : ZMod p) ≠ 0 := fun h0 ↦ by
    rw [← jacobiSym.legendreSym.to_jacobiSym, (legendreSym.eq_zero_iff p x).mpr h0] at h
    exact zero_ne_one h
  obtain ⟨z, hz⟩ := Int.exists_sq_modEq_prime_pow (Fact.out : p.Prime) hp2 (x := x) (y := y)
    (fun hd ↦ hx (by rw [hy, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd, mul_zero]))
    ((ZMod.intCast_eq_intCast_iff _ _ p).mp (by rw [Int.cast_pow, hy, sq])) k
  exact isSquare_intCast_of_modEq (by rwa [Nat.cast_pow])

theorem isSquare_intCast_two_pow_of_modEq {x : ℤ} (hx : x ≡ 1 [ZMOD 8]) (k : ℕ) :
    IsSquare (x : ZMod (2 ^ k)) := by
  obtain ⟨z, hz⟩ := Int.exists_sq_modEq_two_pow hx k
  exact isSquare_intCast_of_modEq (by rwa [Nat.cast_pow, Nat.cast_ofNat])

private lemma isSquare_intCast_two_pow {x : ℤ} {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ 2 ^ n → x % 4 = 1)
    (h8 : 8 ∣ 2 ^ n → x % 8 = 1) : IsSquare (x : ZMod (2 ^ n)) := by
  rcases (by lia : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | hn3
  · rw [pow_one]
    exact FiniteField.isSquare_of_char_two (ZMod.ringChar_zmod_n 2) _
  · rw [show (x : ZMod (2 ^ 2)) = 1 from (ZMod.intCast_eq_intCast_iff' x 1 4).mpr
      (by simpa using h4 dvd_rfl)]
    exact .one
  · exact isSquare_intCast_two_pow_of_modEq (h8 (pow_dvd_pow 2 hn3 : 2 ^ 3 ∣ 2 ^ n)) n

/-- An integer `x` is a square modulo `M ≠ 0` if `(x / p) = 1` for every odd prime `p ∣ M`,
`x ≡ 1 (mod 4)` when `4 ∣ M` and `x ≡ 1 (mod 8)` when `8 ∣ M`: by the Chinese remainder theorem
and Hensel lifting at each prime power. -/
theorem isSquare_intCast_of_forall {x : ℤ} {M : ℕ} (hM : M ≠ 0)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ M → jacobiSym x p = 1) (h4 : 4 ∣ M → x % 4 = 1)
    (h8 : 8 ∣ M → x % 8 = 1) : IsSquare (x : ZMod M) := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hpp hn =>
    rcases eq_or_ne p 2 with rfl | hp2
    · exact isSquare_intCast_two_pow hn h4 h8
    · have := Fact.mk hpp
      exact isSquare_intCast_prime_pow_of_jacobiSym_eq_one hp2
        (hp p hpp hp2 (dvd_pow_self p hn.ne')) n
  | zero => exact absurd rfl hM
  | one => exact ⟨0, Subsingleton.elim _ _⟩
  | coprime a b ha hb hab iha ihb =>
    exact isSquare_intCast_mul hab
      (iha (by lia) (fun p h₁ h₂ h₃ ↦ hp p h₁ h₂ (h₃.mul_right b)) (fun h ↦ h4 (h.mul_right b))
        fun h ↦ h8 (h.mul_right b))
      (ihb (by lia) (fun p h₁ h₂ h₃ ↦ hp p h₁ h₂ (h₃.mul_left a)) (fun h ↦ h4 (h.mul_left a))
        fun h ↦ h8 (h.mul_left a))

/-- An integer `x` prime to `M ≠ 0` and not a square modulo `M` is not a square modulo an odd
prime `p ∣ M`, or `4 ∣ M` and `x ≡ 3 (mod 4)`, or `8 ∣ M` and `x ≢ 1 (mod 8)`. -/
theorem exists_of_not_isSquare_intCast {x : ℤ} {M : ℕ} (hM : M ≠ 0) (hx : IsCoprime x M)
    (h : ¬IsSquare (x : ZMod M)) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ M ∧ jacobiSym x p = -1) ∨ (4 ∣ M ∧ x % 4 = 3) ∨
      (8 ∣ M ∧ x % 8 ≠ 1) := by
  by_contra! ⟨hp, h4, h8⟩
  refine h (isSquare_intCast_of_forall hM (fun p hpp hp2 hpM ↦ ?_) (fun h4M ↦ ?_) h8)
  · have hcop : x.gcd p = 1 := Int.isCoprime_iff_gcd_eq_one.mp
      (hx.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hpM))
    exact (jacobiSym.eq_one_or_neg_one hcop).resolve_right (hp p hpp hp2 hpM)
  · have h2 : ¬(2 : ℤ) ∣ x := fun h2 ↦ Int.prime_two.not_isUnit
      (hx.isUnit_of_dvd' h2 (Int.natCast_dvd_natCast.mpr ((dvd_mul_right 2 2).trans h4M)))
    lia

end ZMod

/-- `jacobiSym.sq_one'` for a prime `p` not dividing `t`. -/
theorem jacobiSym.sq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {t : ℤ} (ht : ¬(p : ℤ) ∣ t) :
    jacobiSym (t ^ 2) p = 1 :=
  jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.mp
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ht).symm)
