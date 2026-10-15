/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import QuadraticIterates.Galois.Iterates

import Mathlib.Tactic.Field
import QuadraticIterates.Mathlib.Data.ZMod

/-!
# The integer sequence `w_n` behind `c_n`

For a parameter `a = r/s` with `r, s ∈ ℤ`, the integers `w_1 = -1`,
`w_{n+1} = r w_n² + s^{2^n - 1}` satisfy `c_n = r w_n / s^{2^{n-1}}`, and
`v_n = w_{n+1} + w_n s^{2^{n-1}}`, `u_n = r² w_n² - r w_n s^{2^{n-1}} + (r + s) s^{2^n - 1}`
satisfy `c_n + c_{n+1} = r v_n / s^{2^n}` and `c_n² - c_n + a + 1 = u_n / s^{2^n}`. More generally,
in any commutative ring `S` in which `s` has an inverse `σ`, these identities hold with the
sequence `c̄` of the parameter `r σ` (the reduction lemmas); with `S = ZMod N` for `N` prime to `s`
this turns congruences for `w_n` into computations with `c̄`.

## Main definitions

* `QuadraticIterates.wSeq r s`, `QuadraticIterates.vSeq r s`, `QuadraticIterates.uSeq r s`.

## Main statements

* `QuadraticIterates.intCast_mul_wSeq`, `QuadraticIterates.intCast_mul_vSeq`,
  `QuadraticIterates.intCast_uSeq`: the reduction lemmas; `QuadraticIterates.cSeq_div_eq`:
  `c_n = r w_n / s^{2^{n-1}}`.
* `QuadraticIterates.isCoprime_wSeq_left`, `QuadraticIterates.isCoprime_wSeq_right`: for coprime
  `r, s`, `w_n` is prime to `r` and to `s`; `v_n` and `u_n` are prime to `s`.
* `QuadraticIterates.wSeq_modEq_left`, `QuadraticIterates.wSeq_modEq_right`,
  `QuadraticIterates.vSeq_modEq_left`: residues modulo `r` and `s`; residues modulo `8`
  (`QuadraticIterates.intCast_mul_wSeq_zmod_eight`: `r w_n ≡ c̄_n (mod 8)` for odd `s`).
-/

@[expose] public section

namespace QuadraticIterates

variable (r s : ℤ)

/-- The integer sequence `w_n` of a parameter `a = r/s`: `w_1 = -1` and
`w_{n+1} = r w_n² + s^{2^n - 1}`, so that `c_n = r w_n / s^{2^{n-1}}`
(`QuadraticIterates.cSeq_div_eq`); the value at index `0` is `0`. -/
def wSeq : ℕ → ℤ
  | 0 => 0
  | 1 => -1
  | n + 2 => r * wSeq (n + 1) ^ 2 + s ^ (2 ^ (n + 1) - 1)

@[simp] lemma wSeq_zero : wSeq r s 0 = 0 := rfl

@[simp] lemma wSeq_one : wSeq r s 1 = -1 := rfl

lemma wSeq_succ {n : ℕ} (hn : 1 ≤ n) : wSeq r s (n + 1) = r * wSeq r s n ^ 2 + s ^ (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rfl

@[simp] lemma wSeq_two : wSeq r s 2 = r + s := by simp [wSeq_succ r s le_rfl]

/-- `v_n = w_{n+1} + w_n s^{2^{n-1}}`, so that `c_n + c_{n+1} = r v_n / s^{2^n}`
(`QuadraticIterates.intCast_mul_vSeq`). -/
def vSeq (n : ℕ) : ℤ := wSeq r s (n + 1) + wSeq r s n * s ^ 2 ^ (n - 1)

/-- `u_n = r² w_n² - r w_n s^{2^{n-1}} + (r + s) s^{2^n - 1}`, so that
`c_n² - c_n + a + 1 = u_n / s^{2^n}` (`QuadraticIterates.intCast_uSeq`). -/
def uSeq (n : ℕ) : ℤ :=
  r ^ 2 * wSeq r s n ^ 2 - r * wSeq r s n * s ^ 2 ^ (n - 1) + (r + s) * s ^ (2 ^ n - 1)

@[simp] lemma vSeq_one : vSeq r s 1 = r := by simp [vSeq]

section Reduction

variable {s} {S : Type*} [CommRing S] {σ : S}

/-- **Reduction**: if `s` is invertible in `S` with inverse `σ`, then `r w_n = s^{2^{n-1}} c̄_n`
in `S`, where `c̄` is the sequence of the parameter `r σ`. -/
theorem intCast_mul_wSeq (hσ : (s : S) * σ = 1) {n : ℕ} (hn : 1 ≤ n) :
    (r : S) * wSeq r s n = (s : S) ^ 2 ^ (n - 1) * cSeq ((r : S) * σ) n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp
    grobner
  | succ n hn ih =>
    have he : (s : S) ^ 2 ^ n = (s : S) ^ (2 ^ n - 1) * s := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    have hsq : ((s : S) ^ 2 ^ (n - 1)) ^ 2 = (s : S) ^ 2 ^ n := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn]
    rw [wSeq_succ r s hn, cSeq_succ _ hn, Nat.add_sub_cancel]
    push_cast
    grobner

theorem intCast_mul_vSeq (hσ : (s : S) * σ = 1) {n : ℕ} (hn : 1 ≤ n) :
    (r : S) * vSeq r s n =
      (s : S) ^ 2 ^ n * (cSeq ((r : S) * σ) n + cSeq ((r : S) * σ) (n + 1)) := by
  have h₁ := intCast_mul_wSeq r hσ hn
  have h₂ := intCast_mul_wSeq r hσ (n := n + 1) (by lia)
  have hsq : ((s : S) ^ 2 ^ (n - 1)) ^ 2 = (s : S) ^ 2 ^ n := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn]
  rw [Nat.add_sub_cancel] at h₂
  simp only [vSeq, Int.cast_add, Int.cast_mul, Int.cast_pow]
  grobner

theorem intCast_uSeq (hσ : (s : S) * σ = 1) {n : ℕ} (hn : 1 ≤ n) :
    (uSeq r s n : S) =
      (s : S) ^ 2 ^ n * (cSeq ((r : S) * σ) n ^ 2 - cSeq ((r : S) * σ) n + r * σ + 1) := by
  have h₁ := intCast_mul_wSeq r hσ hn
  have hsq : ((s : S) ^ 2 ^ (n - 1)) ^ 2 = (s : S) ^ 2 ^ n := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn]
  have he : (s : S) ^ 2 ^ n = (s : S) ^ (2 ^ n - 1) * s := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  simp only [uSeq, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow]
  grobner

/-- `c_n = r w_n / s^{2^{n-1}}` for the parameter `a = r/s`. -/
theorem cSeq_div_eq (hs : s ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    cSeq ((r : ℚ) / s) n = r * wSeq r s n / (s : ℚ) ^ 2 ^ (n - 1) := by
  have hs' : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  rw [intCast_mul_wSeq r (mul_inv_cancel₀ hs') hn, div_eq_mul_inv]
  field

variable {r} in
/-- If `v_n` vanishes in a ring where `s` has an inverse `σ`, then `c̄_n + c̄_{n+1} = 0` for the
sequence `c̄` of the parameter `r σ`. -/
theorem cSeq_add_cSeq_succ_eq_zero_of_vSeq (hσ : (s : S) * σ = 1) {n : ℕ} (hn : 1 ≤ n)
    (hv : (vSeq r s n : S) = 0) : cSeq ((r : S) * σ) n + cSeq ((r : S) * σ) (n + 1) = 0 := by
  have h := intCast_mul_vSeq r hσ hn
  rw [hv, mul_zero, eq_comm] at h
  exact ((IsUnit.of_mul_eq_one σ hσ).pow _).mul_right_eq_zero.mp h

variable {r} in
/-- If `u_n` vanishes in a ring where `s` has an inverse `σ`, then `c̄_n² - c̄_n + a + 1 = 0` for
the sequence `c̄` of the parameter `a = r σ`. -/
theorem cSeq_sq_sub_cSeq_add_eq_zero_of_uSeq (hσ : (s : S) * σ = 1) {n : ℕ} (hn : 1 ≤ n)
    (hu : (uSeq r s n : S) = 0) :
    cSeq ((r : S) * σ) n ^ 2 - cSeq ((r : S) * σ) n + r * σ + 1 = 0 := by
  have h := intCast_uSeq r hσ hn
  rw [hu, eq_comm] at h
  exact ((IsUnit.of_mul_eq_one σ hσ).pow _).mul_right_eq_zero.mp h

end Reduction

/-! ### Coprimality and residues -/

section Coprime

variable {r s} (hrs : IsCoprime r s)
include hrs

theorem isCoprime_wSeq_left {n : ℕ} (hn : 1 ≤ n) : IsCoprime (wSeq r s n) r := by
  induction n, hn using Nat.le_induction with
  | base => simpa using isCoprime_one_left.neg_left
  | succ n hn _ =>
    rw [wSeq_succ r s hn, add_comm]
    exact hrs.symm.pow_left.add_mul_left_left _

theorem isCoprime_wSeq_right {n : ℕ} (hn : 1 ≤ n) : IsCoprime (wSeq r s n) s := by
  induction n, hn using Nat.le_induction with
  | base => simpa using isCoprime_one_left.neg_left
  | succ n hn ih =>
    obtain ⟨t, ht⟩ := dvd_pow_self s (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (n := n) (by lia)))
    rw [wSeq_succ r s hn, ht]
    exact (hrs.mul_left ih.pow_left).add_mul_left_left t

theorem isCoprime_vSeq_right (n : ℕ) : IsCoprime (vSeq r s n) s := by
  obtain ⟨t, ht⟩ := dvd_pow_self s (Nat.two_pow_pos (n - 1)).ne'
  rw [vSeq, ht, mul_left_comm]
  exact (isCoprime_wSeq_right hrs (by lia)).add_mul_left_left _

theorem isCoprime_uSeq_right {n : ℕ} (hn : 1 ≤ n) : IsCoprime (uSeq r s n) s := by
  obtain ⟨t, ht⟩ := dvd_pow_self s (Nat.two_pow_pos (n - 1)).ne'
  obtain ⟨t', ht'⟩ := dvd_pow_self s (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (n := n) (by lia)))
  have hu : uSeq r s n = r ^ 2 * wSeq r s n ^ 2 + s * (-(r * wSeq r s n * t) + (r + s) * t') := by
    rw [uSeq, ht, ht']
    ring
  rw [hu]
  exact (hrs.pow_left.mul_left (isCoprime_wSeq_right hrs hn).pow_left).add_mul_left_left _

end Coprime

theorem wSeq_modEq_left {n : ℕ} (hn : 2 ≤ n) : wSeq r s n ≡ s ^ (2 ^ (n - 1) - 1) [ZMOD r] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [wSeq_succ r s (by lia), Nat.add_sub_cancel, add_comm, Int.ModEq,
    Int.add_mul_emod_self_left]

theorem wSeq_modEq_right {n : ℕ} (hn : 2 ≤ n) : wSeq r s n ≡ r ^ (2 ^ (n - 1) - 1) [ZMOD s] := by
  induction n, hn using Nat.le_induction with
  | base => simp [Int.ModEq]
  | succ n hn ih =>
    obtain ⟨t, ht⟩ := dvd_pow_self s (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (n := n) (by lia)))
    have he : 2 ^ (n + 1 - 1) - 1 = 2 * (2 ^ (n - 1) - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n - 1)
      rw [Nat.add_sub_cancel, ← Nat.sub_add_cancel (by lia : 1 ≤ n), pow_succ]
      lia
    rw [wSeq_succ r s (by lia), ht, he, Int.ModEq, Int.add_mul_emod_self_left, ← Int.ModEq]
    calc r * wSeq r s n ^ 2 ≡ r * (r ^ (2 ^ (n - 1) - 1)) ^ 2 [ZMOD s] := (ih.pow 2).mul_left r
      _ = r ^ (2 * (2 ^ (n - 1) - 1) + 1) := by ring

theorem vSeq_modEq_left {n : ℕ} (hn : 2 ≤ n) : vSeq r s n ≡ 2 * s ^ (2 ^ n - 1) [ZMOD r] := by
  have h₁ := wSeq_modEq_left r s (n := n + 1) (by lia)
  have h₂ := wSeq_modEq_left r s hn
  rw [Nat.add_sub_cancel] at h₁
  have he : s ^ (2 ^ (n - 1) - 1) * s ^ 2 ^ (n - 1) = s ^ (2 ^ n - 1) := by
    rw [← pow_add]
    congr 1
    have := Nat.one_le_two_pow (n := n - 1)
    rw [← Nat.sub_add_cancel (by lia : 1 ≤ n), pow_succ, Nat.add_sub_cancel]
    lia
  rw [vSeq, two_mul]
  exact h₁.add (he ▸ h₂.mul_right _)

section Dyadic

variable {r s}

theorem odd_wSeq_of_even (hs : Even s) (hr : Odd r) {n : ℕ} (hn : 1 ≤ n) : Odd (wSeq r s n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [wSeq_succ r s hn]
    exact (hr.mul ih.pow).add_even
      (hs.pow_of_ne_zero (Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow (n := n) (by lia))))

/-- For even `s`, `w_n ≡ r (mod 8)` from `n = 3` on: `8 ∣ s^{2^n - 1}` and `w_n` is odd. -/
theorem intCast_wSeq_zmod_eight_of_even (hs : Even s) (hr : Odd r) {n : ℕ} (hn : 3 ≤ n) :
    (wSeq r s n : ZMod 8) = r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have h8 : ((s ^ (2 ^ m - 1) : ℤ) : ZMod 8) = 0 := by
    obtain ⟨t, rfl⟩ := hs
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr
      ((Dvd.intro (t ^ 3) (by ring : (8 : ℤ) * t ^ 3 = (t + t) ^ 3)).trans
        (pow_dvd_pow (t + t) (?_ : 3 ≤ 2 ^ m - 1)))
    have := Nat.pow_le_pow_right two_pos (by lia : 2 ≤ m)
    lia
  rw [wSeq_succ r s (by lia)]
  push_cast at h8 ⊢
  rw [h8, ZMod.intCast_sq_eight_eq_one_of_odd (odd_wSeq_of_even hs hr (by lia)), mul_one,
    add_zero]

/-- For odd `s`, `w_{n+1} ≡ r w_n² + s (mod 8)`: `s^{2^n - 1} ≡ s`. -/
theorem intCast_wSeq_succ_zmod_eight_of_odd (hs : Odd s) {n : ℕ} (hn : 1 ≤ n) :
    (wSeq r s (n + 1) : ZMod 8) = r * wSeq r s n ^ 2 + s := by
  rw [wSeq_succ r s hn]
  push_cast
  rw [ZMod.intCast_pow_two_pow_sub_one_eight_of_odd hs hn]

variable (r) in
/-- For odd `s` and `n ≥ 2`, `r w_n ≡ c̄_n (mod 8)`, where `c̄` is the sequence of `r s` in
`ZMod 8`: `s` is its own inverse modulo `8`, and `s^{2^{n-1}} ≡ 1`. -/
theorem intCast_mul_wSeq_zmod_eight (hs : Odd s) {n : ℕ} (hn : 2 ≤ n) :
    ((r * wSeq r s n : ℤ) : ZMod 8) = cSeq ((r : ZMod 8) * s) n := by
  have hσ : (s : ZMod 8) * s = 1 := by rw [← sq]; exact ZMod.intCast_sq_eight_eq_one_of_odd hs
  have he : (s : ZMod 8) ^ 2 ^ (n - 1) = 1 := by
    rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; lia, pow_mul,
      ZMod.intCast_sq_eight_eq_one_of_odd hs, one_pow]
  rw [Int.cast_mul, intCast_mul_wSeq r hσ (by lia), he, one_mul]

end Dyadic

end QuadraticIterates
