/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Sequence.WSeq

import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Field
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.Signs

/-!
# The `2`-adic condition

For `a = r/s ∈ 𝒜` with its sign `ε` (`a ≤ -2` and `ε = -1`, or `a³ + 2a² + 2a + 2 > 0` and
`ε = 1`), the integers `v_n` of `QuadraticIterates.vSeq` satisfy `ε v_n > 0` for `n ≥ 2`, and their
residues modulo `4` and `8` are determined by those of `r` and `s`. In the three `2`-adic classes
(C1)–(C3) this gives every `v_n`, `n ≥ 2`, a prime factor `p ≡ 3 (mod 4)` not dividing `r`
(Lemma 4.4 of the draft), which is what reflection at level `n` needs. Likewise, for
`a ≡ 1 mod 4` and odd `n ≥ 3`, a positive `u_n` (`QuadraticIterates.uSeq`) is `≡ 6 (mod 8)` and
has a prime factor `p ≡ 3 (mod 4)` not dividing `r + s`, which is what period two at level `n`
needs.

## Main definitions

* `QuadraticIterates.TwoAdicClass r s ε`: the classes (C1)–(C3).

## Main statements

* `QuadraticIterates.mul_vSeq_pos`: `ε v_n > 0`.
* `QuadraticIterates.vSeq_modEq_add_two_mul`, `QuadraticIterates.vSeq_modEq_two_mul_add`,
  `QuadraticIterates.vSeq_modEq_of_even`: the residues of `v_n`.
* `QuadraticIterates.exists_prime_dvd_vSeq_of_twoAdicClass`: the prime factor.
* `QuadraticIterates.exists_prime_dvd_uSeq_of_odd`: the prime factor of `u_n`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- For odd `s`, the recursion of `QuadraticIterates.wSeq` modulo `8`. -/
theorem wSeq_succ_modEq_of_odd (hs : Odd s) {n : ℕ} (hn : 1 ≤ n) :
    wSeq r s (n + 1) ≡ r * wSeq r s n ^ 2 + s [ZMOD 8] :=
  (ZMod.intCast_eq_intCast_iff _ _ 8).mp <| by
    push_cast
    exact intCast_wSeq_succ_zmod_eight_of_odd hs hn

private lemma wSeq_succ_modEq_add_of_odd (hs : Odd s) {n : ℕ} (hn : 1 ≤ n)
    (hw : Odd (wSeq r s n)) : wSeq r s (n + 1) ≡ r + s [ZMOD 4] := by
  obtain ⟨u, hu⟩ := hw
  have h := wSeq_succ_modEq_of_odd (r := r) hs hn
  rw [Int.ModEq, hu] at h
  rw [Int.ModEq]
  lia

private lemma wSeq_succ_modEq_of_even (hs : Odd s) {n : ℕ} (hn : 1 ≤ n)
    (hw : Even (wSeq r s n)) : wSeq r s (n + 1) ≡ s [ZMOD 4] := by
  obtain ⟨u, hu⟩ := hw
  have h := wSeq_succ_modEq_of_odd (r := r) hs hn
  rw [Int.ModEq, hu] at h
  rw [Int.ModEq]
  lia

/-- For odd `r` and `s`, modulo `4` the terms `w_{2k}` are `r + s` and the terms `w_{2k+1}`
are `s`, for `k ≥ 1`. -/
private lemma wSeq_modEq_four (hr : Odd r) (hs : Odd s) {k : ℕ} (hk : 1 ≤ k) :
    wSeq r s (2 * k) ≡ r + s [ZMOD 4] ∧ wSeq r s (2 * k + 1) ≡ s [ZMOD 4] := by
  have he {w : ℤ} (h : w ≡ r + s [ZMOD 4]) : Even w := by
    rw [Int.ModEq] at h
    exact Int.even_iff.mpr (by lia [Int.odd_iff.mp hr, Int.odd_iff.mp hs])
  have ho {w : ℤ} (h : w ≡ s [ZMOD 4]) : Odd w := by
    rw [Int.ModEq] at h
    exact Int.odd_iff.mpr (by lia [Int.odd_iff.mp hs])
  induction k, hk using Nat.le_induction with
  | base =>
    have h : wSeq r s 2 ≡ r + s [ZMOD 4] := by simp [Int.ModEq]
    exact ⟨h, wSeq_succ_modEq_of_even hs one_le_two (he h)⟩
  | succ k hk ih =>
    have h := wSeq_succ_modEq_add_of_odd hs (by lia) (ho ih.2)
    exact ⟨h, wSeq_succ_modEq_of_even hs (by lia) (he h)⟩

/-- For odd `r` and `s`, `v_n ≡ r + 2s (mod 4)` for `n ≥ 2`. -/
theorem vSeq_modEq_add_two_mul (hr : Odd r) (hs : Odd s) {n : ℕ} (hn : 2 ≤ n) :
    vSeq r s n ≡ r + 2 * s [ZMOD 4] := by
  have he : s ^ 2 ^ (n - 1) ≡ 1 [ZMOD 4] := by
    rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; lia, pow_mul]
    simpa using (show s ^ 2 ≡ 1 [ZMOD 4] from Int.sq_emod_four_eq_one_of_odd hs).pow (2 ^ (n - 2))
  rw [vSeq]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := wSeq_modEq_four hr hs (k := k) (by lia)
    exact (by ring : s + (r + s) * 1 = r + 2 * s) ▸ h.2.add (h.1.mul he)
  · have h₁ := (wSeq_modEq_four hr hs (k := k + 1) (by lia)).1
    have h₂ := (wSeq_modEq_four hr hs (k := k) (by lia)).2
    exact (by ring : r + s + s * 1 = r + 2 * s) ▸ h₁.add (h₂.mul he)

/-- For even `r` and odd `s`, `w_m ≡ r + s (mod 8)` for `m ≥ 2`. -/
theorem intCast_wSeq_zmod_eight_of_even_left (hr : Even r) (hs : Odd s) {m : ℕ}
    (hm : 2 ≤ m) : (wSeq r s m : ZMod 8) = r + s := by
  have hsq : ((r + s : ℤ) : ZMod 8) ^ 2 = 1 := ZMod.intCast_sq_eight_eq_one_of_odd (hr.add_odd hs)
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [intCast_wSeq_succ_zmod_eight_of_odd hs (by lia), ih]
    push_cast at hsq
    rw [hsq, mul_one]

/-- For even `r` and odd `s`, `v_n ≡ 2(r + s) (mod 8)` for `n ≥ 2`. -/
theorem vSeq_modEq_two_mul_add (hr : Even r) (hs : Odd s) {n : ℕ} (hn : 2 ≤ n) :
    vSeq r s n ≡ 2 * (r + s) [ZMOD 8] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 8).mp ?_
  rw [vSeq]
  push_cast
  rw [ZMod.intCast_pow_two_pow_eight_of_odd hs (by lia),
    intCast_wSeq_zmod_eight_of_even_left hr hs (by lia),
    intCast_wSeq_zmod_eight_of_even_left hr hs hn]
  ring

/-- For even `s` (and `r` prime to `s`), `v_n ≡ r (mod 4)` for `n ≥ 2`: `w_{n+1} ≡ r (mod 8)` and
`4 ∣ s^{2^{n-1}}`. -/
theorem vSeq_modEq_of_even (hrs : IsCoprime r s) (hs : Even s) {n : ℕ} (hn : 2 ≤ n) :
    vSeq r s n ≡ r [ZMOD 4] := by
  have hr : Odd r := Int.not_even_iff_odd.mp fun he ↦
    (Nat.prime_iff_prime_int.mp Nat.prime_two).not_isUnit
      (hrs.isUnit_of_dvd' (even_iff_two_dvd.mp he) (even_iff_two_dvd.mp hs))
  have h4 : (s : ZMod 4) ^ 2 ^ (n - 1) = 0 := by
    obtain ⟨t, rfl⟩ := hs
    rw [show 2 ^ (n - 1) = 2 + (2 ^ (n - 1) - 2) by
      have := Nat.pow_le_pow_right two_pos (by lia : 1 ≤ n - 1); lia, pow_add]
    push_cast
    rw [show ((t : ZMod 4) + t) ^ 2 = 4 * t ^ 2 by ring, show (4 : ZMod 4) = 0 from rfl]
    ring
  have hw := congr(ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)
    $(intCast_wSeq_zmod_eight_of_even hs hr (n := n + 1) (by lia)))
  simp only [map_intCast] at hw
  refine (ZMod.intCast_eq_intCast_iff _ _ 4).mp ?_
  rw [vSeq]
  push_cast
  rw [hw, h4, mul_zero, add_zero]

/-- `r v_n = s^{2^n} (c_n + c_{n+1})` at `a = r/s`, as an identity in `ℚ`. -/
private lemma intCast_mul_vSeq_div (hs : s ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ((r * vSeq r s n : ℤ) : ℚ) =
      (s : ℚ) ^ 2 ^ n * (cSeq ((r : ℚ) / s) n + cSeq ((r : ℚ) / s) (n + 1)) := by
  push_cast
  rw [div_eq_mul_inv]
  exact intCast_mul_vSeq r (mul_inv_cancel₀ (mod_cast hs)) hn

/-- For `r ≤ -2s`, i.e. `a = r/s ≤ -2`, `v_n < 0`: `c_n + c_{n+1} ≥ -2a > 0`. -/
theorem vSeq_neg_of_le_neg_two_mul (hs : 0 < s) (h : r ≤ -2 * s) {n : ℕ} (hn : 1 ≤ n) :
    vSeq r s n < 0 := by
  have ha : (r : ℚ) / s ≤ -2 := by
    rw [div_le_iff₀ (mod_cast hs)]
    exact_mod_cast h
  have hrv : (0 : ℚ) < (r * vSeq r s n : ℤ) := by
    rw [intCast_mul_vSeq_div hs.ne' hn]
    have := neg_le_cSeq_of_le_neg_two ha (n := n + 1) (by lia)
    exact mul_pos (by positivity) (by linarith [neg_le_cSeq_of_le_neg_two ha hn])
  exact neg_of_mul_pos_right (mod_cast hrv) (by lia)

/-- For `r ≤ -2s` and `s > 0`, `-w_n ≥ s^{2^{n-1} - 1}` (`n ≥ 1`): `c_n = r w_n / s^{2^{n-1}}` is
at least `-r/s`. -/
theorem pow_le_neg_wSeq (hs : 0 < s) (h : r ≤ -2 * s) {n : ℕ} (hn : 1 ≤ n) :
    s ^ (2 ^ (n - 1) - 1) ≤ -wSeq r s n := by
  have hs' : (0 : ℚ) < s := mod_cast hs
  have hc := neg_le_cSeq_of_le_neg_two (a := (r : ℚ) / s)
    (by rw [div_le_iff₀ hs']; exact_mod_cast h) hn
  rw [cSeq_div_eq r hs.ne' hn, neg_div', div_le_div_iff₀ hs' (by positivity),
    ← Nat.sub_add_cancel (Nat.one_le_two_pow (n := n - 1)), pow_succ] at hc
  have hr : (0 : ℚ) < -r * s := mul_pos (neg_pos.mpr (mod_cast (by lia : r < 0))) hs'
  have : (s : ℚ) ^ (2 ^ (n - 1) - 1) ≤ -wSeq r s n := by
    refine le_of_mul_le_mul_left ?_ hr
    linear_combination hc
  exact_mod_cast this

/-- For `r > 0` and `s > 0`, `v_n > 0` for `n ≥ 2`. -/
theorem vSeq_pos_of_pos (hs : 0 < s) (hr : 0 < r) {n : ℕ} (hn : 2 ≤ n) : 0 < vSeq r s n := by
  have ha : 0 < (r : ℚ) / s := div_pos (mod_cast hr) (mod_cast hs)
  have hrv : (0 : ℚ) < (r * vSeq r s n : ℤ) := by
    rw [intCast_mul_vSeq_div hs.ne' (by lia)]
    exact mul_pos (by positivity) (add_pos (cSeq_pos_of_pos ha hn) (cSeq_pos_of_pos ha (by lia)))
  exact pos_of_mul_pos_right (mod_cast hrv) hr.le

/-- For `α < a = r/s < 0`, `α` the real root of `x³ + 2x² + 2x + 2`, `v_n > 0` for `n ≥ 2`:
`c_n + c_{n+1} < 0` (`QuadraticIterates.cSeq_add_cSeq_succ_neg`). -/
theorem vSeq_pos_of_neg (hs : 0 < s) (hr : r < 0)
    (h : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3) {n : ℕ} (hn : 2 ≤ n) :
    0 < vSeq r s n := by
  have hα : 0 < ((r : ℚ) / s) ^ 3 + 2 * ((r : ℚ) / s) ^ 2 + 2 * ((r : ℚ) / s) + 2 := by
    have hs' : (s : ℚ) ≠ 0 := mod_cast hs.ne'
    convert div_pos (mod_cast h : (0 : ℚ) < (r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 : ℤ))
      (pow_pos (mod_cast hs : (0 : ℚ) < s) 3) using 1
    push_cast
    field
  have hrv : ((r * vSeq r s n : ℤ) : ℚ) < 0 := by
    rw [intCast_mul_vSeq_div hs.ne' (by lia)]
    exact mul_neg_of_pos_of_neg (by positivity)
      (cSeq_add_cSeq_succ_neg _ (div_neg_of_neg_of_pos (mod_cast hr) (mod_cast hs)) hα hn)
  exact pos_of_mul_neg_right (mod_cast hrv) hr.le

/-- For `a = r/s ∈ 𝒜` with its sign `ε` (`a ≤ -2` and `ε = -1`, or `a > α` and `ε = 1`, `α` the
real root of `x³ + 2x² + 2x + 2`), `ε v_n > 0` for `n ≥ 2`. -/
theorem mul_vSeq_pos (hs : 0 < s) (hr : r ≠ 0) {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    {n : ℕ} (hn : 2 ≤ n) : 0 < ε * vSeq r s n := by
  rcases hε with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · simpa using vSeq_neg_of_le_neg_two_mul hs h (by lia : 1 ≤ n)
  rcases hr.lt_or_gt with hr | hr
  · simpa using vSeq_pos_of_neg hs hr h hn
  · simpa using vSeq_pos_of_pos hs hr hn

/-- The `2`-adic classes (C1)–(C3) of the main theorem for `a = r/s` with sign `ε`: `s` odd and
`r + 2s ≡ -ε (mod 4)`; `s` odd and `r + s ≡ -ε (mod 4)`; or `s` even and `r ≡ -ε (mod 4)`. -/
def TwoAdicClass (r s ε : ℤ) : Prop :=
  (Odd s ∧ r + 2 * s ≡ -ε [ZMOD 4]) ∨ (Odd s ∧ r + s ≡ -ε [ZMOD 4]) ∨ (Even s ∧ r ≡ -ε [ZMOD 4])

/-- Under (C1)–(C3), the positive integer `ε v_n` is `≡ 3 (mod 4)` or `≡ 6 (mod 8)`. -/
private lemma emod_of_twoAdicClass (hrs : IsCoprime r s) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hc : TwoAdicClass r s ε) {n : ℕ} (hn : 2 ≤ n) :
    ε * vSeq r s n % 4 = 3 ∨ ε * vSeq r s n % 8 = 6 := by
  rcases hc with ⟨hs, hc⟩ | ⟨hs, hc⟩ | ⟨hs, hc⟩
  · have hr : Odd r := Int.odd_iff.mpr (by rw [Int.ModEq] at hc; rcases hε with rfl | rfl <;> lia)
    have := vSeq_modEq_add_two_mul hr hs hn
    rw [Int.ModEq] at this hc
    rcases hε with rfl | rfl <;> lia
  · have hr : Even r := Int.even_iff.mpr <| by
      rw [Int.ModEq] at hc
      rcases hε with rfl | rfl <;> lia [Int.odd_iff.mp hs]
    have := vSeq_modEq_two_mul_add hr hs hn
    rw [Int.ModEq] at this hc
    rcases hε with rfl | rfl <;> lia
  · have := vSeq_modEq_of_even hrs hs hn
    rw [Int.ModEq] at this hc
    rcases hε with rfl | rfl <;> lia

/-- An odd prime dividing `v_n` (`n ≥ 2`) does not divide `r`: `v_n ≡ 2 s^{2^n - 1} (mod r)`. -/
theorem not_dvd_left_of_dvd_vSeq (hrs : IsCoprime r s) {n : ℕ} (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpv : (p : ℤ) ∣ vSeq r s n) : ¬(p : ℤ) ∣ r := fun hpr ↦ by
  have hp' := Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd (((vSeq_modEq_left r s hn).of_dvd hpr).dvd_iff.mp hpv) with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (mod_cast h))
  · exact hp'.not_isUnit (hrs.isUnit_of_dvd' hpr (hp'.dvd_of_dvd_pow h))

/-- **The `2`-adic condition** (Lemma 4.4 of the draft): for `a = r/s ∈ 𝒜` with sign `ε` in one of
the classes (C1)–(C3), every `v_n`, `n ≥ 2`, has a prime factor `p ≡ 3 (mod 4)` not dividing `r`:
`ε v_n > 0` is `≡ 3 (mod 4)` or `≡ 6 (mod 8)`, and `v_n ≡ 2 s^{2^n - 1} (mod r)`. -/
theorem exists_prime_dvd_vSeq_of_twoAdicClass (hrs : IsCoprime r s) (hs : 0 < s) (hr0 : r ≠ 0)
    {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq r s n ∧ ¬(p : ℤ) ∣ r := by
  have hpos := mul_vSeq_pos hs hr0 hε hn
  have hε1 : ε = 1 ∨ ε = -1 := by rcases hε with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  obtain ⟨p, hp, hp4, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ ε * vSeq r s n := by
    rcases emod_of_twoAdicClass hrs hε1 hc hn with h | h
    exacts [Int.exists_prime_dvd_of_emod_four_eq_three hpos h,
      Int.exists_prime_dvd_of_emod_eight_eq_six hpos h]
  have hpv : (p : ℤ) ∣ vSeq r s n := by rcases hε1 with rfl | rfl <;> simpa using hpd
  exact ⟨p, hp, hp4, hpv, not_dvd_left_of_dvd_vSeq hrs hn hp (by lia) hpv⟩

/-! ### `u_n` at odd levels for `a ≡ 1 mod 4` -/

/-- `u_n > 0` when `c_n² - c_n + a + 1 > 0` at `a = r/s`, `s > 0`. -/
theorem uSeq_pos (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n)
    (h : 0 < cSeq ((r : ℚ) / s) n ^ 2 - cSeq ((r : ℚ) / s) n + (r : ℚ) / s + 1) :
    0 < uSeq r s n := by
  have hu := intCast_uSeq r (mul_inv_cancel₀ (mod_cast hs.ne' : (s : ℚ) ≠ 0)) hn
  rw [← div_eq_mul_inv] at hu
  have : (0 : ℚ) < uSeq r s n := by
    rw [hu]
    exact mul_pos (pow_pos (mod_cast hs) _) h
  exact_mod_cast this

/-- For odd `s` and `r ≡ s (mod 4)` (`a ≡ 1 mod 4`), `u_n ≡ 6 (mod 8)` for odd `n ≥ 3`. -/
theorem uSeq_emod_eight_of_odd (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) {n : ℕ} (hn : 3 ≤ n)
    (ho : Odd n) : uSeq r s n % 8 = 6 := by
  obtain ⟨j, rfl⟩ := ho
  have hX := intCast_mul_wSeq_zmod_eight r hs (n := 2 * j + 1) (by lia)
  rw [cSeq_two_mul_add_one_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) (by lia)] at hX
  have h : (uSeq r s (2 * j + 1) : ZMod 8) = 6 := by
    rw [show uSeq r s (2 * j + 1) = (r * wSeq r s (2 * j + 1)) ^ 2 -
      r * wSeq r s (2 * j + 1) * s ^ 2 ^ (2 * j) + (r + s) * s ^ (2 ^ (2 * j + 1) - 1) by
        rw [uSeq, Nat.add_sub_cancel]; ring]
    push_cast
    rw [← Int.cast_mul, hX, ZMod.intCast_pow_two_pow_eight_of_odd hs (by lia),
      ZMod.intCast_pow_two_pow_sub_one_eight_of_odd hs (by lia), mul_one, add_mul, ← sq,
      ZMod.intCast_sq_eight_eq_one_of_odd hs]
    rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with h | h <;> rw [h] <;> decide
  have := (ZMod.intCast_eq_intCast_iff' (uSeq r s (2 * j + 1)) 6 8).mp (mod_cast h)
  lia

/-- For odd `s` and `r ≡ s (mod 4)` (`a ≡ 1 mod 4`), `r w_n ≡ 2 (mod 4)` for even `n ≥ 2`:
modulo `8` it is `c̄_n = a + 1` with `a ∈ {1, 5}`. -/
theorem intCast_mul_wSeq_zmod_four_of_even (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) : ((r * wSeq r s n : ℤ) : ZMod 4) = 2 := by
  obtain ⟨j, rfl⟩ := he
  rw [← two_mul] at hn ⊢
  have h := intCast_mul_wSeq_zmod_eight r hs hn
  rw [cSeq_two_mul_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) (by lia)] at h
  have h' := congr(ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) $h)
  rw [map_intCast] at h'
  rw [h']
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with ha | ha <;> rw [ha] <;> decide

/-- For `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`) and odd `n ≥ 3` with `u_n > 0`, a prime
`p ≡ 3 (mod 4)` divides `u_n` and not `r + s`: `u_n ≡ 6 (mod 8)`, and `u_n ≡ 2 s^{2^n} (mod r + s)`
(`QuadraticIterates.uSeq_two_mul_add_one_modEq`). -/
theorem exists_prime_dvd_uSeq_of_odd (hrs : IsCoprime r s) (hs : Odd s) (h4 : r ≡ s [ZMOD 4])
    {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) (hpos : 0 < uSeq r s n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq r s n ∧ ¬(p : ℤ) ∣ r + s := by
  obtain ⟨p, hp, hp4, hpu⟩ :=
    Int.exists_prime_dvd_of_emod_eight_eq_six hpos (uSeq_emod_eight_of_odd hs h4 hn ho)
  refine ⟨p, hp, hp4, hpu, fun hprs ↦ ?_⟩
  obtain ⟨k, rfl⟩ := ho
  have hp' := Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd (((uSeq_two_mul_add_one_modEq hrs (by lia)).of_dvd hprs).dvd_iff.mp
    hpu) with h | h
  · have := Int.le_of_dvd two_pos h
    lia
  · have hps := hp'.dvd_of_dvd_pow h
    exact hp'.not_isUnit (hrs.isUnit_of_dvd' ((dvd_add_left hps).mp hprs) hps)

end QuadraticIterates
