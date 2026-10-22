/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Sequence.WSeq

import Mathlib.RingTheory.Int.Basic
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
(C1)–(C3) this gives every `v_n`, `n ≥ 2`, a prime factor `p ≡ 3 (mod 4)` not dividing `r`,
which is what reflection at level `n` needs. Likewise, for `a ≡ 1 mod 4` and odd `n ≥ 3`, a
positive `u_n` (`QuadraticIterates.uSeq`) is `≡ 6 (mod 8)` and has a prime factor `p ≡ 3 (mod 4)`
not dividing `r + s`, which is what period two at level `n` needs.

## Main definitions

* `QuadraticIterates.TwoAdicClass r s ε`: the classes (C1)–(C3).

## Main statements

* `QuadraticIterates.mul_vSeq_pos`: `ε v_n > 0`.
* `QuadraticIterates.vSeq_modEq_add_two_mul`, `QuadraticIterates.vSeq_modEq_two_mul_add`,
  `QuadraticIterates.vSeq_modEq_of_even`: the residues of `v_n`; the first one from
  `QuadraticIterates.cSeq_add_cSeq_succ_zmod_eight`, `c_n + c_{n+1} = -1` for odd `a` in `ZMod 8`.
* `QuadraticIterates.exists_prime_dvd_vSeq_of_twoAdicClass`: the prime factor.
* `QuadraticIterates.exists_prime_dvd_uSeq_of_odd`: the prime factor of `u_n`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- For odd `a` in `ZMod 8` (`a² = 1`), the sequence is `2`-periodic from `n = 2` on. -/
private lemma cSeq_four_eq_two_zmod_eight {a : ZMod 8} (ha : a ^ 2 = 1) :
    cSeq a (2 + 2) = cSeq a 2 := by
  rw [cSeq_succ a (by norm_num), cSeq_succ a (by norm_num), cSeq_two]
  decide +revert

/-- For `a² = 1` in `ZMod 8`, that is, for odd `a`, `c_n + c_{n+1} = -1` for `n ≥ 2`: the
sequence is `2`-periodic from `n = 2` on, and `c_2 + c_3 = -1`. -/
theorem cSeq_add_cSeq_succ_zmod_eight {a : ZMod 8} (ha : a ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    cSeq a n + cSeq a (n + 1) = -1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [cSeq_succ a (n := 2) (by norm_num), cSeq_two]
    decide +revert
  | succ n hn ih =>
    rwa [cSeq_add_eq_of_add_eq (by norm_num) (cSeq_four_eq_two_zmod_eight ha) hn, add_comm]

/-- For odd `r` and `s`, `v_n ≡ r + 2s (mod 4)` for `n ≥ 2`: modulo `8`, `r v_n = c̄_n + c̄_{n+1}`
for the sequence `c̄` of the odd parameter `rs`, which is `-1`
(`QuadraticIterates.cSeq_add_cSeq_succ_zmod_eight`), so `v_n ≡ -r`. -/
theorem vSeq_modEq_add_two_mul (hr : Odd r) (hs : Odd s) {n : ℕ} (hn : 2 ≤ n) :
    vSeq r s n ≡ r + 2 * s [ZMOD 4] := by
  have hr2 := ZMod.intCast_sq_eight_eq_one_of_odd hr
  have hs2 := ZMod.intCast_sq_eight_eq_one_of_odd hs
  have h := intCast_mul_vSeq r (by rwa [← sq] : (s : ZMod 8) * s = 1) (by lia : 1 ≤ n)
  rw [ZMod.intCast_pow_two_pow_eight_of_odd hs (by lia), one_mul,
    cSeq_add_cSeq_succ_zmod_eight (by rw [mul_pow, hr2, hs2, one_mul]) hn] at h
  have h8 : vSeq r s n ≡ -r [ZMOD 8] := (ZMod.intCast_eq_intCast_iff _ _ 8).mp <| by
    push_cast
    linear_combination (r : ZMod 8) * h - (vSeq r s n : ZMod 8) * hr2
  rw [Int.ModEq] at h8 ⊢
  lia [Int.odd_iff.mp hr, Int.odd_iff.mp hs]

/-- For even `r` and odd `s`, `w_m ≡ r + s (mod 8)` for `m ≥ 2`: `w_{m+1} ≡ r w_m² + s` and
`(r + s)² ≡ 1 (mod 8)`. -/
theorem intCast_wSeq_zmod_eight_of_even_left (hr : Even r) (hs : Odd s) {m : ℕ}
    (hm : 2 ≤ m) : (wSeq r s m : ZMod 8) = r + s := by
  have hsq : ((r : ZMod 8) + s) ^ 2 = 1 :=
    mod_cast ZMod.intCast_sq_eight_eq_one_of_odd (hr.add_odd hs)
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [intCast_wSeq_succ_zmod_eight_of_odd hs (by lia), ih, hsq, mul_one]

/-- For even `r` and odd `s`, `v_n ≡ 2(r + s) (mod 8)` for `n ≥ 2`: `w_n ≡ w_{n+1} ≡ r + s` and
`s^{2^{n-1}} ≡ 1 (mod 8)`. -/
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
  have hr : Odd r := Int.isCoprime_two_right.mp (hrs.of_isCoprime_of_dvd_right hs.two_dvd)
  have h4 : (4 : ℤ) ∣ s ^ 2 ^ (n - 1) :=
    (pow_dvd_pow_of_dvd hs.two_dvd 2).trans (pow_dvd_pow s (Nat.le_self_pow (by lia) 2))
  have hw := (ZMod.intCast_eq_intCast_iff _ _ 8).mp
    (mod_cast intCast_wSeq_zmod_eight_of_even hs hr (n := n + 1) (by lia))
  simpa [vSeq] using (hw.of_dvd (by norm_num : (4 : ℤ) ∣ 8)).add
    ((Int.modEq_zero_iff_dvd.mpr h4).mul_left (wSeq r s n))

/-- `r v_n = s^{2^n} (c_n + c_{n+1})` at `a = r/s`, as an identity in `ℚ`. -/
private lemma intCast_mul_vSeq_div (hs : s ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ((r * vSeq r s n : ℤ) : ℚ) =
      (s : ℚ) ^ 2 ^ n * (cSeq ((r : ℚ) / s) n + cSeq ((r : ℚ) / s) (n + 1)) := by
  push_cast
  rw [div_eq_mul_inv]
  exact intCast_mul_vSeq r (mul_inv_cancel₀ (mod_cast hs)) hn

/-- For `r ≤ -2s` and `s > 0`, `-w_n ≥ s^{2^{n-1} - 1}` (`n ≥ 1`): `c_n = r w_n / s^{2^{n-1}}` is
at least `-r/s`. -/
theorem pow_le_neg_wSeq (hs : 0 < s) (h : r ≤ -2 * s) {n : ℕ} (hn : 1 ≤ n) :
    s ^ (2 ^ (n - 1) - 1) ≤ -wSeq r s n := by
  have hs' : (0 : ℚ) < s := mod_cast hs
  have hc := neg_le_cSeq_of_le_neg_two (a := (r : ℚ) / s) ((div_le_iff₀ hs').mpr (mod_cast h)) hn
  rw [cSeq_div_eq r hs.ne' hn, neg_div', div_le_div_iff₀ hs' (by positivity),
    ← Nat.sub_add_cancel (Nat.one_le_two_pow (n := n - 1)), pow_succ] at hc
  have hr : (0 : ℚ) < -r * s := mul_pos (neg_pos.mpr (mod_cast (by lia : r < 0))) hs'
  have : (s : ℚ) ^ (2 ^ (n - 1) - 1) ≤ -wSeq r s n := by
    refine le_of_mul_le_mul_left ?_ hr
    linear_combination hc
  exact_mod_cast this

/-- For `r ≤ -2s`, i.e. `a = r/s ≤ -2`, `v_n < 0`: `w_n, w_{n+1} < 0`
(`QuadraticIterates.pow_le_neg_wSeq`). -/
theorem vSeq_neg_of_le_neg_two_mul (hs : 0 < s) (h : r ≤ -2 * s) {n : ℕ} (hn : 1 ≤ n) :
    vSeq r s n < 0 :=
  add_neg (by lia [pow_le_neg_wSeq hs h (n := n + 1) (by lia), pow_pos hs (2 ^ (n + 1 - 1) - 1)])
    (mul_neg_of_neg_of_pos (by lia [pow_le_neg_wSeq hs h hn, pow_pos hs (2 ^ (n - 1) - 1)])
      (by positivity))

/-- For `r > 0` and `s > 0`, `v_n > 0` for `n ≥ 2`: `r v_n = s^{2^n} (c_n + c_{n+1})` with
`c_n, c_{n+1} > 0`. -/
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
  have hs' : (0 : ℚ) < s := mod_cast hs
  have hα : 0 < ((r : ℚ) / s) ^ 3 + 2 * ((r : ℚ) / s) ^ 2 + 2 * ((r : ℚ) / s) + 2 :=
    (div_pos (mod_cast h : (0 : ℚ) < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
      (pow_pos hs' 3)).trans_eq (by field)
  have hrv : ((r * vSeq r s n : ℤ) : ℚ) < 0 := by
    rw [intCast_mul_vSeq_div hs.ne' (by lia)]
    exact mul_neg_of_pos_of_neg (by positivity)
      (cSeq_add_cSeq_succ_neg _ (div_neg_of_neg_of_pos (mod_cast hr) hs') hα hn)
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

/-- An odd prime dividing `x ≡ 2 t^k (mod m)`, with `m` prime to `t`, does not divide `m`. -/
private lemma not_dvd_of_modEq_two_mul_pow {m t x : ℤ} (hmt : IsCoprime m t) {k : ℕ}
    (hx : x ≡ 2 * t ^ k [ZMOD m]) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpx : (p : ℤ) ∣ x) :
    ¬(p : ℤ) ∣ m := fun hpm ↦ by
  have hp' := Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd ((hx.of_dvd hpm).dvd_iff.mp hpx) with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (mod_cast h))
  · exact hp'.not_isUnit (hmt.isUnit_of_dvd' hpm (hp'.dvd_of_dvd_pow h))

/-- An odd prime dividing `v_n` (`n ≥ 2`) does not divide `r`: `v_n ≡ 2 s^{2^n - 1} (mod r)`. -/
theorem not_dvd_left_of_dvd_vSeq (hrs : IsCoprime r s) {n : ℕ} (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpv : (p : ℤ) ∣ vSeq r s n) : ¬(p : ℤ) ∣ r :=
  not_dvd_of_modEq_two_mul_pow hrs (vSeq_modEq_left r s hn) hp hp2 hpv

/-- **The `2`-adic condition**: for `a = r/s ∈ 𝒜` with sign `ε` (`a ≤ -2` and `ε = -1`, or
`a³ + 2a² + 2a + 2 > 0` and `ε = 1`) in one of the classes (C1)–(C3), every `v_n`, `n ≥ 2`, has a
prime factor `p ≡ 3 (mod 4)` not dividing `r`: `ε v_n > 0` is `≡ 3 (mod 4)` or `≡ 6 (mod 8)`, and
`v_n ≡ 2 s^{2^n - 1} (mod r)`. -/
theorem exists_prime_dvd_vSeq_of_twoAdicClass (hrs : IsCoprime r s) (hs : 0 < s) (hr0 : r ≠ 0)
    {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq r s n ∧ ¬(p : ℤ) ∣ r := by
  have hpos := mul_vSeq_pos hs hr0 hε hn
  have hε1 : ε = 1 ∨ ε = -1 := hε.symm.imp And.right And.right
  obtain ⟨p, hp, hp4, hpd⟩ := (emod_of_twoAdicClass hrs hε1 hc hn).elim
    (Int.exists_prime_dvd_of_emod_four_eq_three hpos)
    (Int.exists_prime_dvd_of_emod_eight_eq_six hpos)
  have hpv := (Int.isUnit_iff.mpr hε1).dvd_mul_left.mp hpd
  exact ⟨p, hp, hp4, hpv, not_dvd_left_of_dvd_vSeq hrs hn hp (by lia) hpv⟩

/-! ### `u_n` at odd levels for `a ≡ 1 mod 4` -/

/-- `u_n > 0` when `c_n² - c_n + a + 1 > 0` at `a = r/s`, `s > 0`, as
`u_n = s^{2^n} (c_n² - c_n + a + 1)` (`QuadraticIterates.intCast_uSeq`). -/
theorem uSeq_pos (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n)
    (h : 0 < cSeq ((r : ℚ) / s) n ^ 2 - cSeq ((r : ℚ) / s) n + (r : ℚ) / s + 1) :
    0 < uSeq r s n := by
  have hu := intCast_uSeq r (mul_inv_cancel₀ (mod_cast hs.ne' : (s : ℚ) ≠ 0)) hn
  rw [← div_eq_mul_inv] at hu
  exact (Int.cast_pos (R := ℚ)).mp (hu ▸ mul_pos (pow_pos (mod_cast hs) _) h)

/-- For odd `s` and `r ≡ s (mod 4)` (`a ≡ 1 mod 4`), `u_n ≡ 6 (mod 8)` for odd `n ≥ 3`: modulo `8`,
`u_n = c̄_n² - c̄_n + a + 1` with `c̄_n = a + 4` and `a = rs ∈ {1, 5}`. -/
theorem uSeq_emod_eight_of_odd (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) {n : ℕ} (hn : 3 ≤ n)
    (ho : Odd n) : uSeq r s n % 8 = 6 := by
  obtain ⟨j, rfl⟩ := ho
  have hu := intCast_uSeq r (by rw [← sq, ZMod.intCast_sq_eight_eq_one_of_odd hs] :
    (s : ZMod 8) * s = 1) (n := 2 * j + 1) (by lia)
  rw [ZMod.intCast_pow_two_pow_eight_of_odd hs (by lia), one_mul,
    cSeq_two_mul_add_one_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) (by lia)] at hu
  refine (ZMod.intCast_eq_intCast_iff' _ 6 8).mp ?_
  rw [hu]
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with h | h <;> rw [h] <;> decide

/-- For odd `s` and `r ≡ s (mod 4)` (`a ≡ 1 mod 4`), `r w_n ≡ 2 (mod 4)` for even `n ≥ 2`:
modulo `8` it is `c̄_n = a + 1` with `a ∈ {1, 5}`. -/
theorem intCast_mul_wSeq_zmod_four_of_even (hs : Odd s) (h4 : r ≡ s [ZMOD 4]) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) : ((r * wSeq r s n : ℤ) : ZMod 4) = 2 := by
  obtain ⟨j, rfl⟩ := he
  rw [← two_mul] at hn ⊢
  have h := intCast_mul_wSeq_zmod_eight r hs hn
  rw [cSeq_two_mul_zmod_eight (intCast_mul_zmod_eight_of_modEq_four hs h4) (by lia)] at h
  rw [← map_intCast (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)), h]
  rcases intCast_mul_zmod_eight_of_modEq_four hs h4 with ha | ha <;> rw [ha] <;> decide

/-- For `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`) and odd `n ≥ 3` with `u_n > 0`, a prime
`p ≡ 3 (mod 4)` divides `u_n` and not `r + s`: `u_n ≡ 6 (mod 8)`, and `u_n ≡ 2 s^{2^n} (mod r + s)`
(`QuadraticIterates.uSeq_two_mul_add_one_modEq`). -/
theorem exists_prime_dvd_uSeq_of_odd (hrs : IsCoprime r s) (hs : Odd s) (h4 : r ≡ s [ZMOD 4])
    {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) (hpos : 0 < uSeq r s n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq r s n ∧ ¬(p : ℤ) ∣ r + s := by
  obtain ⟨p, hp, hp4, hpu⟩ :=
    Int.exists_prime_dvd_of_emod_eight_eq_six hpos (uSeq_emod_eight_of_odd hs h4 hn ho)
  obtain ⟨k, rfl⟩ := ho
  exact ⟨p, hp, hp4, hpu, not_dvd_of_modEq_two_mul_pow (by simpa using hrs.add_mul_left_left 1)
    (uSeq_two_mul_add_one_modEq hrs (by lia)) hp (by lia) hpu⟩

end QuadraticIterates
