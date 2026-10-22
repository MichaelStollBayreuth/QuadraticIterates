/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import QuadraticIterates.Sequence.WSeq

import Mathlib.Algebra.Field.ZMod
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Mathlib.RingTheory.Int.Basic
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.Signs

/-!
# Vanishing terms and `p`-adic valuations along `(c_n)`

For `a ∈ ℚ`, some `c_n` with `n ≥ 1` vanishes exactly for `a ∈ {0, -1}`. For a prime `p` and
`a ∉ {0, -1}`, the valuations `v_p(c_n)` follow one of three shapes: all zero; a fixed positive
value exactly at the multiples of some `m ≥ 1`; or `2^{n-1} v_p(a)` with `v_p(a) < 0`. For
`a = r/s` with `p ∤ s` the valuations are those of `r w_n`; at `p ∣ r` they are constant, and at
`p ∤ rs` the divisibility of `w_n` by `p` is rigid, `p ∣ w_n ↔ m ∣ n` for the first index `m` with
`p ∣ w_m`.

## Main statements

* `QuadraticIterates.cSeq_ne_zero`, `QuadraticIterates.exists_cSeq_eq_zero_iff`: the vanishing
  terms.
* `QuadraticIterates.padicValRat_cSeq_trichotomy`: the three shapes of `n ↦ v_p(c_n)`.
* `QuadraticIterates.padicValRat_cSeq_of_padicValRat_neg`,
  `QuadraticIterates.padicValRat_cSeq_of_dvd_left`, `QuadraticIterates.padicValRat_cSeq_eq_ite`:
  the three cases.
* `QuadraticIterates.padicValRat_cSeq_eq_padicValInt`: `v_p(c_n) = v_p(r w_n)` at a prime `p ∤ s`.
* `QuadraticIterates.dvd_wSeq_iff`, `QuadraticIterates.padicValInt_wSeq_eq_ite`: rigid
  divisibility of `(w_n)` at a prime `p ∤ rs`, and the valuations `v_p(w_n)`.
-/

@[expose] public section

namespace QuadraticIterates

variable {p : ℕ} [Fact p.Prime]

/-- If `v_p(a) < 0`, then `v_p(c_n) = 2^{n-1} v_p(a)` for `n ≥ 1`: `v_p(c_n²) < v_p(a)`, so the
valuation doubles at each step. -/
theorem padicValRat_cSeq_of_padicValRat_neg {a : ℚ} (ha : padicValRat p a < 0) {n : ℕ}
    (hn : 1 ≤ n) : padicValRat p (cSeq a n) = 2 ^ (n - 1) * padicValRat p a := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hc : cSeq a n ^ 2 ≠ 0 := pow_ne_zero 2 fun h ↦ by simp [h, ha.ne] at ih
    have hpow : (2 : ℤ) ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn, Nat.add_sub_cancel]
    have hlt : padicValRat p (cSeq a n ^ 2) < padicValRat p a := by
      rw [padicValRat.pow, ih]
      push_cast
      lia [mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (one_le_pow₀ (M₀ := ℤ) (n := n - 1) one_le_two)) ha.le]
    rw [cSeq_succ a hn, padicValRat.add_eq_of_lt (fun h ↦ ?_) hc ha0 hlt, padicValRat.pow, ih,
      hpow]
    · push_cast; ring
    · rw [eq_neg_of_add_eq_zero_left h, padicValRat.neg] at hlt
      exact hlt.false

/-- A prime `q` dividing the denominator of `a` has `v_q(a) < 0`, as it does not divide the
numerator. -/
private lemma padicValRat_neg_of_dvd_den {q : ℕ} [Fact q.Prime] {a : ℚ} (h : q ∣ a.den) :
    padicValRat q a < 0 := by
  have h1 := one_le_padicValNat_of_dvd a.den_nz h
  rw [padicValRat_def, (a.num_or_den_zero_padicVal Fact.out).resolve_right (by lia)]
  lia

/-- For `a ∈ ℚ \ {-1, 0}`, no term `c_n` with `n ≥ 1` vanishes. A prime of the denominator gives
`v_p(c_n) < 0` (`QuadraticIterates.padicValRat_cSeq_of_padicValRat_neg`); an integral `a` has
`a > 0` or `a ≤ -2`, where `QuadraticIterates.cSeq_pos_of_pos` and
`QuadraticIterates.neg_le_cSeq_of_le_neg_two` give the signs. -/
theorem cSeq_ne_zero {a : ℚ} (h₀ : a ≠ 0) (h₁ : a ≠ -1) {n : ℕ} (hn : 1 ≤ n) : cSeq a n ≠ 0 := by
  by_cases hd : a.den = 1
  · rw [← Rat.coe_int_num_of_den_eq_one hd] at h₀ h₁ ⊢
    rcases (by lia [(mod_cast h₀ : a.num ≠ 0), (mod_cast h₁ : a.num ≠ -1)] :
      0 < a.num ∨ a.num ≤ -2) with h | h
    · rcases hn.eq_or_lt with rfl | hn
      · simpa using h₀
      · exact (cSeq_pos_of_pos (mod_cast h) hn).ne'
    · refine (lt_of_lt_of_le ?_ (neg_le_cSeq_of_le_neg_two (mod_cast h) hn)).ne'
      exact neg_pos.mpr (mod_cast h.trans_lt (by norm_num))
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
    have := Fact.mk hq
    have hv := padicValRat_neg_of_dvd_den hqd
    exact fun h ↦ by simpa [h, hv.ne] using padicValRat_cSeq_of_padicValRat_neg hv hn

/-- For `a ∈ ℚ`, some term `c_n` with `n ≥ 1` vanishes iff `a ∈ {0, -1}`, where `c_1 = 0`,
resp. `c_2 = 0`. -/
theorem exists_cSeq_eq_zero_iff {a : ℚ} : (∃ n ≥ 1, cSeq a n = 0) ↔ a = 0 ∨ a = -1 := by
  refine ⟨fun ⟨n, hn, h⟩ ↦ or_iff_not_and_not.mpr fun ⟨h₀, h₁⟩ ↦ cSeq_ne_zero h₀ h₁ hn h, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨1, le_rfl, by simp⟩
  · exact ⟨2, by norm_num, by norm_num [cSeq_two]⟩

section Integral

variable {r s : ℤ}

/-- At a prime `p ∤ s`, `v_p(c_n) = v_p(r w_n)`: `c_n = r w_n / s^{2^{n-1}}`. -/
theorem padicValRat_cSeq_eq_padicValInt (hs : s ≠ 0) (hps : ¬(p : ℤ) ∣ s) {n : ℕ} (hn : 1 ≤ n) :
    padicValRat p (cSeq ((r : ℚ) / s) n) = padicValInt p (r * wSeq r s n) := by
  rw [cSeq_div_eq r hs hn, ← Int.cast_mul]
  rcases eq_or_ne (r * wSeq r s n) 0 with h | h
  · simp [h]
  · rw [padicValRat.div (mod_cast h) (pow_ne_zero _ (mod_cast hs)), padicValRat.pow,
      padicValRat.of_int, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hps]
    simp

private lemma two_le_of_dvd_wSeq {m : ℕ} (hm : 1 ≤ m) (hpm : (p : ℤ) ∣ wSeq r s m) : 2 ≤ m :=
  hm.lt_of_ne fun h ↦ (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_one (by simpa [← h] using hpm)

/-- **Rigid divisibility of `(w_n)`** at a prime `p ∤ rs`: if `m ≥ 1` is the first index with
`p ∣ w_m`, then `p ∣ w_n ↔ m ∣ n` for `n ≥ 1`. Modulo `p`, `r w_n = s^{2^{n-1}} c̄_n`, and `0` is
periodic of exact period `m` (`QuadraticIterates.cSeq_eq_zero_iff_dvd`). -/
theorem dvd_wSeq_iff (hpr : ¬(p : ℤ) ∣ r) (hps : ¬(p : ℤ) ∣ s) {m : ℕ} (hm : 1 ≤ m)
    (hpm : (p : ℤ) ∣ wSeq r s m) (hmin : ∀ j ≥ 1, j < m → ¬(p : ℤ) ∣ wSeq r s j) {n : ℕ}
    (hn : 1 ≤ n) : (p : ℤ) ∣ wSeq r s n ↔ m ∣ n := by
  obtain ⟨σ, hσ⟩ := (ZMod.isUnit_intCast_of_not_dvd (pow_one p).symm hps).exists_right_inv
  have hr0 : (r : ZMod p) ≠ 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mp hpr
  have hs0 : (s : ZMod p) ≠ 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hps
  have key (j : ℕ) (hj : 1 ≤ j) : (p : ℤ) ∣ wSeq r s j ↔ cSeq ((r : ZMod p) * σ) j = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← mul_right_inj' hr0, mul_zero,
      intCast_mul_wSeq r hσ hj, mul_eq_zero, or_iff_right (pow_ne_zero _ hs0)]
  rw [key n hn]
  exact cSeq_eq_zero_iff_dvd hm ((key m hm).mp hpm)
    (mul_ne_zero hr0 (right_ne_zero_of_mul_eq_one hσ))
    (fun j hj hjm h ↦ hmin j hj hjm ((key j hj).mpr h)) hn

/-- At a prime `p ∤ rs`, with `m ≥ 1` the first index with `p ∣ w_m ≠ 0`: `v_p(w_n) = v_p(w_m)`
if `m ∣ n`, and `0` otherwise. For `n = mk`, `w_{mk} = w_m T` with `T` prime to `p`
(`QuadraticIterates.exists_wSeq_mul_eq`). -/
theorem padicValInt_wSeq_eq_ite (hrs : IsCoprime r s) (hpr : ¬(p : ℤ) ∣ r) (hps : ¬(p : ℤ) ∣ s)
    {m : ℕ} (hm : 1 ≤ m) (hpm : (p : ℤ) ∣ wSeq r s m)
    (hmin : ∀ j ≥ 1, j < m → ¬(p : ℤ) ∣ wSeq r s j) (hw : wSeq r s m ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) :
    padicValInt p (wSeq r s n) = if m ∣ n then padicValInt p (wSeq r s m) else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    obtain ⟨T, hT, hTm⟩ := exists_wSeq_mul_eq hrs (two_le_of_dvd_wSeq hm hpm)
      (Nat.pos_of_mul_pos_left hn)
    have hpT : ¬(p : ℤ) ∣ T := fun h ↦ hps <| (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow
      ((hTm.of_dvd hpm).dvd_iff.mp h)
    rw [hT, padicValInt.mul hw (by rintro rfl; exact hpT (dvd_zero _)),
      padicValInt.eq_zero_of_not_dvd hpT, add_zero]
  · exact padicValInt.eq_zero_of_not_dvd fun h' ↦ h ((dvd_wSeq_iff hpr hps hm hpm hmin hn).mp h')

/-- At a prime `p ∣ r`, `v_p(c_n) = v_p(r)` for all `n ≥ 1`: `w_n` is prime to `r`, and `p ∤ s`. -/
theorem padicValRat_cSeq_of_dvd_left (hrs : IsCoprime r s) (hs : s ≠ 0) (hr : r ≠ 0)
    (hpr : (p : ℤ) ∣ r) {n : ℕ} (hn : 1 ≤ n) :
    padicValRat p (cSeq ((r : ℚ) / s) n) = padicValInt p r := by
  have hpw : ¬(p : ℤ) ∣ wSeq r s n :=
    Int.Prime.not_dvd_of_isCoprime Fact.out (isCoprime_wSeq_left hrs hn) hpr
  rw [padicValRat_cSeq_eq_padicValInt hs (Int.Prime.not_dvd_of_isCoprime Fact.out hrs.symm hpr) hn,
    padicValInt.mul hr (b := wSeq r s n) fun h ↦ hpw (h ▸ dvd_zero _),
    padicValInt.eq_zero_of_not_dvd hpw, add_zero]

/-- At a prime `p ∤ rs`, with `m ≥ 1` the first index with `p ∣ w_m ≠ 0`: `v_p(c_n) = v_p(w_m)`
if `m ∣ n`, and `0` otherwise (`QuadraticIterates.padicValInt_wSeq_eq_ite`). -/
theorem padicValRat_cSeq_eq_ite (hrs : IsCoprime r s) (hs : s ≠ 0) (hpr : ¬(p : ℤ) ∣ r)
    (hps : ¬(p : ℤ) ∣ s) {m : ℕ} (hm : 1 ≤ m) (hpm : (p : ℤ) ∣ wSeq r s m)
    (hmin : ∀ j ≥ 1, j < m → ¬(p : ℤ) ∣ wSeq r s j) (hw : wSeq r s m ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) : padicValRat p (cSeq ((r : ℚ) / s) n) =
      if m ∣ n then (padicValInt p (wSeq r s m) : ℤ) else 0 := by
  have h := padicValInt_wSeq_eq_ite hrs hpr hps hm hpm hmin hw hn
  rw [padicValRat_cSeq_eq_padicValInt hs hps hn]
  rcases eq_or_ne (wSeq r s n) 0 with h0 | h0
  · split_ifs at h ⊢ <;> simp_all
  · rw [padicValInt.mul (by rintro rfl; exact hpr (dvd_zero _)) h0,
      padicValInt.eq_zero_of_not_dvd hpr, zero_add, h]
    split_ifs <;> rfl

/-- At a prime `p ∤ s`, for `a = r/s ∉ {0, -1}`: `v_p(c_n) = v_p(r) > 0` for all `n ≥ 1` if
`p ∣ r`; otherwise either all `v_p(c_n)` vanish, or `v_p(c_n) = v_p(w_m) > 0` exactly for the
multiples `n` of the first index `m` with `p ∣ w_m`. -/
private lemma padicValRat_cSeq_of_not_dvd (hrs : IsCoprime r s) (hs : s ≠ 0) (hps : ¬(p : ℤ) ∣ s)
    (h₀ : (r : ℚ) / s ≠ 0) (h₁ : (r : ℚ) / s ≠ -1) :
    (∀ n ≥ 1, padicValRat p (cSeq ((r : ℚ) / s) n) = 0) ∨ ∃ m ≥ 1, ∃ e ≥ 1, ∀ n ≥ 1,
      padicValRat p (cSeq ((r : ℚ) / s) n) = if m ∣ n then e else 0 := by
  have hr : r ≠ 0 := by rintro rfl; simp at h₀
  have hw (n : ℕ) (hn : 1 ≤ n) : wSeq r s n ≠ 0 := fun h ↦
    cSeq_ne_zero h₀ h₁ hn (by rw [cSeq_div_eq r hs hn, h]; simp)
  have hval {x : ℤ} (hx : x ≠ 0) (h : (p : ℤ) ∣ x) : 1 ≤ padicValInt p x :=
    ((padicValInt_dvd_iff 1 x).mp (by simpa using h)).resolve_left hx
  by_cases hpr : (p : ℤ) ∣ r
  · refine .inr ⟨1, le_rfl, padicValInt p r, mod_cast hval hr hpr, fun n hn ↦ ?_⟩
    rw [padicValRat_cSeq_of_dvd_left hrs hs hr hpr hn]
    simp
  by_cases hex : ∃ n, 1 ≤ n ∧ (p : ℤ) ∣ wSeq r s n
  · obtain ⟨hm, hpm⟩ := Nat.find_spec hex
    exact .inr ⟨_, hm, _, mod_cast hval (hw _ hm) hpm, fun n hn ↦ padicValRat_cSeq_eq_ite hrs hs
      hpr hps hm hpm (fun j hj hjm h ↦ Nat.find_min hex hjm ⟨hj, h⟩) (hw _ hm) hn⟩
  · refine .inl fun n hn ↦ ?_
    rw [padicValRat_cSeq_eq_padicValInt hs hps hn, padicValInt.mul hr (hw n hn),
      padicValInt.eq_zero_of_not_dvd hpr, padicValInt.eq_zero_of_not_dvd fun h ↦ hex ⟨n, hn, h⟩]
    rfl

end Integral

/-- **The `p`-adic valuations along `(c_n)`**: for `a ∈ ℚ \ {-1, 0}` and a prime `p`, either all
`v_p(c_n)` vanish; or, for some `m ≥ 1` and `e ≥ 1`, `v_p(c_n) = e` for the multiples `n` of `m`
and `v_p(c_n) = 0` otherwise; or `v_p(c_n) = 2^{n-1} e` with `e < 0` (then `e = v_p(a)`). The
cases are distinguished by `v_p(a) < 0` and, for `a = r/s` with `p ∤ s`, by whether `p` divides
some `r w_n` (`QuadraticIterates.padicValRat_cSeq_of_dvd_left`,
`QuadraticIterates.padicValRat_cSeq_eq_ite`). -/
theorem padicValRat_cSeq_trichotomy {a : ℚ} (h₀ : a ≠ 0) (h₁ : a ≠ -1) :
    (∀ n ≥ 1, padicValRat p (cSeq a n) = 0) ∨
      (∃ m ≥ 1, ∃ e ≥ 1, ∀ n ≥ 1, padicValRat p (cSeq a n) = if m ∣ n then e else 0) ∨
      ∃ e < 0, ∀ n ≥ 1, padicValRat p (cSeq a n) = 2 ^ (n - 1) * e := by
  rcases lt_or_ge (padicValRat p a) 0 with hv | hv
  · exact .inr <| .inr ⟨_, hv, fun n hn ↦ padicValRat_cSeq_of_padicValRat_neg hv hn⟩
  obtain ⟨r, s, hrs, hps, rfl⟩ : ∃ r s : ℤ, IsCoprime r s ∧ ¬(p : ℤ) ∣ s ∧ a = r / s :=
    ⟨a.num, a.den, Int.isCoprime_iff_gcd_eq_one.mpr a.reduced,
      fun h ↦ (padicValRat_neg_of_dvd_den (Int.natCast_dvd_natCast.mp h)).not_ge hv,
      mod_cast (Rat.num_div_den a).symm⟩
  have hs : s ≠ 0 := fun h ↦ hps (h ▸ dvd_zero _)
  exact (padicValRat_cSeq_of_not_dvd hrs hs hps h₀ h₁).imp_right .inl

end QuadraticIterates
