/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Main.Theorem

import QuadraticIterates.Characters.Criterion
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.Data.ZMod
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Sequence.Orbit

/-!
# Two families

For two families of rational parameters the `2`-adic condition of the main theorem
(`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`) fails, but `x² + x + a` resp.
`x² - x + a + 1` splits over `ℚ`, and the factors of `v_n` resp. `u_n` supply primes
`p ≡ 3 (mod 4)` at every level.

## Main statements

* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`: Theorem A for rational parameters,
  `a = -j(j + 1)` with `j = u/v > 1` and `(u, v) ≡ (2, 1)` or `(3, 3) (mod 4)`.
* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`: Li's Theorem 3.9 for rational
  parameters, `a = -(ℓ² + ℓ + 1) ≤ -2` with `ℓ = u/v` and `(u, v) ≡ (1, 1)` or `(2, 3) (mod 4)`.
* `QuadraticIterates.neg_vSeq_neg_mul_add_eq`, `QuadraticIterates.uSeq_eq_mul_of_add_eq`: the
  factorizations of `v_n` resp. `u_n`.
-/

@[expose] public section

namespace QuadraticIterates

/-- `(v²)^{2^n - 1} = V²` for `V = v^{2^n - 1}`. -/
private lemma sq_pow_two_pow_sub_one (v : ℤ) (n : ℕ) :
    (v ^ 2) ^ (2 ^ n - 1) = (v ^ (2 ^ n - 1)) ^ 2 := by
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- `(v²)^{2^{n-1}} = v V` for `V = v^{2^n - 1}`, `n ≥ 1`. -/
private lemma sq_pow_two_pow (v : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (v ^ 2) ^ 2 ^ (n - 1) = v * v ^ (2 ^ n - 1) := by
  rw [← pow_mul, ← pow_succ', ← pow_succ', Nat.sub_add_cancel hn,
    Nat.sub_add_cancel Nat.one_le_two_pow]

section TheoremA

variable {u v : ℤ}

/-- For `r = -u(u + v)` and `s = v²`, `-v_n = ((u + v) W - V)(u W + V)` with `W = -w_n` and
`V = v^{2^n - 1}` (`n ≥ 1`). -/
theorem neg_vSeq_neg_mul_add_eq {n : ℕ} (hn : 1 ≤ n) :
    -vSeq (-(u * (u + v))) (v ^ 2) n =
      ((u + v) * -wSeq (-(u * (u + v))) (v ^ 2) n - v ^ (2 ^ n - 1)) *
        (u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1)) := by
  rw [vSeq, wSeq_succ _ _ hn, sq_pow_two_pow_sub_one, sq_pow_two_pow v hn]
  ring

private lemma emod_eight_of_two_one (hu : u % 4 = 2) (hv : v % 4 = 1) {n : ℕ} (hn : 2 ≤ n) :
    ((u + v) * -wSeq (-(u * (u + v))) (v ^ 2) n - v ^ (2 ^ n - 1)) % 8 = 6 := by
  have hv' : Odd v := Int.odd_iff.mpr (by lia)
  have h : (((u + v) * -wSeq (-(u * (u + v))) (v ^ 2) n - v ^ (2 ^ n - 1) : ℤ) : ZMod 8) = 6 := by
    push_cast
    rw [intCast_wSeq_zmod_eight_of_even_left
      ((Int.even_iff.mpr (by lia : u % 2 = 0)).mul_right _).neg hv'.pow hn,
      ZMod.intCast_pow_two_pow_sub_one_eight_of_odd hv' (by lia)]
    push_cast
    rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hu with h | h <;>
    rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hv with h' | h' <;>
    · rw [h, h']
      decide
  exact (ZMod.intCast_eq_intCast_iff' _ 6 8).mp (mod_cast h)

private lemma emod_eight_of_three_three (hu : u % 4 = 3) (hv : v % 4 = 3) {n : ℕ} (hn : 2 ≤ n) :
    (u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1)) % 8 = 6 := by
  have hv' : Odd v := Int.odd_iff.mpr (by lia)
  have h : ((u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1) : ℤ) : ZMod 8) = 6 := by
    push_cast
    rw [intCast_wSeq_zmod_eight_of_even_left
      ((Int.even_iff.mpr (by lia : (u + v) % 2 = 0)).mul_left u).neg hv'.pow hn,
      ZMod.intCast_pow_two_pow_sub_one_eight_of_odd hv' (by lia)]
    push_cast
    rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hu with h | h <;>
    rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hv with h' | h' <;>
    · rw [h, h']
      decide
  exact (ZMod.intCast_eq_intCast_iff' _ 6 8).mp (mod_cast h)

/-- For `a = -j(j + 1)`, `j = u/v > 1`, in the classes `(u, v) ≡ (2, 1), (3, 3) (mod 4)`, every
`v_n`, `n ≥ 2`, has a prime factor `p ≡ 3 (mod 4)`: `-v_n = F₁ F₂` with `F₁, F₂ > 0`, and `F₁`
resp. `F₂` is `≡ 6 (mod 8)`. -/
theorem exists_prime_dvd_vSeq_neg_mul_add (hv : 0 < v) (hvu : v < u)
    (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq (-(u * (u + v))) (v ^ 2) n := by
  have hW := pow_le_neg_wSeq (r := -(u * (u + v))) (pow_pos hv 2) (by nlinarith) (n := n)
    (by lia)
  rw [← pow_mul, Nat.mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by lia)] at hW
  have hV : v ^ (2 ^ n - 1) = v * v ^ (2 ^ n - 2) := by
    rw [← pow_succ', show 2 ^ n - 2 + 1 = 2 ^ n - 1 by have := Nat.one_lt_two_pow (n := n); lia]
  have hP : 0 < v ^ (2 ^ n - 2) := pow_pos hv _
  have hfac := neg_vSeq_neg_mul_add_eq (u := u) (v := v) (by lia : 1 ≤ n)
  rcases h with ⟨hu, hv4⟩ | ⟨hu, hv4⟩
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_six
      (by nlinarith [mul_le_mul_of_nonneg_left hW (by lia : 0 ≤ u + v)])
      (emod_eight_of_two_one hu hv4 hn)
    exact ⟨p, hp, hp4, dvd_neg.mp (hfac ▸ hpd.mul_right _)⟩
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_six
      (by nlinarith [mul_le_mul_of_nonneg_left hW (by lia : 0 ≤ u)])
      (emod_eight_of_three_three hu hv4 hn)
    exact ⟨p, hp, hp4, dvd_neg.mp (hfac ▸ hpd.mul_left _)⟩

private lemma emod_four_neg_mul_add (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) :
    -(u * (u + v)) % 4 = 2 := by
  have := Int.mul_emod u (u + v) 4
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rw [hu] at this <;> lia

/-- In the classes `(2, 1)` and `(3, 3)`, a prime `p ≡ 3 (mod 4)` divides `u + v` resp. `u`. -/
private lemma exists_prime_dvd_neg_mul_add (hv : 0 < v) (hvu : v < u)
    (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ -(u * (u + v)) := by
  rcases h with ⟨hu, hv4⟩ | ⟨hu, -⟩
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_four_eq_three (x := u + v)
      (by lia) (by lia)
    exact ⟨p, hp, hp4, (hpd.mul_left u).neg_right⟩
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_four_eq_three (by lia) hu
    exact ⟨p, hp, hp4, (hpd.mul_right _).neg_right⟩

/-- **Theorem A for rational parameters**: for `a = -j(j + 1)` with `j = u/v > 1`, `u, v` coprime
and `(u, v) ≡ (2, 1)` or `(3, 3) (mod 4)`, `Ω_n ≅ [C₂]ⁿ` for all `n`. Here `r = -u(u + v) ≡ 2
(mod 4)` gives `φ₀` by (Z1), a prime `p ≡ 3 (mod 4)` dividing `u + v` resp. `u` gives `φ₁`, and
`QuadraticIterates.exists_prime_dvd_vSeq_neg_mul_add` gives reflection at every level `n ≥ 2`. -/
theorem nonempty_mulEquiv_of_eq_neg_mul_add_one (huv : IsCoprime u v) (hv : 0 < v) (hvu : v < u)
    (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) (n : ℕ) :
    Nonempty (GaloisGroup (-((u : ℚ) / v * ((u : ℚ) / v + 1))) n ≃* WreathPower n) := by
  have ha : -((u : ℚ) / v * ((u : ℚ) / v + 1)) =
      ((-(u * (u + v)) : ℤ) : ℚ) / ((v ^ 2 : ℤ) : ℚ) := by
    have : (v : ℚ) ≠ 0 := mod_cast hv.ne'
    push_cast
    field
  rw [ha]
  have hrs : IsCoprime (-(u * (u + v))) (v ^ 2) :=
    (huv.mul_left (by simpa using huv.add_mul_left_left 1)).neg_left.pow_right
  have hr4 := emod_four_neg_mul_add h
  have h₀ := hasCharPattern_neg_one_of_negAllCriterion hrs (pow_pos hv 2).ne'
    (.not_isSquare (Int.not_isSquare_of_two_le_emod_four (by lia))
      (Int.not_isSquare_of_two_le_emod_four (by lia)))
  obtain ⟨p, hp, hp4, hpr⟩ := exists_prime_dvd_neg_mul_add hv hvu h
  have := Fact.mk hp
  refine forall_nonempty_mulEquiv_of_forall_dvd_vSeq hrs h₀
    (hasCharPattern_mulSingle_one_of_prime_dvd hrs (pow_pos hv 2).ne' (by lia) hp4 hpr h₀)
    (fun n hn ↦ .inl ?_) n
  obtain ⟨q, hq, hq4, hqv⟩ := exists_prime_dvd_vSeq_neg_mul_add hv hvu h hn
  exact ⟨q, hq, hq4, hqv, not_dvd_left_of_dvd_vSeq hrs hn hq (by lia) hqv⟩

end TheoremA

section Li

variable {r s u v : ℤ}

private lemma two_pow_eq {n : ℕ} (hn : 1 ≤ n) : 2 ^ n - 1 = (2 ^ (n - 1) - 1) * 2 + 1 := by
  have e : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hn]
  lia [Nat.one_le_two_pow (n := n - 1)]

/-- For `s = v²` and `r + s = -u(u + v)`, `u_n = (r w_n - (u + v) V)(r w_n + u V)` with
`V = v s^{2^{n-1} - 1} = v^{2^n - 1}` (`n ≥ 1`). -/
theorem uSeq_eq_mul_of_add_eq (hs : s = v ^ 2) (hr : r + s = -(u * (u + v))) {n : ℕ}
    (hn : 1 ≤ n) :
    uSeq r s n = (r * wSeq r s n - (u + v) * (v * s ^ (2 ^ (n - 1) - 1))) *
      (r * wSeq r s n + u * (v * s ^ (2 ^ (n - 1) - 1))) := by
  have h₁ : s ^ 2 ^ (n - 1) = s * s ^ (2 ^ (n - 1) - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  have h₂ : s ^ (2 ^ n - 1) = s * (s ^ (2 ^ (n - 1) - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_succ', two_pow_eq hn]
  rw [uSeq, h₁, h₂, hr]
  subst hs
  ring

/-- Modulo `r + s`, `-r T ≡ s^{2^{n-1} - 1}` when `T ≡ s^{2^{n-1} - 2}` (`n ≥ 2`). -/
private lemma neg_mul_modEq {T : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (hT : T ≡ s ^ (2 ^ (n - 1) - 2) [ZMOD r + s]) :
    -r * T ≡ s ^ (2 ^ (n - 1) - 1) [ZMOD r + s] := by
  have hr : -r ≡ s [ZMOD r + s] := Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  rw [show 2 ^ (n - 1) - 1 = 2 ^ (n - 1) - 2 + 1 by
    lia [Nat.le_self_pow (by lia : n - 1 ≠ 0) 2], pow_succ']
  exact hr.mul hT

/-- A prime `p` dividing `u(u + v)`, with `u, v` coprime, does not divide `v`. -/
private lemma not_dvd_right_of_dvd_mul_add (huv : IsCoprime u v) {p : ℤ} (hp : Prime p)
    (h : p ∣ u * (u + v)) : ¬p ∣ v := fun hv ↦
  hp.not_isUnit <| huv.isUnit_of_dvd' ((hp.dvd_or_dvd h).elim id fun h' ↦ by
    simpa using dvd_sub h' hv) hv

private lemma not_dvd_add_two_mul (huv : IsCoprime u v) {p : ℤ} (hp : Prime p) (hp2 : ¬p ∣ 2)
    (h : p ∣ u * (u + v)) : ¬p ∣ u + 2 * v := fun hc ↦ by
  have hv := not_dvd_right_of_dvd_mul_add huv hp h
  rcases hp.dvd_or_dvd h with hu | hu
  · rcases hp.dvd_or_dvd (by simpa using dvd_sub hc hu : p ∣ 2 * v) with h2 | h2
    exacts [hp2 h2, hv h2]
  · have := dvd_sub hc hu
    rw [show u + 2 * v - (u + v) = v by ring] at this
    exact hv this

private lemma not_dvd_sub (huv : IsCoprime u v) {p : ℤ} (hp : Prime p) (hp2 : ¬p ∣ 2)
    (h : p ∣ u * (u + v)) : ¬p ∣ u - v := fun hc ↦ by
  have hv := not_dvd_right_of_dvd_mul_add huv hp h
  rcases hp.dvd_or_dvd h with hu | hu
  · exact hv (by simpa using dvd_sub hu hc)
  · have := dvd_add hu hc
    rw [show u + v + (u - v) = 2 * u by ring] at this
    rcases hp.dvd_or_dvd this with h2 | h2
    exacts [hp2 h2, hv (by simpa using dvd_sub hu h2)]

private lemma intCast_zmod_four_of_emod {x c : ℤ} (h : x % 4 = c) :
    (x : ZMod 4) = c :=
  (ZMod.intCast_eq_intCast_iff' x c 4).mpr (by lia)

/-- A prime `p` dividing `K ≡ c Q (mod r + s)`, where `r + s = -u(u + v)` and `Q = (v²)^m`, does
not divide `r + s` if it cannot divide `c` when it divides `u(u + v)`. -/
private lemma not_dvd_add_of_modEq (huv : IsCoprime u v) {p : ℤ} (hp : Prime p)
    (hr : r + v ^ 2 = -(u * (u + v))) {K c : ℤ} {m : ℕ}
    (hK : K ≡ c * (v ^ 2) ^ m [ZMOD r + v ^ 2]) (hc : p ∣ u * (u + v) → ¬p ∣ c)
    (hpK : p ∣ K) : ¬p ∣ r + v ^ 2 := fun hprs ↦ by
  have hpuv : p ∣ u * (u + v) := by rwa [hr, dvd_neg] at hprs
  rcases hp.dvd_or_dvd ((hK.of_dvd hprs).dvd_iff.mp hpK) with h | h
  · exact hc hpuv h
  · exact not_dvd_right_of_dvd_mul_add huv hp hpuv (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))

private lemma two_not_dvd {p : ℕ} (hp4 : p % 4 = 3) : ¬(p : ℤ) ∣ 2 := fun h ↦ by
  have := Int.le_of_dvd two_pos h
  lia

/-- `K ≡ 3 (mod 4)` from `X + e = d K` with `X ≡ 2` and `d ≡ e ≡ 1 (mod 4)`. -/
private lemma emod_four_eq_three_of_add_eq_mul {X e d K : ℤ} (h : X + e = d * K)
    (hX : (X : ZMod 4) = 2) (hd : (d : ZMod 4) = 1) (he : (e : ZMod 4) = 1) : K % 4 = 3 := by
  have h' := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast [hX, hd, he] at h'
  simpa using (ZMod.intCast_eq_intCast_iff' K 3 4).mp (by push_cast; linear_combination -h')

/-- Class `(u, v) ≡ (1, 1) (mod 4)`: `K = H_n / u = -r(u + v)T + vQ`, `Q = s^{2^{n-1} - 1}`, is a
positive divisor of `u_n`, `≡ 3 (mod 4)` and `≡ (u + 2v) Q (mod r + s)`. -/
private lemma exists_prime_dvd_uSeq_of_one_one (huv : IsCoprime u v) (hu : 0 < u) (hv : 0 < v)
    (hu4 : u % 4 = 1) (hv4 : v % 4 = 1) (hr : r + v ^ 2 = -(u * (u + v))) {n : ℕ} (hn : 2 ≤ n)
    {T : ℤ} (hw : wSeq r (v ^ 2) n = (r + v ^ 2) * T)
    (hT : T ≡ (v ^ 2) ^ (2 ^ (n - 1) - 2) [ZMOD r + v ^ 2])
    (hX : 0 < r * wSeq r (v ^ 2) n) (hX4 : ((r * wSeq r (v ^ 2) n : ℤ) : ZMod 4) = 2) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq r (v ^ 2) n ∧ ¬(p : ℤ) ∣ r + v ^ 2 := by
  set Q := (v ^ 2) ^ (2 ^ (n - 1) - 1) with hQ
  set K := -r * (u + v) * T + v * Q with hK
  have hH : r * wSeq r (v ^ 2) n + u * (v * Q) = u * K := by rw [hw, hr]; ring
  have hu' := intCast_zmod_four_of_emod hu4
  obtain ⟨p, hp, hp4, hpK⟩ := Int.exists_prime_dvd_of_emod_four_eq_three
    (pos_of_mul_pos_right (hH ▸ add_pos hX (by positivity)) hu.le)
    (emod_four_eq_three_of_add_eq_mul hH hX4 (by simpa using hu')
      (by simp [hQ, hu', intCast_zmod_four_of_emod hv4]))
  have hp' := Nat.prime_iff_prime_int.mp hp
  refine ⟨p, hp, hp4, ?_, not_dvd_add_of_modEq huv hp' hr (c := u + 2 * v)
    (m := 2 ^ (n - 1) - 1) ?_ (not_dvd_add_two_mul huv hp' (two_not_dvd hp4)) hpK⟩
  · rw [uSeq_eq_mul_of_add_eq rfl hr (by lia), hH]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpK u) _
  · calc K = (u + v) * (-r * T) + v * Q := by ring
      _ ≡ (u + v) * Q + v * Q [ZMOD r + v ^ 2] := ((neg_mul_modEq hn hT).mul_left _).add_right _
      _ = (u + 2 * v) * Q := by ring

/-- Class `(u, v) ≡ (2, 3) (mod 4)`: `K = G_n / (u + v) = -r u T - vQ`, `Q = s^{2^{n-1} - 1}`, is
a positive divisor of `u_n`, `≡ 3 (mod 4)` and `≡ (u - v) Q (mod r + s)`. -/
private lemma exists_prime_dvd_uSeq_of_two_three (huv : IsCoprime u v) (hu : 0 < u) (hv : 0 < v)
    (hu4 : u % 4 = 2) (hv4 : v % 4 = 3) (hr : r + v ^ 2 = -(u * (u + v))) {n : ℕ} (hn : 2 ≤ n)
    {T : ℤ} (hw : wSeq r (v ^ 2) n = (r + v ^ 2) * T)
    (hT : T ≡ (v ^ 2) ^ (2 ^ (n - 1) - 2) [ZMOD r + v ^ 2])
    (hX : (u + v) * (v * (v ^ 2) ^ (2 ^ (n - 1) - 1)) < r * wSeq r (v ^ 2) n)
    (hX4 : ((r * wSeq r (v ^ 2) n : ℤ) : ZMod 4) = 2) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq r (v ^ 2) n ∧ ¬(p : ℤ) ∣ r + v ^ 2 := by
  set Q := (v ^ 2) ^ (2 ^ (n - 1) - 1) with hQ
  set K := -r * u * T - v * Q with hK
  have hG : r * wSeq r (v ^ 2) n + -((u + v) * (v * Q)) = (u + v) * K := by rw [hw, hr]; ring
  have hu' := intCast_zmod_four_of_emod hu4
  have hv' := intCast_zmod_four_of_emod hv4
  obtain ⟨p, hp, hp4, hpK⟩ := Int.exists_prime_dvd_of_emod_four_eq_three
    (pos_of_mul_pos_right (by lia : 0 < (u + v) * K) (by lia))
    (emod_four_eq_three_of_add_eq_mul hG hX4 (by push_cast [hu', hv']; decide)
      (by push_cast [hQ, hu', hv', show (3 : ZMod 4) ^ 2 = 1 by decide, one_pow]; decide))
  have hp' := Nat.prime_iff_prime_int.mp hp
  refine ⟨p, hp, hp4, ?_, not_dvd_add_of_modEq huv hp' hr (c := u - v)
    (m := 2 ^ (n - 1) - 1) ?_ (not_dvd_sub huv hp' (two_not_dvd hp4)) hpK⟩
  · rw [uSeq_eq_mul_of_add_eq rfl hr (by lia), sub_eq_add_neg, hG]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpK _) _
  · calc K = u * (-r * T) - v * Q := by ring
      _ ≡ u * Q - v * Q [ZMOD r + v ^ 2] := ((neg_mul_modEq hn hT).mul_left _).sub_right _
      _ = (u - v) * Q := by ring

private lemma isCoprime_neg_sq_add_add (huv : IsCoprime u v) :
    IsCoprime (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) := by
  have := (huv.mul_left (by simpa using huv.add_mul_left_left 1)).add_mul_left_left v
  exact (by convert this using 1; ring : IsCoprime (u ^ 2 + u * v + v ^ 2) v).neg_left.pow_right

private lemma modEq_four_neg_sq_add_add (h : u % 4 = 1 ∧ v % 4 = 1 ∨ u % 4 = 2 ∧ v % 4 = 3) :
    -(u ^ 2 + u * v + v ^ 2) ≡ v ^ 2 [ZMOD 4] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 4).mp ?_
  push_cast
  rcases h with ⟨hu4, hv4⟩ | ⟨hu4, hv4⟩ <;>
  · rw [intCast_zmod_four_of_emod hu4, intCast_zmod_four_of_emod hv4]
    decide

/-- (Z1) for `r = -(u² + uv + v²)`: `r < 0`, and `-r ≡ 3 (mod 4)` in both classes. -/
private lemma negAllCriterion_neg_sq_add_add (hu : 0 < u) (hv : 0 < v)
    (h : u % 4 = 1 ∧ v % 4 = 1 ∨ u % 4 = 2 ∧ v % 4 = 3) :
    NegAllCriterion (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) := by
  have h4 := modEq_four_neg_sq_add_add h
  rw [Int.ModEq] at h4
  refine .not_isSquare (fun ⟨t, ht⟩ ↦ ?_) (Int.not_isSquare_of_two_le_emod_four ?_)
  · lia [mul_self_nonneg t, mul_pos hu hv, sq_nonneg u, sq_nonneg v]
  · lia [Int.sq_emod_four_eq_one_of_odd (Int.odd_iff.mpr (by lia : v % 2 = 1))]

/-- For `a = -(ℓ² + ℓ + 1) ≤ -2`, `ℓ = u/v`, in the classes `(u, v) ≡ (1, 1), (2, 3) (mod 4)`,
every `u_n` with `n ≥ 2` even has a prime factor `p ≡ 3 (mod 4)` not dividing `r + s`. -/
theorem exists_prime_dvd_uSeq_neg_sq_add_add (huv : IsCoprime u v) (hu : 0 < u) (hv : 0 < v)
    (h2 : v ^ 2 ≤ u * (u + v)) (h : u % 4 = 1 ∧ v % 4 = 1 ∨ u % 4 = 2 ∧ v % 4 = 3) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) n ∧
      ¬(p : ℤ) ∣ -(u ^ 2 + u * v + v ^ 2) + v ^ 2 := by
  have hr : -(u ^ 2 + u * v + v ^ 2) + v ^ 2 = -(u * (u + v)) := by ring
  have hX4 := intCast_mul_wSeq_zmod_four_of_even (Int.odd_iff.mpr (by lia : v % 2 = 1)).pow
    (modEq_four_neg_sq_add_add h) hn he
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := even_iff_two_dvd.mp he
  obtain ⟨T, hw, hT⟩ := exists_wSeq_two_mul_eq (isCoprime_neg_sq_add_add huv) (k := k) (by lia)
  have hX := mul_le_mul_of_nonneg_left (pow_le_neg_wSeq (r := -(u ^ 2 + u * v + v ^ 2))
    (pow_pos hv 2) (by linear_combination h2) (n := 2 * k) (by lia))
    (by positivity : 0 ≤ u ^ 2 + u * v + v ^ 2)
  rw [show (u ^ 2 + u * v + v ^ 2) * -wSeq (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) (2 * k) =
    -(u ^ 2 + u * v + v ^ 2) * wSeq (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) (2 * k) by ring] at hX
  have hQ : 0 < (v ^ 2) ^ (2 ^ (2 * k - 1) - 1) := by positivity
  rcases h with ⟨hu4, hv4⟩ | ⟨hu4, hv4⟩
  · exact exists_prime_dvd_uSeq_of_one_one huv hu hv hu4 hv4 hr hn hw hT
      (lt_of_lt_of_le (by positivity) hX) hX4
  · exact exists_prime_dvd_uSeq_of_two_three huv hu hv hu4 hv4 hr hn hw hT
      (lt_of_lt_of_le (by linear_combination mul_pos (pow_pos hu 2) hQ) hX) hX4

/-- **Li's Theorem 3.9 for rational parameters**: for `a = -(ℓ² + ℓ + 1) ≤ -2` with `ℓ = u/v`,
`u, v` coprime and `(u, v) ≡ (1, 1)` or `(2, 3) (mod 4)`, `Ω_n ≅ [C₂]ⁿ` for all `n`. Here
`a ≡ 1 mod 4` and `|r| ≡ 3 (mod 4)`, so (Z1) and (O2) give `φ₀` and `φ₁`; the odd levels are
`QuadraticIterates.hasCharPattern_mulSingle_of_odd`, the even ones
`QuadraticIterates.exists_prime_dvd_uSeq_neg_sq_add_add` with period two. -/
theorem nonempty_mulEquiv_of_eq_neg_sq_add_add_one (huv : IsCoprime u v) (hu : 0 < u)
    (hv : 0 < v) (h2 : v ^ 2 ≤ u * (u + v))
    (h : u % 4 = 1 ∧ v % 4 = 1 ∨ u % 4 = 2 ∧ v % 4 = 3) (n : ℕ) :
    Nonempty (GaloisGroup (-(((u : ℚ) / v) ^ 2 + (u : ℚ) / v + 1)) n ≃* WreathPower n) := by
  have hv' : (v : ℚ) ≠ 0 := mod_cast hv.ne'
  rw [show -(((u : ℚ) / v) ^ 2 + (u : ℚ) / v + 1) =
    ((-(u ^ 2 + u * v + v ^ 2) : ℤ) : ℚ) / ((v ^ 2 : ℤ) : ℚ) by push_cast; field]
  have hrs := isCoprime_neg_sq_add_add huv
  have hodd : Odd (v ^ 2) := (Int.odd_iff.mpr (by lia : v % 2 = 1)).pow
  have h4 := modEq_four_neg_sq_add_add h
  have h₀ := hasCharPattern_neg_one_of_negAllCriterion hrs (pow_pos hv 2).ne'
    (negAllCriterion_neg_sq_add_add hu hv h)
  refine forall_nonempty_mulEquiv_of_forall_hasCharPattern (fun m hm ↦ ?_) n
  rcases hm.eq_or_lt with rfl | hm
  · exact hasCharPattern_mulSingle_one_of_modEq_four hrs hodd h4
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨p, hp, hp4, hpu, hprs⟩ := exists_prime_dvd_uSeq_neg_sq_add_add huv hu hv h2 h hm he
    have := Fact.mk hp
    exact hasCharPattern_mulSingle_of_prime_dvd_uSeq hrs hodd h4 h₀ (by lia) hp4 hpu hprs
  · refine hasCharPattern_mulSingle_of_odd hrs (pow_pos hv 2) hodd h4 (.inl ?_) h₀
      (by lia [Nat.odd_iff.mp ho]) ho
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (by linear_combination h2 : -(u ^ 2 + u * v + v ^ 2) ≤ -2 * v ^ 2)

end Li

end QuadraticIterates
