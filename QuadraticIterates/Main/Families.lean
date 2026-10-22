/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Sequence.WSeq

import QuadraticIterates.Characters.Criterion
import QuadraticIterates.Main.Theorem
import QuadraticIterates.Mathlib.Algebra.Group.Nat.Defs
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
`p ≡ 3 (mod 4)` at every level `n ≥ 2` resp. at the even levels; the odd levels of the second
family are `QuadraticIterates.hasCharPattern_mulSingle_of_odd`.

## Main statements

* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`: the family `a = -ℓ(ℓ + 1)` with
  `ℓ = u/v > 1` and `(u, v) ≡ (2, 1)` or `(3, 3) (mod 4)`.
* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`: Li's Theorem 3.9 for rational
  parameters, `a = -(ℓ² + ℓ + 1) ≤ -2` with `ℓ = u/v` and `(u, v) ≡ (1, 1)` or `(2, 3) (mod 4)`.
* `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two` and
  `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one`: the integer
  parameters of the two families, which contain Theorems 3.3 and 3.9 of [Li 2021].
* `QuadraticIterates.neg_vSeq_neg_mul_add_eq`, `QuadraticIterates.uSeq_eq_mul_of_add_eq`: the
  factorizations of `v_n` resp. `u_n`.
* `QuadraticIterates.exists_prime_dvd_vSeq_neg_mul_add`,
  `QuadraticIterates.exists_prime_dvd_uSeq_neg_sq_add_add`: a prime `p ≡ 3 (mod 4)` dividing `v_n`
  for every `n ≥ 2`, resp. dividing `u_n` but not `r + s` for every even `n ≥ 2`.

## References

* H.-C. Li, *On Stoll's criterion for the maximality of quadratic arboreal Galois
  representations*, Arch. Math. **117** (2021), 133-140.
-/

@[expose] public section

namespace QuadraticIterates

/-- `(v²)^{2^{n-1}} = v V` for `V = v^{2^n - 1}`, `n ≥ 1`. -/
private lemma sq_pow_two_pow (v : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (v ^ 2) ^ 2 ^ (n - 1) = v * v ^ (2 ^ n - 1) := by
  rw [← pow_mul, ← pow_succ', ← pow_succ', Nat.sub_add_cancel hn,
    Nat.sub_add_cancel Nat.one_le_two_pow]

section NegMulAddOne

variable {u v : ℤ}

/-- For `r = -u(u + v)` and `s = v²`, `-v_n = ((u + v) W - V)(u W + V)` with `W = -w_n` and
`V = v^{2^n - 1}` (`n ≥ 1`). -/
theorem neg_vSeq_neg_mul_add_eq {n : ℕ} (hn : 1 ≤ n) :
    -vSeq (-(u * (u + v))) (v ^ 2) n =
      ((u + v) * -wSeq (-(u * (u + v))) (v ^ 2) n - v ^ (2 ^ n - 1)) *
        (u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1)) := by
  rw [vSeq, wSeq_succ _ _ hn, sq_pow_two_pow v hn]
  ring

/-- In the classes `(u, v) ≡ (2, 1)`, `(3, 3) (mod 4)`, the first resp. second factor of
`QuadraticIterates.neg_vSeq_neg_mul_add_eq` is `6` modulo `8` (`n ≥ 2`): there
`-w_n ≡ u(u + v) - v²` and `v^{2^n - 1} ≡ v`. -/
private lemma intCast_zmod_eight_eq_six (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3)
    {n : ℕ} (hn : 2 ≤ n) :
    (((u + v) * -wSeq (-(u * (u + v))) (v ^ 2) n - v ^ (2 ^ n - 1) : ℤ) : ZMod 8) = 6 ∨
      ((u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1) : ℤ) : ZMod 8) = 6 := by
  have hv : Odd v := Int.odd_iff.mpr (by lia)
  have hr : Even (u * (u + v)) := Int.even_mul.mpr <| by
    rcases h with h | h
    exacts [.inl (Int.even_iff.mpr (by lia)), .inr (Int.even_iff.mpr (by lia))]
  push_cast
  rw [intCast_wSeq_zmod_eight_of_even_left hr.neg hv.pow hn,
    ZMod.intCast_pow_two_pow_sub_one_eight_of_odd hv (by lia)]
  push_cast
  rcases h with ⟨hu, hv4⟩ | ⟨hu, hv4⟩ <;>
  rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hu with h | h <;>
  rcases ZMod.intCast_eight_eq_or_eq_of_emod_four hv4 with h' | h' <;>
  · rw [h, h']
    decide

/-- For `a = -ℓ(ℓ + 1)`, `ℓ = u/v > 1`, in the classes `(u, v) ≡ (2, 1), (3, 3) (mod 4)`, every
`v_n`, `n ≥ 2`, has a prime factor `p ≡ 3 (mod 4)`: `-v_n = F₁ F₂` with `F₂ > 0` (as `w_n < 0`),
so `F₁ > 0` (as `v_n < 0`), and `F₁` resp. `F₂` is `≡ 6 (mod 8)`. -/
theorem exists_prime_dvd_vSeq_neg_mul_add (hv : 0 < v) (hvu : v < u)
    (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq (-(u * (u + v))) (v ^ 2) n := by
  have hr : -(u * (u + v)) ≤ -2 * v ^ 2 := by
    linear_combination mul_nonneg (by lia : 0 ≤ u - v) (by lia : 0 ≤ u + 2 * v)
  have hfac := neg_vSeq_neg_mul_add_eq (u := u) (v := v) (by lia : 1 ≤ n)
  have hF₂ : 0 < u * -wSeq (-(u * (u + v))) (v ^ 2) n + v ^ (2 ^ n - 1) :=
    add_pos (mul_pos (by lia) ((pow_pos (pow_pos hv 2) _).trans_le
      (pow_le_neg_wSeq (pow_pos hv 2) hr (by lia)))) (pow_pos hv _)
  have hF₁ := pos_of_mul_pos_left
    (hfac ▸ neg_pos.mpr (vSeq_neg_of_le_neg_two_mul (pow_pos hv 2) hr (by lia))) hF₂.le
  rcases intCast_zmod_eight_eq_six h hn with h8 | h8
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_six hF₁
      ((ZMod.intCast_eq_intCast_iff' _ 6 8).mp (mod_cast h8))
    exact ⟨p, hp, hp4, dvd_neg.mp (hfac ▸ hpd.mul_right _)⟩
  · obtain ⟨p, hp, hp4, hpd⟩ := Int.exists_prime_dvd_of_emod_eight_eq_six hF₂
      ((ZMod.intCast_eq_intCast_iff' _ 6 8).mp (mod_cast h8))
    exact ⟨p, hp, hp4, dvd_neg.mp (hfac ▸ hpd.mul_left _)⟩

private lemma emod_four_neg_mul_add (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) :
    -(u * (u + v)) % 4 = 2 := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> lia [Int.mul_emod u (u + v) 4]

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

/-- **The family `a = -ℓ(ℓ + 1)`**: for `ℓ = u/v > 1` with `u, v` coprime and `(u, v) ≡ (2, 1)` or
`(3, 3) (mod 4)`, `Ω_n ≅ [C₂]ⁿ` for all `n`. Here `r = -u(u + v) ≡ 2 (mod 4)` gives `φ₀` by (Z1), a
prime `p ≡ 3 (mod 4)` dividing `u + v` resp. `u` gives `φ₁`, and
`QuadraticIterates.exists_prime_dvd_vSeq_neg_mul_add` gives reflection at every level `n ≥ 2`. -/
theorem nonempty_mulEquiv_of_eq_neg_mul_add_one (huv : IsCoprime u v) (hv : 0 < v) (hvu : v < u)
    (h : u % 4 = 2 ∧ v % 4 = 1 ∨ u % 4 = 3 ∧ v % 4 = 3) (n : ℕ) :
    Nonempty (GaloisGroup (-((u : ℚ) / v * ((u : ℚ) / v + 1))) n ≃* WreathPower n) := by
  have hv' : (v : ℚ) ≠ 0 := mod_cast hv.ne'
  rw [show -((u : ℚ) / v * ((u : ℚ) / v + 1)) = ((-(u * (u + v)) : ℤ) : ℚ) / ((v ^ 2 : ℤ) : ℚ) by
    push_cast; field]
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

end NegMulAddOne

section NegSqAddAddOne

variable {r s u v : ℤ}

/-- For `s = v²` and `r + s = -u(u + v)`, `u_n = (r w_n - (u + v) V)(r w_n + u V)` with
`V = v s^{2^{n-1} - 1} = v^{2^n - 1}` (`n ≥ 1`). -/
theorem uSeq_eq_mul_of_add_eq (hs : s = v ^ 2) (hr : r + s = -(u * (u + v))) {n : ℕ} (hn : 1 ≤ n) :
    uSeq r s n = (r * wSeq r s n - (u + v) * (v * s ^ (2 ^ (n - 1) - 1))) *
      (r * wSeq r s n + u * (v * s ^ (2 ^ (n - 1) - 1))) := by
  have h₁ : s ^ 2 ^ (n - 1) = s * s ^ (2 ^ (n - 1) - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  have h₂ : s ^ (2 ^ n - 1) = s * (s ^ (2 ^ (n - 1) - 1)) ^ 2 := by
    rw [← pow_mul', ← pow_succ', Nat.two_pow_sub_one_eq hn]
  rw [uSeq, h₁, h₂, hr, hs]
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
  hp.not_isUnit <| huv.isUnit_of_dvd' ((hp.dvd_or_dvd h).elim id (dvd_add_left hv).mp) hv

/-- A prime `p ∤ 2` dividing `u(u + v)`, with `u, v` coprime, does not divide `u + 2v`: it
would divide `u(u + v) - (u + 2v)(u - v) = 2v²`. -/
private lemma not_dvd_add_two_mul (huv : IsCoprime u v) {p : ℤ} (hp : Prime p) (hp2 : ¬p ∣ 2)
    (h : p ∣ u * (u + v)) : ¬p ∣ u + 2 * v := fun hc ↦ by
  rcases hp.dvd_or_dvd (by convert dvd_sub h (hc.mul_right (u - v)) using 1; ring : p ∣ 2 * v ^ 2)
    with h2 | h2
  exacts [hp2 h2, not_dvd_right_of_dvd_mul_add huv hp h (hp.dvd_of_dvd_pow h2)]

private lemma intCast_zmod_four_of_emod {x c : ℤ} (h : x % 4 = c) : (x : ZMod 4) = c :=
  (ZMod.intCast_eq_intCast_iff' x c 4).mpr (by lia)

/-- A prime `p ∤ 2` dividing `K ≡ (u + 2v) Q (mod r + s)`, where `r + s = -u(u + v)` and
`Q = (v²)^m`, does not divide `r + s`. -/
private lemma not_dvd_add_of_modEq (huv : IsCoprime u v) {p : ℤ} (hp : Prime p) (hp2 : ¬p ∣ 2)
    (hr : r + v ^ 2 = -(u * (u + v))) {K : ℤ} {m : ℕ}
    (hK : K ≡ (u + 2 * v) * (v ^ 2) ^ m [ZMOD r + v ^ 2]) (hpK : p ∣ K) :
    ¬p ∣ r + v ^ 2 := fun hprs ↦ by
  have hpuv : p ∣ u * (u + v) := by rwa [hr, dvd_neg] at hprs
  rcases hp.dvd_or_dvd ((hK.of_dvd hprs).dvd_iff.mp hpK) with h | h
  · exact not_dvd_add_two_mul huv hp hp2 hpuv h
  · exact not_dvd_right_of_dvd_mul_add huv hp hpuv (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))

private lemma not_dvd_two_of_mod_four_eq_three {p : ℕ} (hp4 : p % 4 = 3) : ¬(p : ℤ) ∣ 2 :=
  fun h ↦ by lia [Int.le_of_dvd two_pos h]

/-- `K ≡ 3 (mod 4)` from `X + e = d K` with `X ≡ 2` and `d ≡ e ≡ 1 (mod 4)`. -/
private lemma emod_four_eq_three_of_add_eq_mul {X e d K : ℤ} (h : X + e = d * K)
    (hX : (X : ZMod 4) = 2) (hd : (d : ZMod 4) = 1) (he : (e : ZMod 4) = 1) : K % 4 = 3 := by
  have h' := congr(($h : ZMod 4))
  push_cast [hX, hd, he] at h'
  simpa using (ZMod.intCast_eq_intCast_iff' K 3 4).mp (by push_cast; linear_combination -h')

/-- For `(u, v) ≡ (1, 1) (mod 4)`, `s = v²` and `H_n = r w_n + u v s^{2^{n-1} - 1} > 0`,
`K = H_n / u = -r(u + v)T + vQ`, `Q = s^{2^{n-1} - 1}`, is a positive divisor of `u_n`,
`≡ 3 (mod 4)` and `≡ (u + 2v) Q (mod r + s)`. The sign of `v` is arbitrary: `(u + v, -v)` turns the
class `(2, 3)` into `(1, 1)` and leaves `r` and `s` unchanged. -/
private lemma exists_prime_dvd_uSeq_of_one_one (huv : IsCoprime u v) (hu : 0 < u)
    (hu4 : u % 4 = 1) (hv4 : v % 4 = 1) (hs : s = v ^ 2) (hr : r + s = -(u * (u + v))) {n : ℕ}
    (hn : 2 ≤ n) {T : ℤ} (hw : wSeq r s n = (r + s) * T)
    (hT : T ≡ s ^ (2 ^ (n - 1) - 2) [ZMOD r + s])
    (hH : 0 < r * wSeq r s n + u * (v * s ^ (2 ^ (n - 1) - 1)))
    (hX4 : ((r * wSeq r s n : ℤ) : ZMod 4) = 2) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq r s n ∧ ¬(p : ℤ) ∣ r + s := by
  subst hs
  set Q := (v ^ 2) ^ (2 ^ (n - 1) - 1) with hQ
  set K := -r * (u + v) * T + v * Q
  have hK : r * wSeq r (v ^ 2) n + u * (v * Q) = u * K := by rw [hw, hr]; ring
  have hu' := intCast_zmod_four_of_emod hu4
  obtain ⟨p, hp, hp4, hpK⟩ := Int.exists_prime_dvd_of_emod_four_eq_three
    (pos_of_mul_pos_right (hK ▸ hH) hu.le)
    (emod_four_eq_three_of_add_eq_mul hK hX4 (by simpa using hu')
      (by simp [hQ, hu', intCast_zmod_four_of_emod hv4]))
  refine ⟨p, hp, hp4, ?_, not_dvd_add_of_modEq huv (Nat.prime_iff_prime_int.mp hp)
    (not_dvd_two_of_mod_four_eq_three hp4) hr (m := 2 ^ (n - 1) - 1) ?_ hpK⟩
  · rw [uSeq_eq_mul_of_add_eq rfl hr (by lia), hK]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpK u) _
  · calc K = (u + v) * (-r * T) + v * Q := by ring
      _ ≡ (u + v) * Q + v * Q [ZMOD r + v ^ 2] := ((neg_mul_modEq hn hT).mul_left _).add_right _
      _ = (u + 2 * v) * Q := by ring

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
  refine .not_isSquare (not_isSquare_of_neg (neg_neg_of_pos (by positivity)))
    (Int.not_isSquare_of_two_le_emod_four ?_)
  lia [Int.sq_emod_four_eq_one_of_odd (Int.odd_iff.mpr (by lia : v % 2 = 1))]

/-- For `a = -(ℓ² + ℓ + 1) ≤ -2`, `ℓ = u/v`, in the classes `(u, v) ≡ (1, 1), (2, 3) (mod 4)`,
every `u_n` with `n ≥ 2` even has a prime factor `p ≡ 3 (mod 4)` not dividing `r + s`. The class
`(2, 3)` is the class `(1, 1)` of `(u + v, -v)`, that is, of `-1 - ℓ`, which gives the same `a`. -/
theorem exists_prime_dvd_uSeq_neg_sq_add_add (huv : IsCoprime u v) (hu : 0 < u) (hv : 0 < v)
    (h2 : v ^ 2 ≤ u * (u + v)) (h : u % 4 = 1 ∧ v % 4 = 1 ∨ u % 4 = 2 ∧ v % 4 = 3) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ uSeq (-(u ^ 2 + u * v + v ^ 2)) (v ^ 2) n ∧
      ¬(p : ℤ) ∣ -(u ^ 2 + u * v + v ^ 2) + v ^ 2 := by
  have hX4 := intCast_mul_wSeq_zmod_four_of_even (Int.odd_iff.mpr (by lia : v % 2 = 1)).pow
    (modEq_four_neg_sq_add_add h) hn he
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := even_iff_two_dvd.mp he
  obtain ⟨T, hw, hT⟩ := exists_wSeq_two_mul_eq (isCoprime_neg_sq_add_add huv) (k := k) (by lia)
  have hX := mul_le_mul_of_nonneg_left (pow_le_neg_wSeq (r := -(u ^ 2 + u * v + v ^ 2))
    (pow_pos hv 2) (by linear_combination h2) (n := 2 * k) (by lia))
    (by positivity : 0 ≤ u ^ 2 + u * v + v ^ 2)
  rw [mul_neg, ← neg_mul] at hX
  have hQ : 0 < (v ^ 2) ^ (2 ^ (2 * k - 1) - 1) := by positivity
  rcases h with ⟨hu4, hv4⟩ | ⟨hu4, hv4⟩
  · exact exists_prime_dvd_uSeq_of_one_one huv hu hu4 hv4 rfl (by ring) hn hw hT
      (add_pos (lt_of_lt_of_le (by positivity) hX) (by positivity)) hX4
  · exact exists_prime_dvd_uSeq_of_one_one (u := u + v) (v := -v)
      (by simpa using (huv.add_mul_left_left 1).neg_right) (by lia) (by lia) (by lia)
      (neg_sq v).symm (by ring) hn hw hT (by linear_combination hX + mul_pos (pow_pos hu 2) hQ) hX4

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

end NegSqAddAddOne

/-- For `a = -ℓ(ℓ + 1)` with a positive integer `ℓ ≡ 2 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`: the
case `v = 1` of `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`. For `ℓ = 8k + 2` this
is Theorem 3.3 of [Li 2021]. -/
theorem nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two {ℓ : ℤ} (hℓ : 0 < ℓ)
    (hℓ4 : ℓ % 4 = 2) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) * (ℓ + 1))) n ≃* WreathPower n) := by
  have h := nonempty_mulEquiv_of_eq_neg_mul_add_one isCoprime_one_right one_pos (by lia)
    (.inl ⟨hℓ4, rfl⟩) n
  rwa [Int.cast_one, div_one] at h

/-- For `a = -(ℓ² + ℓ + 1)` with a positive integer `ℓ ≡ 1 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`: the
case `v = 1` of `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`. For `ℓ = 4k + 1`
this is Theorem 3.9 of [Li 2021]. -/
theorem nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one {ℓ : ℤ} (hℓ : 0 < ℓ)
    (hℓ4 : ℓ % 4 = 1) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) ^ 2 + ℓ + 1)) n ≃* WreathPower n) := by
  have h := nonempty_mulEquiv_of_eq_neg_sq_add_add_one isCoprime_one_right hℓ one_pos
    (by rw [one_pow]; exact one_le_mul_of_one_le_of_one_le hℓ (by lia)) (.inl ⟨hℓ4, rfl⟩) n
  rwa [Int.cast_one, div_one] at h

end QuadraticIterates
