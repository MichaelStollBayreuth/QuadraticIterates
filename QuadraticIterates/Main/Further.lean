/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import QuadraticIterates.Characters.Pattern
public import QuadraticIterates.Mathlib.NumberTheory.MulChar.Rat
public import QuadraticIterates.Sequence.WSeq

import QuadraticIterates.Main.Criteria
import QuadraticIterates.Main.TwoAdic
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Patterns.Primes
import QuadraticIterates.Patterns.Reflection
import QuadraticIterates.Sequence.Orbit
import QuadraticIterates.Sequence.SquareClasses

/-!
# Further criteria for `φ₁` and `τ`

For `a = r/s`, characters at primes where the orbit of `0` is short. At a prime `p ≡ 1 (mod 4)`
dividing `v_2` (modulo `p` the orbit of `0` reaches a fixed point after three steps) or `v_3`
(after four steps), `χ_p` is constant from `c_2` on, and so is `χ_p χ_q` for two primes
`p, q ≡ 3 (mod 4)` dividing `v_2`; such a character is a `φ₁`, a `τ` or a `φ₀` according to its
values at `c_1` and `c_2`. Modulo the primes of `w_3`, `0` has period `3`, and these primes give
`τ` under a condition on Legendre symbols. None of this is used by the main theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`; with `φ₀` or `φ₁` from its
criteria, these characters complete the Klein four-group of patterns
(`QuadraticIterates.hasCharPattern_mulSingle_of_neg_of_neg_mulSingle` and its siblings).

## Main statements

* `QuadraticIterates.unitPartChar_cSeq_of_dvd_vSeq_two`,
  `QuadraticIterates.unitPartChar_mul_unitPartChar_cSeq_of_dvd_vSeq_two`,
  `QuadraticIterates.unitPartChar_cSeq_of_dvd_vSeq_three`: characters constant from `c_2` on
  ((R1), (R2), (R3) of the blueprint).
* `QuadraticIterates.hasCharPattern_neg_mulSingle_one_of_dvd_wSeq_three`: `τ` from the primes of
  `w_3` ((P3)).
-/

@[expose] public section

namespace QuadraticIterates

open Rat

variable {r s : ℤ} {p : ℕ} [Fact p.Prime]

/-! ### Values of `χ_p` as Jacobi symbols -/

private lemma unitPartChar_cSeq_one_eq_jacobiSym (hs : s ≠ 0) (hp : ¬(p : ℤ) ∣ r * s) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) 1) = jacobiSym (-(r * s)) p := by
  rw [mulChar_cSeq_one _ hs, show -((r : ℚ) * s) = ((-(r * s) : ℤ) : ℚ) by push_cast; ring,
    unitPartChar_intCast (pow_one p).symm (by rwa [dvd_neg])]
  exact jacobiSym.legendreSym.to_jacobiSym p _

private lemma unitPartChar_cSeq_eq_jacobiSym (hs : s ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hp : ¬(p : ℤ) ∣ r * wSeq r s n) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) n) =
      jacobiSym (r * wSeq r s n) p := by
  rw [mulChar_cSeq_of_two_le _ hs hn, ← Int.cast_mul, unitPartChar_intCast (pow_one p).symm hp]
  exact jacobiSym.legendreSym.to_jacobiSym p _

private lemma jacobiSym_eq_zero_of_dvd {x : ℤ} (hx : (p : ℤ) ∣ x) : jacobiSym x p = 0 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact (legendreSym.eq_zero_iff p x).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr hx)

/-- A prime dividing `w_3` does not divide `r + s`: `w_3 ≡ s³ (mod r + s)`. -/
private lemma not_dvd_add_of_dvd_wSeq_three (hrs : IsCoprime r s) (hp : (p : ℤ) ∣ wSeq r s 3) :
    ¬(p : ℤ) ∣ r + s := fun h ↦ by
  have hp' := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have h3 := ((wSeq_two_mul_add_one_modEq hrs (k := 1) le_rfl).of_dvd h).dvd_iff.mp hp
  exact hp'.not_isUnit ((isCoprime_wSeq_right hrs (n := 3) (by norm_num)).isUnit_of_dvd' hp
    (hp'.dvd_of_dvd_pow h3))

/-- A prime dividing `v_2 = w_3 + (r + s) s²` does not divide `r + s`. -/
private lemma not_dvd_add_of_dvd_vSeq_two (hrs : IsCoprime r s) (hp : (p : ℤ) ∣ vSeq r s 2) :
    ¬(p : ℤ) ∣ r + s := fun h ↦ not_dvd_add_of_dvd_wSeq_three hrs (by
  have hv : vSeq r s 2 = wSeq r s 3 + (r + s) * s ^ 2 := by simp [vSeq]
  have hd := dvd_sub hp (h.mul_right (s ^ 2))
  rwa [hv, add_sub_cancel_right] at hd) h

/-! ### Primes of `v_2` and `v_3` -/

/-- At an odd prime `p ∣ v_2`, `χ_p(c_2) = (r(r + s) / p)`. -/
private lemma unitPartChar_cSeq_two_of_dvd_vSeq_two (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hp2 : p ≠ 2) (hp : (p : ℤ) ∣ vSeq r s 2) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) 2) = jacobiSym (r * (r + s)) p := by
  have h₂ := unitPartChar_cSeq_eq_jacobiSym (p := p) hs le_rfl (n := 2) (by
    simpa using (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_mul
      (not_dvd_left_of_dvd_vSeq hrs le_rfl Fact.out hp2 hp) (not_dvd_add_of_dvd_vSeq_two hrs hp))
  rwa [wSeq_two] at h₂

/-- **(R1)** At a prime `p ≡ 1 (mod 4)` dividing `v_2 = r³ + 2r²s + 2rs² + 2s³`, the character
`χ_p` is constant from `c_2` on: `χ_p(c_m) = (r(r + s) / p)` for `m ≥ 2` (reflection, with
`(-1 / p) = 1`), while `χ_p(c_1) = (-rs / p)`. So `χ_p` is a `φ₁` or a `τ` when
`(-s(r + s) / p) = -1`. -/
theorem unitPartChar_cSeq_of_dvd_vSeq_two (hrs : IsCoprime r s) (hs : s ≠ 0) (hp4 : p % 4 = 1)
    (hp : (p : ℤ) ∣ vSeq r s 2) {m : ℕ} (hm : 2 ≤ m) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) m) = jacobiSym (r * (r + s)) p := by
  have h₂ := unitPartChar_cSeq_two_of_dvd_vSeq_two hrs hs (by lia) hp
  rcases hm.eq_or_lt with rfl | hm
  · exact h₂
  rw [unitPartChar_cSeq_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero _ (n := 2) (by norm_num) hp
    (not_dvd_left_of_dvd_vSeq hrs le_rfl Fact.out (by lia) hp) hm,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_one hp4, one_mul, h₂]

/-- **(R2)** At primes `p, q ≡ 3 (mod 4)` dividing `v_2`, the character `χ_p χ_q` is constant from
`c_2` on: by reflection, both change sign after `c_2`. -/
theorem unitPartChar_mul_unitPartChar_cSeq_of_dvd_vSeq_two {q : ℕ} [Fact q.Prime]
    (hrs : IsCoprime r s) (hs : s ≠ 0) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hp : (p : ℤ) ∣ vSeq r s 2) (hq : (q : ℤ) ∣ vSeq r s 2) {m : ℕ} (hm : 2 ≤ m) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) m) *
        unitPartChar q (quadraticChar (ZMod q)) (cSeq ((r : ℚ) / s) m) =
      jacobiSym (r * (r + s)) p * jacobiSym (r * (r + s)) q := by
  have hp₂ := unitPartChar_cSeq_two_of_dvd_vSeq_two hrs hs (by lia) hp
  have hq₂ := unitPartChar_cSeq_two_of_dvd_vSeq_two hrs hs (by lia) hq
  rcases hm.eq_or_lt with rfl | hm
  · rw [hp₂, hq₂]
  rw [unitPartChar_cSeq_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero _ (n := 2) (by norm_num) hp
    (not_dvd_left_of_dvd_vSeq hrs le_rfl Fact.out (by lia) hp) hm,
    unitPartChar_cSeq_of_dvd_vSeq hrs (pow_one q).symm one_ne_zero _ (n := 2) (by norm_num) hq
    (not_dvd_left_of_dvd_vSeq hrs le_rfl Fact.out (by lia) hq) hm,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_three hq4, hp₂, hq₂]
  ring

/-- **(R3)** At a prime `p ≡ 1 (mod 4)` dividing `v_3` with `((r + s) w_3 / p) = 1`, the
character `χ_p` is constant from `c_2` on: by reflection from `c_3` on, and
`χ_p(c_2 c_3) = ((r + s) w_3 / p)`. -/
theorem unitPartChar_cSeq_of_dvd_vSeq_three (hrs : IsCoprime r s) (hs : s ≠ 0) (hp4 : p % 4 = 1)
    (hp : (p : ℤ) ∣ vSeq r s 3) (h : jacobiSym ((r + s) * wSeq r s 3) p = 1) {m : ℕ}
    (hm : 2 ≤ m) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) m) = jacobiSym (r * (r + s)) p := by
  have hp' := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hpr := not_dvd_left_of_dvd_vSeq hrs (by norm_num) Fact.out (by lia) hp
  have hpw : ¬(p : ℤ) ∣ (r + s) * wSeq r s 3 := fun hd ↦ by simp [jacobiSym_eq_zero_of_dvd hd] at h
  have hw3 : ¬(p : ℤ) ∣ wSeq r s 3 := fun hd ↦ hpw (hd.mul_left _)
  have h₂ := unitPartChar_cSeq_eq_jacobiSym (p := p) hs le_rfl (n := 2)
    (by simpa using hp'.not_dvd_mul hpr fun hd ↦ hpw (hd.mul_right _))
  have h₃ := unitPartChar_cSeq_eq_jacobiSym (p := p) hs (n := 3) (by norm_num)
    (hp'.not_dvd_mul hpr hw3)
  have hJ : jacobiSym (r * wSeq r s 3) p = jacobiSym (r * (r + s)) p := by
    have e := congr(jacobiSym $(show r * wSeq r s 3 * ((r + s) * wSeq r s 3) =
      r * (r + s) * wSeq r s 3 ^ 2 by ring) p)
    rwa [jacobiSym.mul_left, jacobiSym.mul_left (r * (r + s)), h, mul_one,
      jacobiSym.sq_one_of_not_dvd Fact.out hw3, mul_one] at e
  rw [wSeq_two] at h₂
  obtain rfl | rfl | hm : m = 2 ∨ m = 3 ∨ 3 < m := by lia
  · exact h₂
  · rw [h₃, hJ]
  rw [unitPartChar_cSeq_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero _ (n := 3) (by norm_num) hp
    hpr hm,
    ZMod.quadraticChar_neg_one_of_mod_four_eq_one hp4, one_mul, h₃, hJ]

/-! ### Primes of `w_3` -/

/-- At a prime `p ∣ w_3`, `χ_p` is `1` at `c_1`, `(-1 / p)` at `c_{3j+1}` (`j ≥ 1`),
`(-s(r + s) / p)` at `c_{3j+2}`, and `χ_p(c_3)` at `c_{3j}` (`j ≥ 1`): the values of
`QuadraticIterates.unitPartChar_cSeq_one_of_dvd_wSeq_three` and its companions. -/
private lemma quadraticChar_values_of_dvd_wSeq_three (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hp : (p : ℤ) ∣ wSeq r s 3) :
    unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) 1) = 1 ∧
      (∀ j ≥ 1, unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) (3 * j + 1)) =
        quadraticChar (ZMod p) (-1)) ∧
      (∀ j, unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) (3 * j + 2)) =
        jacobiSym (-(s * (r + s))) p) ∧
      ∀ j ≥ 1, unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) (3 * j)) =
        unitPartChar p (quadraticChar (ZMod p)) (cSeq ((r : ℚ) / s) 3) := by
  have hN : p = p ^ 1 := (pow_one p).symm
  refine ⟨unitPartChar_cSeq_one_of_dvd_wSeq_three hrs hN one_ne_zero hp _, fun j hj ↦
    unitPartChar_cSeq_three_mul_add_one_of_dvd_wSeq_three hrs hN one_ne_zero hp _ hj, fun j ↦ ?_,
    fun j hj ↦ unitPartChar_cSeq_three_mul_of_dvd_wSeq_three hrs hs hN one_ne_zero hp _ hj⟩
  rw [unitPartChar_cSeq_three_mul_add_two_of_dvd_wSeq_three hrs hN one_ne_zero hp _ j,
    show -((s : ZMod p) * (r + s)) = ((-(s * (r + s)) : ℤ) : ZMod p) by push_cast; ring]
  exact jacobiSym.legendreSym.to_jacobiSym p _

/-- The characters at the primes `p, q ∣ w_3` combine to a character that is `1` at `c_1`, `-1`
at the other `c_n` with `3 ∤ n`, and constant on the `c_{3j}`: `χ_q` if `(-s(r + s) / q) = -1`,
otherwise `χ_p` or `χ_p χ_q` according to `(-1 / p)`. -/
private lemma exists_mulChar_of_dvd_wSeq_three (hrs : IsCoprime r s) (hs : s ≠ 0) {q : ℕ}
    [Fact q.Prime] (hq4 : q % 4 = 3) (hq : (q : ℤ) ∣ wSeq r s 3) (hp : (p : ℤ) ∣ wSeq r s 3)
    (hy : jacobiSym (-(s * (r + s))) p = -1) :
    ∃ Φ : MulChar ℚ ℤ, Φ (cSeq ((r : ℚ) / s) 1) = 1 ∧
      (∀ j ≥ 1, Φ (cSeq ((r : ℚ) / s) (3 * j + 1)) = -1) ∧
      (∀ j, Φ (cSeq ((r : ℚ) / s) (3 * j + 2)) = -1) ∧
      ∀ j ≥ 1, Φ (cSeq ((r : ℚ) / s) (3 * j)) = Φ (cSeq ((r : ℚ) / s) 3) := by
  obtain ⟨p₁, p₂, p₃, p₀⟩ := quadraticChar_values_of_dvd_wSeq_three hrs hs hp
  obtain ⟨q₁, q₂, q₃, q₀⟩ := quadraticChar_values_of_dvd_wSeq_three hrs hs hq
  have hq' := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  have hqs := fun h ↦ hq'.not_isUnit
    ((isCoprime_wSeq_right hrs (n := 3) (by norm_num)).isUnit_of_dvd' hq h)
  have hq1 := ZMod.quadraticChar_neg_one_of_mod_four_eq_three hq4
  have hyq : jacobiSym (-(s * (r + s))) q = 1 ∨ jacobiSym (-(s * (r + s))) q = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    refine legendreSym.eq_one_or_neg_one q ?_
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg]
    exact hq'.not_dvd_mul hqs (not_dvd_add_of_dvd_wSeq_three hrs hq)
  rcases hyq with hyq | hyq
  · rcases quadraticChar_dichotomy (F := ZMod p) (neg_ne_zero.mpr one_ne_zero) with hp1 | hp1
    · refine ⟨unitPartChar p (quadraticChar (ZMod p)) * unitPartChar q (quadraticChar (ZMod q)),
        ?_, fun j hj ↦ ?_, fun j ↦ ?_, fun j hj ↦ ?_⟩ <;>
        simp only [MulChar.coeToFun_mul, Pi.mul_apply]
      exacts [by rw [p₁, q₁, mul_one], by rw [p₂ j hj, q₂ j hj, hp1, hq1, one_mul],
        by rw [p₃ j, q₃ j, hy, hyq, mul_one], by rw [p₀ j hj, q₀ j hj]]
    · exact ⟨_, p₁, fun j hj ↦ (p₂ j hj).trans hp1, fun j ↦ (p₃ j).trans hy, p₀⟩
  · exact ⟨_, q₁, fun j hj ↦ (q₂ j hj).trans hq1, fun j ↦ (q₃ j).trans hyq, q₀⟩

/-- A character `Φ` that is `1` at `v 1`, `-1` at the `v n` with `n ≥ 2` and `3 ∤ n`, and `±1`
and constant on the `v (3j)`, together with a character `Λ` that is `-1` exactly at the multiples
of `3`, yields `τ`: `Φ` itself, or `Φ Λ`. -/
private lemma hasCharPattern_neg_mulSingle_one_of_three {M : Type*} [CommMonoid M] {v : ℕ → M}
    {Φ Λ : MulChar M ℤ} (h₁ : Φ (v 1) = 1) (h₂ : ∀ j ≥ 1, Φ (v (3 * j + 1)) = -1)
    (h₃ : ∀ j, Φ (v (3 * j + 2)) = -1) (h₀ : ∀ j ≥ 1, Φ (v (3 * j)) = Φ (v 3))
    (hu : Φ (v 3) = 1 ∨ Φ (v 3) = -1) (hΛ₁ : ∀ j, Λ (v (3 * j + 1)) = 1)
    (hΛ₂ : ∀ j, Λ (v (3 * j + 2)) = 1) (hΛ₀ : ∀ j ≥ 1, Λ (v (3 * j)) = -1) :
    HasCharPattern v 1 (-Pi.mulSingle 1 (-1)) := by
  have key (Ψ : MulChar M ℤ) (hΨ₁ : Ψ (v 1) = 1) (hΨ₂ : ∀ j ≥ 1, Ψ (v (3 * j + 1)) = -1)
      (hΨ₃ : ∀ j, Ψ (v (3 * j + 2)) = -1) (hΨ₀ : ∀ j ≥ 1, Ψ (v (3 * j)) = -1) :
      HasCharPattern v 1 (-Pi.mulSingle 1 (-1)) := by
    refine hasCharPattern_neg_mulSingle_one_of_apply Ψ hΨ₁ fun n hn ↦ ?_
    obtain ⟨j, i, hi, rfl⟩ : ∃ j i, i < 3 ∧ n = 3 * j + i :=
      ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
    interval_cases i
    exacts [hΨ₀ j (by lia), hΨ₂ j (by lia), hΨ₃ j]
  rcases hu with hu | hu
  · exact key (Φ * Λ) (by simpa [h₁] using hΛ₁ 0) (fun j hj ↦ by simp [h₂ j hj, hΛ₁ j])
      (fun j ↦ by simp [h₃ j, hΛ₂ j]) fun j hj ↦ by simp [h₀ j hj, hu, hΛ₀ j hj]
  · exact key Φ h₁ h₂ h₃ fun j hj ↦ (h₀ j hj).trans hu

/-- **(P3)** If `w_3 ≠ ±□`, a prime `q ≡ 3 (mod 4)` divides `w_3`, and `(-s(r + s) / p) = -1`
for some prime `p ∣ w_3`, then `a` has `τ`. Modulo the primes of `w_3`, `0` has period `3`; a
product of their characters is `(1, -1, u, -1, -1, u, …)`, and `val_ℓ` for a prime `ℓ` with
`v_ℓ(w_3)` odd corrects the multiples of `3`. -/
theorem hasCharPattern_neg_mulSingle_one_of_dvd_wSeq_three (hrs : IsCoprime r s) (hs : s ≠ 0)
    (hw : ¬IsSquare (wSeq r s 3)) (hw' : ¬IsSquare (-wSeq r s 3)) {q : ℕ} [Fact q.Prime]
    (hq4 : q % 4 = 3) (hq : (q : ℤ) ∣ wSeq r s 3) (hp : (p : ℤ) ∣ wSeq r s 3)
    (hy : jacobiSym (-(s * (r + s))) p = -1) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-Pi.mulSingle 1 (-1)) := by
  obtain ⟨ℓ, _, hℓ, hval⟩ := exists_prime_dvd_valChar_eq_neg_one hw hw'
  obtain ⟨Φ, h₁, h₂, h₃, h₀⟩ := exists_mulChar_of_dvd_wSeq_three hrs hs hq4 hq hp hy
  have hr : r ≠ 0 := fun hr ↦ (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).not_isUnit
    ((isCoprime_wSeq_left hrs (n := 3) (by norm_num)).isUnit_of_dvd' hq (hr ▸ dvd_zero _))
  have hw0 : wSeq r s 3 ≠ 0 := fun h ↦ hw (h ▸ ⟨0, by simp⟩)
  have hc : cSeq ((r : ℚ) / s) 3 ≠ 0 := by
    rw [cSeq_div_eq r hs (by norm_num)]
    exact div_ne_zero (mul_ne_zero (mod_cast hr) (mod_cast hw0)) (pow_ne_zero _ (mod_cast hs))
  exact hasCharPattern_neg_mulSingle_one_of_three h₁ h₂ h₃ h₀
    (Φ.apply_eq_one_or_eq_neg_one hc.isUnit)
    (fun j ↦ valChar_cSeq_three_mul_add_one_of_dvd_wSeq_three hrs hℓ j)
    (fun j ↦ valChar_cSeq_three_mul_add_two_of_dvd_wSeq_three hrs hℓ j)
    fun j hj ↦ (valChar_cSeq_three_mul_of_dvd_wSeq_three hrs hs hℓ hj).trans hval

end QuadraticIterates
