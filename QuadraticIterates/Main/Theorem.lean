/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Main.Criteria
public import QuadraticIterates.Main.TwoAdic

import QuadraticIterates.Characters.Criterion
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Patterns.Reflection
import QuadraticIterates.Sequence.Signs

/-!
# The main theorem

Surjectivity of the arboreal Galois representation of `X² + a` for rational `a = r/s` with `a ≤ -2`
or `a³ + 2a² + 2a + 2 > 0`: the patterns `φ₀` and `φ₁` along `(c_n)` and the `2`-adic classes
(C1)–(C3) of `QuadraticIterates.TwoAdicClass` give `Ω_n ≅ [C₂]ⁿ` for all `n`, and any two of the
three lists of criteria `QuadraticIterates.NegAllCriterion`, `QuadraticIterates.NegFirstCriterion`
and `QuadraticIterates.NegTailCriterion` supply the two patterns.

## Main statements

* `QuadraticIterates.forall_nonempty_mulEquiv_of_forall_dvd_vSeq`: reflection at every level.
* `QuadraticIterates.hasCharPattern_mulSingle_of_twoAdicClass`: in the `2`-adic classes,
  `φ₀` gives `φ_n` for every `n ≥ 2`.
* `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern`: the main theorem,
  abstract form.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_hasCharPattern_of_twoAdicClass`: the main theorem
  as a characterization: in the `2`-adic classes, all levels are maximal iff `a` has `φ₀` and `φ₁`.
* `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`: the main theorem.
* `QuadraticIterates.hasCharPattern_mulSingle_of_prime_dvd_uSeq`: period two with `val₂` for
  `a ≡ 1 mod 4`.
* `QuadraticIterates.hasCharPattern_mulSingle_of_odd`: for `a ≡ 1 mod 4`, `φ₀` gives `φ_n` at
  every odd level `n ≥ 3`.

## Notation

In the docstrings, `𝒜` is the set of `a` with `a ≤ -2` (sign `ε = -1`) or `a³ + 2a² + 2a + 2 > 0`
(sign `ε = 1`); `χ_p` is the character `Rat.unitPartChar p (quadraticChar (ZMod p))` of `ℚ` at an
odd prime `p`, and `val₂` is `Rat.valChar 2`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- Reflection at a prime `p ≡ 3 (mod 4)` dividing `v_n`, `n ≥ 2`: `φ₀` gives `φ_n` through `χ_p`
(`QuadraticIterates.hasCharPattern_mulSingle_of_dvd_vSeq`); `p ∤ r` is automatic
(`QuadraticIterates.not_dvd_left_of_dvd_vSeq`). -/
private lemma hasCharPattern_mulSingle_of_prime_dvd_vSeq (hrs : IsCoprime r s)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ} (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 3) (hpv : (p : ℤ) ∣ vSeq r s n) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  have := Fact.mk hp
  exact hasCharPattern_mulSingle_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) (by lia) (by simpa using hpv)
    (not_dvd_left_of_dvd_vSeq hrs hn hp (by lia) hpv) (h₀.mono (by lia))

/-- **Reflection at every level**: if `a = r/s` has `φ₀` and `φ₁`, and for every `n ≥ 2` the
integer `v_n` is divisible by a prime `p ≡ 3 (mod 4)` not dividing `r`, or by `4` with `r` odd, then
`Ω_n ≅ [C₂]ⁿ` for all `n`. -/
theorem forall_nonempty_mulEquiv_of_forall_dvd_vSeq (hrs : IsCoprime r s)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1))
    (h₁ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)))
    (h : ∀ n ≥ 2, (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq r s n ∧ ¬(p : ℤ) ∣ r) ∨
      (4 ∣ vSeq r s n ∧ ¬2 ∣ r)) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  refine forall_nonempty_mulEquiv_of_hasCharPattern_of_forall_hasCharPattern h₁ (fun n hn ↦ ?_) n
  rcases h n hn with ⟨p, hp, hp4, hpv, -⟩ | ⟨h4, hr⟩
  · exact hasCharPattern_mulSingle_of_prime_dvd_vSeq hrs h₀ hn hp hp4 hpv
  · exact hasCharPattern_mulSingle_of_dvd_vSeq (p := 2) hrs (N := 4) rfl two_ne_zero
      (show ZMod.χ₄ (-1) = -1 by decide) (by lia) (mod_cast h4) (mod_cast hr) (h₀.mono (by lia))

/-- For `a = r/s ∈ 𝒜` with sign `ε` (`a ≤ -2` and `ε = -1`, or `a³ + 2a² + 2a + 2 > 0` and
`ε = 1`) in one of the `2`-adic classes (C1)–(C3), `φ₀` gives `φ_n` for every `n ≥ 2`: a prime
`p ≡ 3 (mod 4)` divides `v_n` (`QuadraticIterates.exists_prime_dvd_vSeq_of_twoAdicClass`), and
`χ_p` reflects at `c_n` (`QuadraticIterates.hasCharPattern_mulSingle_of_dvd_vSeq`). -/
theorem hasCharPattern_mulSingle_of_twoAdicClass (hrs : IsCoprime r s) (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1)
    (hc : TwoAdicClass r s ε) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ}
    (hn : 2 ≤ n) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  have hr0 : r ≠ 0 := fun h ↦ h₀.ne_zero le_rfl (by simp) (by simp [h])
  obtain ⟨p, hp, hp4, hpv, -⟩ := exists_prime_dvd_vSeq_of_twoAdicClass hrs hs hr0 hε hc hn
  exact hasCharPattern_mulSingle_of_prime_dvd_vSeq hrs h₀ hn hp hp4 hpv

/-- **The main theorem, abstract form**: for `a = r/s ∈ 𝒜` with sign `ε` (`a ≤ -2` and `ε = -1`,
or `a³ + 2a² + 2a + 2 > 0` and `ε = 1`) in one of the `2`-adic classes (C1)–(C3), `φ₀` and `φ₁`
give `Ω_n ≅ [C₂]ⁿ` for all `n` (`QuadraticIterates.hasCharPattern_mulSingle_of_twoAdicClass` for
`n ≥ 2`). -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern (hrs : IsCoprime r s) (hs : 0 < s)
    {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1)
    (hc : TwoAdicClass r s ε) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1))
    (h₁ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1))) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) :=
  forall_nonempty_mulEquiv_of_hasCharPattern_of_forall_hasCharPattern h₁
    (fun _ ↦ hasCharPattern_mulSingle_of_twoAdicClass hrs hs hε hc h₀) n

/-- **The main theorem as a characterization**: for `a = r/s ∈ 𝒜` with sign `ε` (`a ≤ -2` and
`ε = -1`, or `a³ + 2a² + 2a + 2 > 0` and `ε = 1`) in one of the `2`-adic classes (C1)–(C3), the
Galois groups `Ω_n` of the iterates of `X² + a` satisfy `Ω_n ≅ [C₂]ⁿ` for all `n` if and only if
`a` has `φ₀` and `φ₁` (the patterns `-1` and `Pi.mulSingle 1 (-1)` along `c_n` from `1` on).
Surjectivity gives every sign pattern
(`QuadraticIterates.hasCharPattern_one_of_forall_nonempty_mulEquiv`). -/
theorem forall_nonempty_mulEquiv_iff_hasCharPattern_of_twoAdicClass (hrs : IsCoprime r s)
    (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1) ∧
        HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) :=
  ⟨fun h ↦ ⟨hasCharPattern_one_of_forall_nonempty_mulEquiv h fun _ _ ↦ .inr rfl,
      hasCharPattern_one_of_forall_nonempty_mulEquiv h fun m _ ↦ by
        rcases eq_or_ne m 1 with rfl | hm <;> simp [*]⟩,
    fun ⟨h₀, h₁⟩ ↦ nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern hrs hs hε hc h₀ h₁⟩

/-- **The main theorem** for rational parameters: let `a = r/s` with `r, s` coprime, `s > 0`, and
either `a ≤ -2` and `ε = -1`, or `a³ + 2a² + 2a + 2 > 0` and `ε = 1`. If `(r, s, ε)` is in one of
the `2`-adic classes (C1)–(C3) and two of the three lists of criteria (Z), (O), (T) apply, then
`Ω_n ≅ [C₂]ⁿ` for all `n`: the arboreal Galois representation of `X² + a` is surjective. -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_criteria (hrs : IsCoprime r s) (hs : 0 < s) {ε : ℤ}
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1)
    (hc : TwoAdicClass r s ε)
    (h : NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  have hZ := hasCharPattern_neg_one_of_negAllCriterion hrs hs.ne'
  have hO := hasCharPattern_mulSingle_one_of_negFirstCriterion hrs hs
  have hT := hasCharPattern_neg_mulSingle_one_of_negTailCriterion hrs hs
  refine nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern hrs hs hε hc ?_ ?_ n <;>
  rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  exacts [hZ h₀, hZ h₀, hasCharPattern_neg_of_mulSingle_of_neg_mulSingle (hO h₀) (hT h₁), hO h₁,
    hasCharPattern_mulSingle_of_neg_of_neg_mulSingle (hZ h₀) (hT h₁), hO h₀]

/-- **Period two with `val₂`** for `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`): a prime
`p ≡ 3 (mod 4)` dividing `u_n` and not `r + s` gives `φ_n` from `φ₀`. -/
theorem hasCharPattern_mulSingle_of_prime_dvd_uSeq (hrs : IsCoprime r s) (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ} (hn : 1 ≤ n)
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hpu : (p : ℤ) ∣ uSeq r s n)
    (hprs : ¬(p : ℤ) ∣ r + s) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) :=
  hasCharPattern_mulSingle_of_dvd_uSeq hrs (pow_one p).symm one_ne_zero
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) hn (by simpa using hpu) hprs
    (h₀.mono hn) (χ := Rat.valChar 2) ((h₀.ne_zero hn (by simp)).isUnit.map _).ne_zero
    fun m hm ↦ valChar_two_cSeq_succ_of_modEq_four hrs hs h4 (by lia)

/-- **Odd levels** for `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`) with `a ≤ -2`, or `a > -1`,
or `a < -1` and `c_3 < 0 < c_4`: `φ₀` gives `φ_n` for every odd `n ≥ 3`. Here `u_n > 0`, a prime
`p ≡ 3 (mod 4)` divides `u_n` and not `r + s`, and `val₂` alternates. -/
theorem hasCharPattern_mulSingle_of_odd (hrs : IsCoprime r s) (hs : 0 < s) (hodd : Odd s)
    (h4 : r ≡ s [ZMOD 4])
    (ha : (r : ℚ) / s ≤ -2 ∨ -1 < (r : ℚ) / s ∨
      (r : ℚ) / s < -1 ∧ cSeq ((r : ℚ) / s) 3 < 0 ∧ 0 < cSeq ((r : ℚ) / s) 4)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  have hpos : 0 < uSeq r s n := uSeq_pos hs (by lia) <| by
    rcases ha with ha | ha | ⟨ha, h₃, h₄⟩
    exacts [cSeq_sq_sub_cSeq_add_pos_of_le_neg_two ha (by lia),
      cSeq_sq_sub_cSeq_add_pos_of_neg_one_lt ha (by lia),
      cSeq_sq_sub_cSeq_add_pos_of_odd ha h₃ h₄ hn ho]
  obtain ⟨p, hp, hp4, hpu, hprs⟩ := exists_prime_dvd_uSeq_of_odd hrs hodd h4 hn ho hpos
  have := Fact.mk hp
  exact hasCharPattern_mulSingle_of_prime_dvd_uSeq hrs hodd h4 h₀ (by lia) hp4 hpu hprs

end QuadraticIterates
