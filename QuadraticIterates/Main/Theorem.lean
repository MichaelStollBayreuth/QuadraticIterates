/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Main.Criteria
public import QuadraticIterates.Main.TwoAdic

import QuadraticIterates.Characters.Criterion
import QuadraticIterates.Galois.Criterion
import QuadraticIterates.Mathlib.Data.Nat.Factorization.Basic
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic
import QuadraticIterates.Patterns.Dyadic
import QuadraticIterates.Patterns.Reflection
import QuadraticIterates.Sequence.Signs

/-!
# The main theorem

Surjectivity of the arboreal Galois representation of `X² + a` for rational `a = r/s`: the patterns
`φ₀` and `φ₁` along `(c_n)` and the `2`-adic classes (C1)–(C3) of
`QuadraticIterates.TwoAdicClass` give `Ω_n ≅ [C₂]ⁿ` for all `n`, and any two of the three lists of
criteria `QuadraticIterates.NegAllCriterion`, `QuadraticIterates.NegFirstCriterion` and
`QuadraticIterates.NegTailCriterion` supply the two patterns.

## Main statements

* `QuadraticIterates.forall_nonempty_mulEquiv_of_forall_dvd_vSeq`: reflection at every level.
* `QuadraticIterates.hasCharPattern_mulSingle_of_twoAdicClass`: in the `2`-adic classes,
  `φ₀` gives `φ_n` for every `n ≥ 2`.
* `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern`: the main theorem,
  abstract form.
* `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`: the main theorem.
* `QuadraticIterates.forall_nonempty_mulEquiv_iff_of_le_neg_two`: Li's theorem of 2020 for
  rational parameters `a ≤ -2`.
* `QuadraticIterates.hasCharPattern_mulSingle_of_prime_dvd_uSeq`: period two with `val₂` for
  `a ≡ 1 mod 4`.
* `QuadraticIterates.hasCharPattern_mulSingle_of_odd`: for `a ≡ 1 mod 4`, `φ₀` gives `φ_n` at
  every odd level `n ≥ 3`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-- **Reflection at every level**: if `a = r/s` has `φ₀` and `φ₁`, and for every `n ≥ 2` the
integer `v_n` is divisible by a prime `p ≡ 3 (mod 4)` not dividing `r`, or by `4` with `r` odd, then
`Ω_n ≅ [C₂]ⁿ` for all `n`. -/
theorem forall_nonempty_mulEquiv_of_forall_dvd_vSeq (hrs : IsCoprime r s)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1))
    (h₁ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)))
    (h : ∀ n ≥ 2, (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ vSeq r s n ∧ ¬(p : ℤ) ∣ r) ∨
      (4 ∣ vSeq r s n ∧ ¬2 ∣ r)) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  refine forall_nonempty_mulEquiv_of_forall_hasCharPattern (fun n hn ↦ ?_) n
  rcases hn.eq_or_lt with rfl | hn
  · exact h₁
  rcases h n hn with ⟨p, hp, hp4, hpv, hpr⟩ | ⟨h4, hr⟩
  · have := Fact.mk hp
    exact hasCharPattern_mulSingle_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero
      (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) (by lia) (by simpa using hpv) hpr
      (h₀.mono (by lia))
  · exact hasCharPattern_mulSingle_of_dvd_vSeq (p := 2) hrs (N := 4) rfl two_ne_zero
      (show ZMod.χ₄ (-1) = -1 by decide) (by lia) (mod_cast h4) (mod_cast hr) (h₀.mono (by lia))

/-- For `a = r/s ∈ 𝒜` with sign `ε` in one of the `2`-adic classes (C1)–(C3), `φ₀` gives `φ_n`
for every `n ≥ 2`: a prime `p ≡ 3 (mod 4)` divides `v_n`
(`QuadraticIterates.exists_prime_dvd_vSeq_of_twoAdicClass`), and `χ_p` reflects at `c_n`
(`QuadraticIterates.hasCharPattern_mulSingle_of_dvd_vSeq`). -/
theorem hasCharPattern_mulSingle_of_twoAdicClass (hrs : IsCoprime r s) (hs : 0 < s) {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ}
    (hn : 2 ≤ n) : HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact h₀.ne_zero le_rfl (by simp) (by simp)
  obtain ⟨p, hp, hp4, hpv, hpr⟩ := exists_prime_dvd_vSeq_of_twoAdicClass hrs hs hr0 hε hc hn
  have := Fact.mk hp
  exact hasCharPattern_mulSingle_of_dvd_vSeq hrs (pow_one p).symm one_ne_zero
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) (by lia) (by simpa using hpv) hpr
    (h₀.mono (by lia))

/-- **The main theorem, abstract form**: for `a = r/s ∈ 𝒜` with sign `ε` in one of the `2`-adic
classes (C1)–(C3), `φ₀` and `φ₁` give `Ω_n ≅ [C₂]ⁿ` for all `n`
(`QuadraticIterates.hasCharPattern_mulSingle_of_twoAdicClass` for `n ≥ 2`). -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern (hrs : IsCoprime r s) (hs : 0 < s)
    {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1))
    (h₁ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1))) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) := by
  refine forall_nonempty_mulEquiv_of_forall_hasCharPattern (fun n hn ↦ ?_) n
  rcases hn.eq_or_lt with rfl | hn
  exacts [h₁, hasCharPattern_mulSingle_of_twoAdicClass hrs hs hε hc h₀ hn]

/-- **The main theorem** for rational parameters: let `a = r/s` with `r, s` coprime, `s > 0`, and
either `a ≤ -2` and `ε = -1`, or `a³ + 2a² + 2a + 2 > 0` and `ε = 1`. If `(r, s, ε)` is in one of
the `2`-adic classes (C1)–(C3) and two of the three lists of criteria (Z), (O), (T) apply, then
`Ω_n ≅ [C₂]ⁿ` for all `n`: the arboreal Galois representation of `X² + a` is surjective. -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_criteria (hrs : IsCoprime r s) (hs : 0 < s)
    {ε : ℤ}
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
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

/-- For `a = r/s ≤ -2` with `r ≡ 3` and `s ≡ 1 (mod 4)`, `φ₀` and `-(a + 1) ≠ □` give `φ₁`: by
(O3) if `s ≠ □`, and by (T3) and `φ₀ τ = φ₁` if `s = □`. -/
private lemma hasCharPattern_mulSingle_one_of_le_neg_two (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r ≤ -2 * s) (hs4 : s % 4 = 1) (hr4 : r % 4 = 3)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) (h : ¬IsSquare (-((r : ℚ) / s + 1))) :
    HasCharPattern (cSeq ((r : ℚ) / s)) 1 (Pi.mulSingle 1 (-1)) := by
  by_cases hsq : IsSquare s
  · obtain ⟨u, hu⟩ := hsq
    refine hasCharPattern_mulSingle_of_neg_of_neg_mulSingle h₀
      (hasCharPattern_neg_mulSingle_one_of_negTailCriterion hrs hs
        (.not_isSquare_add (fun ⟨t, ht⟩ ↦ by lia [mul_self_nonneg t]) (fun ⟨t, ht⟩ ↦ h
          ⟨t / u, ?_⟩) (.inl (by lia))))
    rw [div_mul_div_comm, ← Int.cast_mul, ← Int.cast_mul, ← ht, ← hu]
    push_cast
    field
  · obtain ⟨p, k, m, hp, hk, hsm, hm⟩ := Int.exists_prime_pow_mul_of_not_isSquare hs.le hsq
    have hps : (p : ℤ) ∣ s := hsm ▸ (dvd_pow_self _ hk.pos.ne').mul_right m
    exact hasCharPattern_mulSingle_one_of_negFirstCriterion hrs hs
      (.dvd_right p k m hp (by rintro rfl; lia) hk.pos hsm hm (.inl hk))

/-- **Li 2020 for rational parameters**: for `a = r/s ≤ -2` with `r ≡ 3` and `s ≡ 1 (mod 4)` and
`φ₀` (for instance `|r| ≠ □`), the arboreal representation of `X² + a` is surjective if and only
if `-(a + 1)` is not a square; if it is, `c₁ c₂ = a² · (-(a + 1))` is a square. -/
theorem forall_nonempty_mulEquiv_iff_of_le_neg_two (hrs : IsCoprime r s) (hs : 0 < s)
    (ha : r ≤ -2 * s) (hs4 : s % 4 = 1) (hr4 : r % 4 = 3)
    (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) :
    (∀ n, Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n)) ↔
      ¬IsSquare (-((r : ℚ) / s + 1)) := by
  refine ⟨fun h ⟨t, ht⟩ ↦ (nonempty_mulEquiv_iff_twoIndependent _ 2).mp (h 2) Finset.univ
    Finset.univ_nonempty ⟨(r : ℚ) / s * t, ?_⟩, fun h ↦
    nonempty_mulEquiv_of_twoAdicClass_of_hasCharPattern hrs hs (.inl ⟨ha, rfl⟩)
      (.inl ⟨Int.odd_iff.mpr (by lia), by rw [Int.ModEq]; lia⟩) h₀
      (hasCharPattern_mulSingle_one_of_le_neg_two hrs hs ha hs4 hr4 h₀ h)⟩
  simp [Fin.prod_univ_two, cSeq_two]
  linear_combination ((r : ℚ) / s) ^ 2 * ht

/-- **Period two with `val₂`** for `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`): a prime
`p ≡ 3 (mod 4)` dividing `u_n` and not `r + s` gives `φ_n` from `φ₀`. -/
theorem hasCharPattern_mulSingle_of_prime_dvd_uSeq (hrs : IsCoprime r s) (hs : Odd s)
    (h4 : r ≡ s [ZMOD 4]) (h₀ : HasCharPattern (cSeq ((r : ℚ) / s)) 1 (-1)) {n : ℕ} (hn : 1 ≤ n)
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hpu : (p : ℤ) ∣ uSeq r s n)
    (hprs : ¬(p : ℤ) ∣ r + s) : HasCharPattern (cSeq ((r : ℚ) / s)) n (Pi.mulSingle n (-1)) := by
  refine hasCharPattern_mulSingle_of_dvd_uSeq hrs (pow_one p).symm one_ne_zero
    (ZMod.quadraticChar_neg_one_of_mod_four_eq_three hp4) hn (by simpa using hpu) hprs
    (h₀.mono hn) (χ := Rat.valChar 2) ?_
    fun m hm ↦ valChar_two_cSeq_succ_of_modEq_four hrs hs h4 (by lia)
  have hc := h₀.ne_zero hn (by simp)
  rcases (Rat.valChar 2).apply_eq_one_or_eq_neg_one (Ne.isUnit hc) with h | h <;> simp [h]

/-- **Odd levels** for `a = r/s ≡ 1 mod 4` (`s` odd, `r ≡ s (mod 4)`) with `a ≤ -2`, or `a > -1`,
or `a < -1` and `c₃ < 0 < c₄`: `φ₀` gives `φ_n` for every odd `n ≥ 3`. Here `u_n > 0`, a prime
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
