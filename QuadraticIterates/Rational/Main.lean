/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.Residues
public import QuadraticIterates.Rational.SquareClasses

import QuadraticIterates.Mathlib.RingTheory.Radical.NatInt
import QuadraticIterates.Rational.GammaTwo

/-!
# Theorems R⁺ and R⁻: maximal Galois groups for rational parameters

The two theorems of the rational program, for `a = r/s` with `r` and `s` coprime, `s > 0`:

* `QuadraticIterates.nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCertificate`
  (**Theorem R⁺**, the positive world `a > -1`, `a ≠ 0`);
* `QuadraticIterates.nonempty_mulEquiv_of_two_mul_le_neg_of_twoAdicClass_of_squarefreeCertificate`
  (**Theorem R⁻**, Stoll's world `a ≤ -2`).

In both, `-rs` is not a square, the parameter lies in one of the 2-adic classes
(`QuadraticIterates.TwoAdicClass`), and one of the squarefree-level certificates
(`QuadraticIterates.SquarefreeCertificate`) holds; the conclusion is `Ω_n ≅ [C₂]ⁿ` for all `n`.
Both are instances of the uniform theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate` for `a = εr/s` with
a positive sequence `w = QuadraticIterates.wSeq r s ε`: in the 2-adic classes `β_n` is not a square
for every non-squarefree `n` (`QuadraticIterates.not_isSquare_betaInt_of_twoAdicClass_of_two_le`),
under a certificate for every squarefree `n ≥ 2`
(`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_squarefreeCertificate`), and the
shared-part lemma `QuadraticIterates.nonempty_mulEquiv_of_forall_not_isSquare_abs_betaInt`
concludes.

Part of the extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some
iterated polynomials*, Arch. Math. **59** (1992), 239-244, to rational parameters `a`; see
`QuadraticIterates.Rational`.
-/

@[expose] public section

open UniqueFactorizationMonoid

namespace QuadraticIterates

variable {r s ε : ℤ}

/-! ### The squarefree-level certificates -/

/-- **The squarefree-level certificates.** A certificate that `β_n` is not a square for every
squarefree `n ≥ 2`, for the parameter `a = εr/s` with sequence `w = QuadraticIterates.wSeq r s ε`
(`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_squarefreeCertificate`): one of the
four mechanisms of the squarefree levels, each with its modulus. -/
inductive SquarefreeCertificate (r s ε : ℤ) : Prop
  /-- A divisor `M` of `s` modulo which `r` is not a square
  (`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_dvd_of_not_isSquare`). -/
  | dvd (M : ℕ) (hM : (M : ℤ) ∣ s) (h : ¬IsSquare (r : ZMod M))
  /-- A divisor `M` of `r + (1 + ε)s`, the numerator of `γ_1 + γ_2`, modulo which `-s` is not a
  square (`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_dvd_reflNum_one`). -/
  | reflNum (M : ℕ) (hM : (M : ℤ) ∣ r + (1 + ε) * s) (h : ¬IsSquare (-(s : ZMod M)))
  /-- `s` even, `r ≡ 3 mod 4` and `r + εs ≢ 1 mod 8`: residues modulo `8`
  (`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_odd_of_even`,
  `QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_even_of_even`). -/
  | even (hs : s % 2 = 0) (hr : r % 4 = 3) (h : (r + ε * s) % 8 ≠ 1)
  /-- `β_2 = r + εs`, the numerator of `γ_2`, is not a square, and a divisor `M` of it modulo which
  `εs` is not a square (`QuadraticIterates.not_isSquare_betaInt_of_squarefree_of_dvd_wSeq_two`). -/
  | gammaTwo (hw2 : ¬IsSquare (r + ε * s)) (M : ℕ) (hM : (M : ℤ) ∣ r + ε * s)
    (h : ¬IsSquare ((ε : ZMod M) * s))

/-- The squarefree-level certificate as the disjunction of its four clauses. -/
theorem squarefreeCertificate_iff : SquarefreeCertificate r s ε ↔
    (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + (1 + ε) * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + ε * s) % 8 ≠ 1) ∨
          (¬IsSquare (r + ε * s) ∧
            ∃ M : ℕ, (M : ℤ) ∣ r + ε * s ∧ ¬IsSquare ((ε : ZMod M) * s)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | dvd M hM h => exact .inl ⟨M, hM, h⟩
    | reflNum M hM h => exact .inr (.inl ⟨M, hM, h⟩)
    | even hs hr h => exact .inr (.inr (.inl ⟨hs, hr, h⟩))
    | gammaTwo hw2 M hM h => exact .inr (.inr (.inr ⟨hw2, M, hM, h⟩))
  · rcases h with ⟨M, hM, h⟩ | ⟨M, hM, h⟩ | ⟨hs, hr, h⟩ | ⟨hw2, M, hM, h⟩
    · exact .dvd M hM h
    · exact .reflNum M hM h
    · exact .even hs hr h
    · exact .gammaTwo hw2 M hM h

/-- **Squarefree levels.** Under a certificate `QuadraticIterates.SquarefreeCertificate r s ε`,
`β_n` is not a square for every squarefree `n ≥ 2`. -/
theorem not_isSquare_betaInt_of_squarefree_of_squarefreeCertificate (hs : s ≠ 0)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, wSeq r s ε n ≠ 0)
    (hcert : SquarefreeCertificate r s ε) {n : ℕ} (hn : 2 ≤ n) (hsf : Squarefree n) :
    ¬IsSquare (betaInt r s ε n) := by
  cases hcert with
  | dvd M hM h =>
    exact not_isSquare_betaInt_of_squarefree_of_dvd_of_not_isSquare hs hrs hε hw hn hsf hM h
  | reflNum M hM h =>
    exact not_isSquare_betaInt_of_squarefree_of_dvd_reflNum_one hs hrs hε hw hn hsf
      (reflNum_one ▸ hM) h
  | even hs2 hr h8 =>
    rcases Nat.even_or_odd n with hne | hno
    · exact not_isSquare_betaInt_of_squarefree_of_even_of_even hs2 hs hrs hε hw hsf hne h8
    · exact not_isSquare_betaInt_of_squarefree_of_odd_of_even hs2 hs hrs hε hw hn hsf hno hr
  | gammaTwo hw2 M hM h =>
    rcases (show n = 2 ∨ 3 ≤ n by lia) with rfl | hn3
    · rwa [betaInt_two hs hrs hε hw]
    · exact not_isSquare_betaInt_of_squarefree_of_dvd_wSeq_two hs hrs hε hw hn3 hsf
        (wSeq_two r s ε ▸ hM) h

/-! ### The uniform theorem and its two sign instances -/

/-- **Non-squarefree levels.** In the 2-adic classes, `β_n` is not a square for every `n ≥ 2`
that is not squarefree: `QuadraticIterates.not_isSquare_betaInt_of_twoAdicClass_of_two_le` with
`k = n / rad n ≥ 2`. -/
theorem not_isSquare_betaInt_of_twoAdicClass_of_not_squarefree (hs : 0 < s) (hrs : IsCoprime r s)
    (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, 0 < wSeq r s ε n) (hc : TwoAdicClass r s ε) {n : ℕ}
    (hn : 2 ≤ n) (hsf : ¬Squarefree n) : ¬IsSquare (betaInt r s ε n) := by
  have hk2 := Nat.two_le_div_radical_of_not_squarefree (by lia) hsf
  exact not_isSquare_betaInt_of_twoAdicClass_of_two_le hs.ne' hrs hε (fun n hn ↦ (hw n hn).ne') hc
    hn (Nat.div_mul_cancel radical_dvd_self).symm hk2
    (reflNum_pos hs.le hw (one_le_two.trans hk2)).le

/-- In the 2-adic classes and under a squarefree-level certificate, `β_n` is not a square for any
`n ≥ 2`. -/
theorem not_isSquare_betaInt_of_twoAdicClass_of_squarefreeCertificate (hs : 0 < s)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, 0 < wSeq r s ε n)
    (hc : TwoAdicClass r s ε) (hcert : SquarefreeCertificate r s ε) {n : ℕ} (hn : 2 ≤ n) :
    ¬IsSquare (betaInt r s ε n) :=
  (em (Squarefree n)).elim
    (not_isSquare_betaInt_of_squarefree_of_squarefreeCertificate hs.ne' hrs hε
      (fun n hn ↦ (hw n hn).ne') hcert hn)
    (not_isSquare_betaInt_of_twoAdicClass_of_not_squarefree hs hrs hε hw hc hn)

/-- **The uniform theorem.** For `a = εr/s` with `s > 0`, all `w_n > 0`, `(r, s, ε)` in a 2-adic
class, `-εrs` not a square and a squarefree-level certificate, `Ω_n ≅ [C₂]ⁿ` for all `n`: the
shared-part lemma `QuadraticIterates.nonempty_mulEquiv_of_forall_not_isSquare_abs_betaInt`, with
`|β_n| = β_n`. Theorems R⁺ and R⁻ are its two sign instances. -/
theorem nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate (hs : 0 < s)
    (hrs : IsCoprime r s) (hε : ε ^ 2 = 1) (hw : ∀ n ≥ 1, 0 < wSeq r s ε n)
    (hc : TwoAdicClass r s ε) (ha : ¬IsSquare (-(ε * r * s)))
    (hcert : SquarefreeCertificate r s ε) (n : ℕ) :
    Nonempty (GaloisGroup (ε * r / s : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_forall_not_isSquare_abs_betaInt hs.ne' hrs hε (fun n hn ↦ (hw n hn).ne') ha
    (fun _ hn ↦ (abs_of_pos (betaInt_pos hs.ne' hrs hε hw (one_le_two.trans hn))).symm ▸
      not_isSquare_betaInt_of_twoAdicClass_of_squarefreeCertificate hs hrs hε hw hc hcert hn) n

/-- **Theorem R⁺** (the positive world). Let `a = r/s` with `s > 0`, `r` coprime to `s` and
`a > -1`, `-rs` not a square, `(r, s, 1)` in a 2-adic class (`QuadraticIterates.TwoAdicClass`),
and a squarefree-level certificate (`QuadraticIterates.SquarefreeCertificate`). Then
`Ω_n ≅ [C₂]ⁿ` for all `n`. The sequence `w` of `a` is positive for `a > 0` and for `-1 < a < 0`. -/
theorem nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCertificate (hs : 0 < s)
    (hrs : IsCoprime r s) (hr : -s < r) (hc : TwoAdicClass r s 1) (ha : ¬IsSquare (-(r * s)))
    (hcert : SquarefreeCertificate r s 1) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) := by
  have hr0 : r ≠ 0 := fun h ↦ ha (by simp [h])
  have hw : ∀ n ≥ 1, 0 < wSeq r s 1 n :=
    (lt_or_gt_of_ne hr0).elim (fun h ↦ wSeq_pos_of_neg_lt h hr) fun h ↦ wSeq_pos_of_pos h hs
  exact (show ((1 : ℤ) : ℚ) * r / s = (r / s : ℚ) by simp) ▸
    nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate hs hrs (one_pow 2) hw hc
      (by rwa [one_mul]) hcert n

/-- **Theorem R⁻** (Stoll's world). Let `a = r/s ≤ -2` with `s > 0` and `r` coprime to `s`,
`-rs` not a square, `(-r, s, -1)` in a 2-adic class (`QuadraticIterates.TwoAdicClass`), and a
squarefree-level certificate (`QuadraticIterates.SquarefreeCertificate`) for `(-r, s, -1)`. Then
`Ω_n ≅ [C₂]ⁿ` for all `n`. The sequence `w` of `(-r, s, -1)` is the sequence of `a` in Stoll's
normalization `a = -|r|/s`, positive for `a ≤ -2`. -/
theorem nonempty_mulEquiv_of_two_mul_le_neg_of_twoAdicClass_of_squarefreeCertificate (hs : 0 < s)
    (hrs : IsCoprime r s) (hr : 2 * s ≤ -r) (hc : TwoAdicClass (-r) s (-1))
    (ha : ¬IsSquare (-(r * s))) (hcert : SquarefreeCertificate (-r) s (-1)) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  (show ((-1 : ℤ) : ℚ) * ((-r : ℤ) : ℚ) / s = (r / s : ℚ) by simp) ▸
    nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate hs hrs.neg_left neg_one_sq
      (wSeq_pos_of_two_mul_le hs hr) hc (by simpa using ha) hcert n

end QuadraticIterates

end
