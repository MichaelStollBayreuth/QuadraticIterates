/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Main.Criteria
public import QuadraticIterates.Main.TwoAdic

import QuadraticIterates.Main.Theorem
import QuadraticIterates.Mathlib.Algebra.Ring.Int.Parity
import QuadraticIterates.Mathlib.Data.Nat.Prime.Basic
import QuadraticIterates.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QuadraticIterates.Mathlib.RingTheory.Coprime.Basic
import QuadraticIterates.Mathlib.RingTheory.Int.Basic
import QuadraticIterates.Mathlib.RingTheory.Multiplicity

/-!
# Theorems R⁺ and R⁻ from the main theorem

Theorems R⁺ (`a = r/s > -1`) and R⁻ (`a = -R/s ≤ -2`) of the author's earlier working notes,
formalized on the `main` branch, assume `a` in one of their `2`-adic classes and one of four
*squarefree-level certificates*: a modulus `M` dividing `s`, `r + 2s` (resp. `R`) or `r + s`
(resp. `R - s`) modulo which `r`, `-s` or `±s` is not a square, or a residue condition modulo `8`.
This file checks that these hypotheses imply those of the main theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`: the `2`-adic classes are
`QuadraticIterates.TwoAdicClass`, and the certificates, reduced to a prime or to `4` or `8` by
`ZMod.exists_of_not_isSquare_intCast`, give two of the three lists of criteria. It is a
consistency check of the new criteria against the earlier theorems, not part of the blueprint.

## Main statements

* `QuadraticIterates.criteria_of_neg_lt_of_certificate`,
  `QuadraticIterates.nonempty_mulEquiv_of_neg_lt_of_certificate`: Theorem R⁺.
* `QuadraticIterates.criteria_of_two_mul_le_of_certificate`,
  `QuadraticIterates.nonempty_mulEquiv_of_two_mul_le_of_certificate`: Theorem R⁻.
* `QuadraticIterates.twoAdicClass_one_of_emod`, `QuadraticIterates.twoAdicClass_neg_one_of_emod`:
  the `2`-adic classes of Theorems R⁺ and R⁻ as `QuadraticIterates.TwoAdicClass`.
-/

@[expose] public section

namespace QuadraticIterates

variable {r s : ℤ}

/-! ### Jacobi symbols -/

private lemma emod_eight_of_jacobiSym_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : jacobiSym 2 p = -1) :
    p % 8 = 3 ∨ p % 8 = 5 := by
  have ho := hp.odd_of_ne_two hp2
  rw [jacobiSym.at_two ho, ZMod.χ₈_nat_eq_if_mod_eight] at h
  split_ifs at h
  lia

private lemma emod_four_of_jacobiSym_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : jacobiSym (-1) p = -1) :
    p % 4 = 3 := by
  have ho := hp.odd_of_ne_two hp2
  rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_eq_if_mod_four] at h
  split_ifs at h
  lia

/-- A certificate `¬IsSquare (x : ZMod M)` with `M ∣ N ≠ 0` and `x` prime to `N` gives an odd prime
`p ∣ N` with `(x / p) = -1`, or `4 ∣ N` and `x ≡ 3 (mod 4)`, or `8 ∣ N` and `x ≢ 1 (mod 8)`. -/
private lemma exists_of_not_isSquare_of_dvd {x N : ℤ} {M : ℕ} (hN : N ≠ 0) (hx : IsCoprime x N)
    (hMN : (M : ℤ) ∣ N) (h : ¬IsSquare (x : ZMod M)) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (p : ℤ) ∣ N ∧ jacobiSym x p = -1) ∨ (4 ∣ N ∧ x % 4 = 3) ∨
      (8 ∣ N ∧ x % 8 ≠ 1) := by
  have hM : M ≠ 0 := by rintro rfl; simp_all
  have hlift {d : ℕ} (hd : d ∣ M) : (d : ℤ) ∣ N := (Int.natCast_dvd_natCast.mpr hd).trans hMN
  exact (ZMod.exists_of_not_isSquare_intCast hM (hx.of_isCoprime_of_dvd_right hMN) h).imp
    (fun ⟨p, hp, hp2, hpM, hj⟩ ↦ ⟨p, hp, hp2, hlift hpM, hj⟩)
    (.imp (.imp_left hlift) (.imp_left hlift))

/-- A prime `p ∤ c` dividing `r + c s`, with `r, s` coprime, does not divide `r`. -/
private lemma not_dvd_left_of_dvd_add_mul (hrs : IsCoprime r s) {p c : ℤ} (hp : Prime p)
    (hpc : ¬p ∣ c) (h : p ∣ r + c * s) :
    ¬p ∣ r := fun hpr ↦
  hp.not_isUnit <| hrs.isUnit_of_dvd' hpr <|
    (hp.dvd_or_dvd ((dvd_add_right hpr).mp h)).resolve_left hpc

/-! ### Theorem R⁺ -/

private lemma not_two_dvd_and (hrs : IsCoprime r s) : ¬((2 : ℤ) ∣ r ∧ 2 ∣ s) :=
  fun h ↦ Int.prime_two.not_isUnit (hrs.isUnit_of_dvd' h.1 h.2)

/-- The second certificate of Theorem R⁺ for `r = t²` gives (Z2): a prime `p ∣ r + 2s` with
`(-s / p) = -1` has `(2 / p) = -1`, as `-2s ≡ t² (mod p)`; `4 ∤ t² + 2s`. -/
private lemma negAllCriterion_of_eq_sq_of_cert (hs : 0 < s) (hrs : IsCoprime r s) {t : ℤ}
    (ht : r = t ^ 2) {M : ℕ} (hM : (M : ℤ) ∣ r + 2 * s) (h : ¬IsSquare (-(s : ZMod M))) :
    NegAllCriterion r s := by
  have h2 := not_two_dvd_and hrs
  rcases exists_of_not_isSquare_of_dvd (x := -s) (N := r + 2 * s) (by lia [ht ▸ sq_nonneg t])
    (hrs.symm.add_mul_right_right 2).neg_left hM (by simpa using h) with
    ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, -⟩ | ⟨h8, -⟩
  · have hpt : ¬(p : ℤ) ∣ t := fun hpt ↦ not_dvd_left_of_dvd_add_mul hrs
      (Nat.prime_iff_prime_int.mp hp) (Int.Prime.not_dvd_two hp hp2) hpN
      (ht ▸ dvd_pow hpt two_ne_zero)
    have h1 := (jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (by rw [← ht]; simpa using hpN) :
      2 * -s ≡ t ^ 2 [ZMOD p])).trans (jacobiSym.sq_one_of_not_dvd hp hpt)
    rw [jacobiSym.mul_left, hj] at h1
    exact .dvd_add_two_mul p hp (emod_eight_of_jacobiSym_two hp hp2 (by lia)) hpN
  · lia [Int.sq_emod_four t]
  · lia [Int.sq_emod_four t]

/-- The fourth certificate of Theorem R⁺ for `r = t²` gives (T3): a prime `p ∣ r + s` with
`(s / p) = -1` has `(-1 / p) = -1`, as `-s ≡ t² (mod p)`. -/
private lemma negTailCriterion_of_eq_sq_of_cert (hs : 0 < s) (hrs : IsCoprime r s) {t : ℤ}
    (ht : r = t ^ 2) (hns : ¬IsSquare (r + s)) {M : ℕ} (hM : (M : ℤ) ∣ r + s)
    (h : ¬IsSquare (s : ZMod M)) :
    NegTailCriterion r s := by
  have hr0 : 0 ≤ r := ht ▸ sq_nonneg t
  refine .not_isSquare_add hns (not_isSquare_of_neg (by lia)) ?_
  rcases exists_of_not_isSquare_of_dvd (x := s) (N := r + s) (by lia)
    hrs.symm.add_self_right hM h with
    ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, -⟩ | ⟨h8, -⟩
  · have hp' := Nat.prime_iff_prime_int.mp hp
    have hpt : ¬(p : ℤ) ∣ t := fun hpt ↦ not_dvd_left_of_dvd_add_mul hrs hp'
      (c := 1) hp'.not_dvd_one (by simpa using hpN) (ht ▸ dvd_pow hpt two_ne_zero)
    have h1 := (jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (by rw [← ht]; simpa using hpN) :
      -1 * s ≡ t ^ 2 [ZMOD p])).trans (jacobiSym.sq_one_of_not_dvd hp hpt)
    rw [jacobiSym.mul_left, hj] at h1
    exact .inr ⟨p, hp, emod_four_of_jacobiSym_neg_one hp hp2 (by lia), hpN⟩
  · exact .inl h4
  · exact .inl ((by norm_num : (4 : ℤ) ∣ 8).trans h8)

/-- For a positive square `r = t²`, the certificates of Theorem R⁺ give (Z2) or (T3). -/
private lemma negAllCriterion_or_negTailCriterion_of_eq_sq (hs : 0 < s) (hrs : IsCoprime r s)
    {t : ℤ} (ht : r = t ^ 2)
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + 2 * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + s) % 8 ≠ 1) ∨
          (¬IsSquare (r + s) ∧ ∃ M : ℕ, (M : ℤ) ∣ r + s ∧ ¬IsSquare (s : ZMod M))) :
    NegAllCriterion r s ∨ NegTailCriterion r s := by
  rcases hcert with ⟨M, -, h⟩ | ⟨M, hM, h⟩ | ⟨-, h, -⟩ | ⟨hns, M, hM, h⟩
  · exact absurd ⟨(t : ZMod M), by rw [ht]; push_cast; ring⟩ h
  · exact .inl (negAllCriterion_of_eq_sq_of_cert hs hrs ht hM h)
  · lia [Int.sq_emod_four t]
  · exact .inr (negTailCriterion_of_eq_sq_of_cert hs hrs ht hns hM h)

/-- The hypotheses of Theorem R⁺ (`a = r/s > -1`) give two of the three lists of criteria. -/
theorem criteria_of_neg_lt_of_certificate (hs : 0 < s) (hrs : IsCoprime r s) (hr : -s < r)
    (hsq : ¬IsSquare (-(r * s)))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + 2 * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + s) % 8 ≠ 1) ∨
          (¬IsSquare (r + s) ∧ ∃ M : ℕ, (M : ℤ) ∣ r + s ∧ ¬IsSquare (s : ZMod M))) :
    NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s := by
  rcases lt_trichotomy r 0 with h0 | rfl | h0
  · by_cases hr2 : IsSquare (-r)
    · exact .inr (.inr ⟨negFirstCriterion_of_not_isSquare_right hs.le
        fun h ↦ hsq (neg_mul r s ▸ hr2.mul h), .neg_one_lt hr h0⟩)
    · exact .inr (.inl ⟨.not_isSquare (not_isSquare_of_neg h0) hr2, .neg_one_lt hr h0⟩)
  · exact absurd ⟨0, by simp⟩ hsq
  · by_cases hr2 : IsSquare r
    · obtain ⟨t, ht⟩ := hr2
      exact (negAllCriterion_or_negTailCriterion_of_eq_sq hs hrs (t := t) (by rw [ht, sq])
        hcert).imp (⟨·, .pos h0⟩) fun h ↦ .inr ⟨.pos h0, h⟩
    · exact .inl ⟨.not_isSquare hr2 (not_isSquare_of_neg (neg_neg_of_pos h0)), .pos h0⟩

/-- The `2`-adic classes of Theorem R⁺ are `QuadraticIterates.TwoAdicClass r s 1`. -/
theorem twoAdicClass_one_of_emod
    (hc : (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3)) :
    TwoAdicClass r s 1 := twoAdicClass_one_iff.mpr (by lia)

/-- **Theorem R⁺** from the main theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`. -/
theorem nonempty_mulEquiv_of_neg_lt_of_certificate (hs : 0 < s) (hrs : IsCoprime r s)
    (hr : -s < r) (hsq : ¬IsSquare (-(r * s)))
    (hc : (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + 2 * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + s) % 8 ≠ 1) ∨
          (¬IsSquare (r + s) ∧ ∃ M : ℕ, (M : ℤ) ∣ r + s ∧ ¬IsSquare (s : ZMod M))) (n : ℕ) :
    Nonempty (GaloisGroup ((r : ℚ) / s) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs (.inr ⟨cubic_pos_of_neg_lt hs hr, rfl⟩)
    (twoAdicClass_one_of_emod hc) (criteria_of_neg_lt_of_certificate hs hrs hr hsq hcert) n

/-! ### Theorem R⁻ -/

private lemma not_dvd_neg_sq {p : ℕ} (hp : p.Prime) {u : ℤ} (hu : ¬(p : ℤ) ∣ u) :
    ¬(p : ℤ) ∣ -u ^ 2 := fun h ↦ hu ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (dvd_neg.mp h))

/-- For `R = t²` and an odd prime `p ∣ R` with `(-s / p) = -1`: (Z4) for `p ≡ 1` and (T2) for
`p ≡ 3 (mod 4)`, from `-R = p^{2j} (-u²)`. -/
private lemma negAllCriterion_or_negTailCriterion_of_dvd_sq {t : ℤ} (ht : t ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpt : (p : ℤ) ∣ t) (hj : jacobiSym (-s) p = -1) :
    NegAllCriterion (-t ^ 2) s ∨ NegTailCriterion (-t ^ 2) s := by
  obtain ⟨j, u, hj0, htu, hu⟩ := Int.exists_sq_eq_pow_mul_of_dvd hp ht hpt
  have hr : -t ^ 2 = p ^ (2 * j) * -u ^ 2 := by rw [htu]; ring
  have h : jacobiSym (-u ^ 2 * s) p = -1 := by
    rw [show -u ^ 2 * s = u ^ 2 * -s by ring, jacobiSym.mul_left,
      jacobiSym.sq_one_of_not_dvd hp hu, hj, one_mul]
  rcases (by lia [Nat.odd_iff.mp (hp.odd_of_ne_two hp2)] : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
  · exact .inl (.dvd_left p (2 * j) (-u ^ 2) hp h4 (by lia) hr (not_dvd_neg_sq hp hu) h)
  · exact .inr (.dvd_left p (2 * j) (-u ^ 2) hp h4 (by lia) hr (not_dvd_neg_sq hp hu) h)

/-- The `2`-part of a square: for `2 ∣ t ≠ 0`, `t² = 2^{2j} u²` with `j > 0`, `u` odd and
`u² ≡ 1 (mod 8)`. -/
private lemma exists_sq_eq_two_pow_mul {t : ℤ} (ht : t ≠ 0) (h2t : 2 ∣ t) :
    ∃ j : ℕ, ∃ u : ℤ, 0 < j ∧ t ^ 2 = 2 ^ (2 * j) * u ^ 2 ∧ Odd u ∧ u ^ 2 % 8 = 1 := by
  obtain ⟨j, u, hj, htu, hu⟩ := Int.exists_sq_eq_pow_mul_of_dvd Nat.prime_two ht (mod_cast h2t)
  have hu' : Odd u := Int.not_even_iff_odd.mp fun he ↦ hu (mod_cast he.two_dvd)
  exact ⟨j, u, hj, by simpa using htu, hu', Int.sq_emod_eight_eq_one_of_odd hu'⟩

/-- For `R = t²` with `t` even and `s` odd: (T2) at `2` if `-s ≡ 3 (mod 4)`, (Z4) at `2` if
`8 ∣ R` and `-s ≡ 5 (mod 8)`. -/
private lemma negAllCriterion_or_negTailCriterion_of_two_dvd_sq {t : ℤ} (ht : t ≠ 0) (h2t : 2 ∣ t)
    (h : -s % 4 = 3 ∨ 8 ∣ t ^ 2 ∧ -s % 8 = 5) :
    NegAllCriterion (-t ^ 2) s ∨ NegTailCriterion (-t ^ 2) s := by
  obtain ⟨j, u, hj, htu, -, hu8⟩ := exists_sq_eq_two_pow_mul ht h2t
  have hr : -t ^ 2 = 2 ^ (2 * j) * -u ^ 2 := by rw [htu]; ring
  have hu : u ^ 2 = 8 * (u ^ 2 / 8) + 1 := by lia
  have hus : -u ^ 2 * s = -(8 * (u ^ 2 / 8) * s) - s := by linear_combination (-s) * hu
  rcases h with h4 | ⟨h8, h5⟩
  · exact .inr (.dvd_left_two (2 * j) (-u ^ 2) (by lia) hr (by lia))
  · exact .inl (.dvd_left_two (2 * j) (-u ^ 2) (by lia) hr (.inr (by lia)))

variable {R : ℤ}

/-- (T3) for `a = -R/s ≤ -2` from the fourth certificate of Theorem R⁻ when `s ≡ t² (mod R - s)`,
as for `R = t²` or `s = t²`: then `(s / p) = 1` at the odd primes `p ∣ R - s`, so `(-s / p) = -1`
forces `p ≡ 3 (mod 4)`. -/
private lemma negTailCriterion_of_cert_sub (hs : 0 < s) (hRs : IsCoprime R s) (hR : 2 * s ≤ R)
    (t : ℤ) (ht : s ≡ t ^ 2 [ZMOD R - s]) (hns : ¬IsSquare (R - s)) {M : ℕ} (hM : (M : ℤ) ∣ R - s)
    (h : ¬IsSquare (-(s : ZMod M))) :
    NegTailCriterion (-R) s := by
  have he : -R + s = -(R - s) := by ring
  refine .not_isSquare_add (not_isSquare_of_neg (by lia)) (by rwa [he, neg_neg]) ?_
  rcases exists_of_not_isSquare_of_dvd (x := -s) (N := R - s) (by lia)
    (by simpa [sub_eq_add_neg] using (hRs.symm.add_mul_right_right (-1)).neg_left) hM
    (by simpa using h) with ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, -⟩ | ⟨h8, -⟩
  · have hps : ¬(p : ℤ) ∣ s := fun hps ↦
      Int.Prime.not_dvd_of_isCoprime hp hRs hps ((dvd_sub_left hps).mp hpN)
    have hpt : ¬(p : ℤ) ∣ t := fun hpt ↦
      hps ((ht.of_dvd hpN).dvd_iff.mpr (dvd_pow hpt two_ne_zero))
    refine .inr ⟨p, hp, emod_four_of_jacobiSym_neg_one hp hp2 ?_, he ▸ hpN.neg_right⟩
    rw [show -s = -1 * s by ring, jacobiSym.mul_left, jacobiSym.mod_left' (ht.of_dvd hpN),
      jacobiSym.sq_one_of_not_dvd hp hpt] at hj
    simpa using hj
  · exact .inl (he ▸ h4.neg_right)
  · exact .inl (he ▸ ((by norm_num : (4 : ℤ) ∣ 8).trans h8).neg_right)

/-- The second certificate of Theorem R⁻ for `R = t²` gives (Z4) or (T2), at an odd prime or
at `2`. -/
private lemma negAllCriterion_or_negTailCriterion_of_eq_sq_of_cert (hRs : IsCoprime R s) {t : ℤ}
    (ht : R = t ^ 2) (ht0 : t ≠ 0) {M : ℕ} (hM : (M : ℤ) ∣ R) (h : ¬IsSquare (-(s : ZMod M))) :
    NegAllCriterion (-R) s ∨ NegTailCriterion (-R) s := by
  have h2 := not_two_dvd_and hRs
  subst ht
  rcases exists_of_not_isSquare_of_dvd (x := -s) (N := t ^ 2) (by positivity) hRs.symm.neg_left hM
    (by simpa using h) with ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, hs4⟩ | ⟨h8, hs8⟩
  · exact negAllCriterion_or_negTailCriterion_of_dvd_sq ht0 hp hp2
      ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpN) hj
  · exact negAllCriterion_or_negTailCriterion_of_two_dvd_sq ht0
      (Int.prime_two.dvd_of_dvd_pow ((by norm_num : (2 : ℤ) ∣ 4).trans h4)) (.inl hs4)
  · have h2t := Int.prime_two.dvd_of_dvd_pow ((by norm_num : (2 : ℤ) ∣ 8).trans h8)
    exact negAllCriterion_or_negTailCriterion_of_two_dvd_sq ht0 h2t
      ((by lia : -s % 4 = 3 ∨ -s % 8 = 5).imp_right (⟨h8, ·⟩))

/-- For `R = t²`, the certificates of Theorem R⁻ give (Z4) or a `τ`. -/
private lemma negAllCriterion_or_negTailCriterion_of_eq_sq_of_two_mul_le (hs : 0 < s)
    (hRs : IsCoprime R s) (hR : 2 * s ≤ R) {t : ℤ} (ht : R = t ^ 2)
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧ ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) :
    NegAllCriterion (-R) s ∨ NegTailCriterion (-R) s := by
  have ht0 : t ≠ 0 := by rintro rfl; lia
  rcases hcert with ⟨M, -, h⟩ | ⟨M, hM, h⟩ | ⟨-, h, -⟩ | ⟨hns, M, hM, h⟩
  · exact absurd ⟨(t : ZMod M), by rw [ht]; push_cast; ring⟩ h
  · exact negAllCriterion_or_negTailCriterion_of_eq_sq_of_cert hRs ht ht0 hM h
  · lia [Int.sq_emod_four t]
  · exact .inr (negTailCriterion_of_cert_sub hs hRs hR t
      (by rw [← ht]; exact (Int.modEq_sub R s).symm) hns hM h)

/-- (O3) at `2` for `s = t²` with `t` even: `R ≡ 3 (mod 4)`, or `8 ∣ s` and `R ≡ 5 (mod 8)`. -/
private lemma negFirstCriterion_of_two_dvd_sq_right {t : ℤ} (ht : t ≠ 0) (h2t : 2 ∣ t)
    (h : R % 4 = 3 ∨ 8 ∣ t ^ 2 ∧ R % 8 = 5) :
    NegFirstCriterion (-R) (t ^ 2) := by
  obtain ⟨j, u, hj, htu, hu, hu8⟩ := exists_sq_eq_two_pow_mul ht h2t
  have hu2 : u ^ 2 = 8 * (u ^ 2 / 8) + 1 := by lia
  have hRu : -R * u ^ 2 = -(8 * (u ^ 2 / 8) * R) - R := by linear_combination (-R) * hu2
  refine .dvd_right_two (2 * j) (u ^ 2) (by simpa using htu) hu.pow (.inr ?_)
  rcases h with h | ⟨h8, h⟩
  · rcases (by lia : j = 1 ∨ 2 ≤ j) with rfl | hj2
    exacts [.inl ⟨rfl, by lia⟩, .inr ⟨even_two_mul j, by lia, by lia⟩]
  · exact .inr ⟨even_two_mul j, by lia, by lia⟩

/-- The first certificate of Theorem R⁻ for `s = t²` gives (O3): a prime `p ∣ t` with
`(R / p) = -1`, or `4 ∣ s` with `R ≡ 3 (mod 4)`, or `8 ∣ s` with `R ≡ 5 (mod 8)`. -/
private lemma negFirstCriterion_of_eq_sq_right_of_cert {t : ℤ} (hRs : IsCoprime R (t ^ 2))
    (ht0 : t ≠ 0) {M : ℕ} (hM : (M : ℤ) ∣ t ^ 2) (h : ¬IsSquare (R : ZMod M)) :
    NegFirstCriterion (-R) (t ^ 2) := by
  have h2 := not_two_dvd_and hRs
  rcases exists_of_not_isSquare_of_dvd (x := R) (N := t ^ 2) (by positivity) hRs hM h
    with ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, hR4⟩ | ⟨h8, hR8⟩
  · have hp' := Nat.prime_iff_prime_int.mp hp
    obtain ⟨j, u, hj0, htu, hu⟩ := Int.exists_sq_eq_pow_mul_of_dvd hp ht0 (hp'.dvd_of_dvd_pow hpN)
    refine .dvd_right p (2 * j) (u ^ 2) hp hp2 (by lia) htu
      (fun h ↦ hu (hp'.dvd_of_dvd_pow h)) (.inr ?_)
    rw [show -(-R * u ^ 2) = u ^ 2 * R by ring, jacobiSym.mul_left,
      jacobiSym.sq_one_of_not_dvd hp hu, hj, one_mul]
  · exact negFirstCriterion_of_two_dvd_sq_right ht0
      (Int.prime_two.dvd_of_dvd_pow ((by norm_num : (2 : ℤ) ∣ 4).trans h4)) (.inl hR4)
  · have h2t := Int.prime_two.dvd_of_dvd_pow ((by norm_num : (2 : ℤ) ∣ 8).trans h8)
    exact negFirstCriterion_of_two_dvd_sq_right ht0 h2t
      ((by lia : R % 4 = 3 ∨ R % 8 = 5).imp_right (⟨h8, ·⟩))

/-- The second certificate of Theorem R⁻ for `s = t²` gives (O4) or (T2): a prime `p ∣ R` with
`(-s / p) = -1` is `≡ 3 (mod 4)`, as `s` is a square. -/
private lemma negFirstCriterion_or_negTailCriterion_of_eq_sq_right_of_cert (hRs : IsCoprime R s)
    (hR0 : R ≠ 0) {t : ℤ} (ht : s = t ^ 2) {M : ℕ} (hM : (M : ℤ) ∣ R)
    (h : ¬IsSquare (-(s : ZMod M))) :
    NegFirstCriterion (-R) s ∨ NegTailCriterion (-R) s := by
  have h2 := not_two_dvd_and hRs
  rcases exists_of_not_isSquare_of_dvd (x := -s) (N := R) hR0 hRs.symm.neg_left hM
    (by simpa using h) with ⟨p, hp, hp2, hpN, hj⟩ | ⟨h4, hs4⟩ | ⟨h8, -⟩
  · have hps : ¬(p : ℤ) ∣ s := Int.Prime.not_dvd_of_isCoprime hp hRs.symm hpN
    have hpt : ¬(p : ℤ) ∣ t := fun hpt ↦ hps (ht ▸ dvd_pow hpt two_ne_zero)
    rw [ht, show -t ^ 2 = -1 * t ^ 2 by ring, jacobiSym.mul_left,
      jacobiSym.sq_one_of_not_dvd hp hpt, mul_one] at hj
    exact negFirstCriterion_or_negTailCriterion_of_prime_dvd (neg_ne_zero.mpr hR0) hp
      (emod_four_of_jacobiSym_neg_one hp hp2 hj) hpN.neg_right hps
  · exact negFirstCriterion_or_negTailCriterion_of_four_dvd (neg_ne_zero.mpr hR0) h4.neg_right
      (Int.odd_iff.mpr (by lia))
  · exact negFirstCriterion_or_negTailCriterion_of_four_dvd (neg_ne_zero.mpr hR0)
      ((by norm_num : (4 : ℤ) ∣ 8).trans h8).neg_right (Int.odd_iff.mpr (by lia))

/-- For `s = t²`, the certificates of Theorem R⁻ give `φ₁` ((O3), (O4)) or a `τ`. -/
private lemma negFirstCriterion_or_negTailCriterion_of_eq_sq_right (hs : 0 < s)
    (hRs : IsCoprime R s) (hR : 2 * s ≤ R) {t : ℤ} (ht : s = t ^ 2)
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧ ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) :
    NegFirstCriterion (-R) s ∨ NegTailCriterion (-R) s := by
  have ht0 : t ≠ 0 := by rintro rfl; lia
  rcases hcert with ⟨M, hM, h⟩ | ⟨M, hM, h⟩ | ⟨hs2, hR4, -⟩ | ⟨hns, M, hM, h⟩
  · rw [ht] at hM hRs ⊢
    exact .inl (negFirstCriterion_of_eq_sq_right_of_cert hRs ht0 hM h)
  · exact negFirstCriterion_or_negTailCriterion_of_eq_sq_right_of_cert hRs (by lia) ht hM h
  · obtain ⟨p, hp, hp4, hpR⟩ := Int.exists_prime_dvd_of_emod_four_eq_three (by lia) hR4
    exact negFirstCriterion_or_negTailCriterion_of_prime_dvd (by lia) hp hp4 hpR.neg_right
      (Int.Prime.not_dvd_of_isCoprime hp hRs.symm hpR)
  · exact .inr (negTailCriterion_of_cert_sub hs hRs hR t (ht ▸ .refl _) hns hM h)

/-- The hypotheses of Theorem R⁻ (`a = -R/s ≤ -2`) give two of the three lists of criteria. -/
theorem criteria_of_two_mul_le_of_certificate (hs : 0 < s) (hRs : IsCoprime R s)
    (hR : 2 * s ≤ R) (hsq : ¬IsSquare (R * s))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧ ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) :
    NegAllCriterion (-R) s ∧ NegFirstCriterion (-R) s ∨
      NegAllCriterion (-R) s ∧ NegTailCriterion (-R) s ∨
        NegFirstCriterion (-R) s ∧ NegTailCriterion (-R) s := by
  by_cases hRsq : IsSquare R
  · have h₁ : NegFirstCriterion (-R) s :=
      negFirstCriterion_of_not_isSquare_right hs.le fun h ↦ hsq (hRsq.mul h)
    obtain ⟨t, ht⟩ := hRsq
    exact (negAllCriterion_or_negTailCriterion_of_eq_sq_of_two_mul_le hs hRs hR (t := t)
      (by rw [ht, sq]) hcert).imp (⟨·, h₁⟩) fun h ↦ .inr ⟨h₁, h⟩
  · have h₀ : NegAllCriterion (-R) s :=
      .not_isSquare (not_isSquare_of_neg (by lia)) (by rwa [neg_neg])
    by_cases hssq : IsSquare s
    · obtain ⟨t, ht⟩ := hssq
      exact (negFirstCriterion_or_negTailCriterion_of_eq_sq_right hs hRs hR (t := t)
        (by rw [ht, sq]) hcert).imp (⟨h₀, ·⟩) fun h ↦ .inl ⟨h₀, h⟩
    · exact .inl ⟨h₀, negFirstCriterion_of_not_isSquare_right hs.le hssq⟩

/-- The `2`-adic classes of Theorem R⁻ are `QuadraticIterates.TwoAdicClass (-R) s (-1)`. -/
theorem twoAdicClass_neg_one_of_emod
    (hc : (s % 2 = 1 ∧ (R % 4 = 1 ∨ (R - s) % 4 = 3)) ∨ (s % 2 = 0 ∧ R % 4 = 3)) :
    TwoAdicClass (-R) s (-1) := twoAdicClass_neg_one_iff.mpr (by lia)

/-- **Theorem R⁻** from the main theorem
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`. -/
theorem nonempty_mulEquiv_of_two_mul_le_of_certificate (hs : 0 < s) (hRs : IsCoprime R s)
    (hR : 2 * s ≤ R) (hsq : ¬IsSquare (R * s))
    (hc : (s % 2 = 1 ∧ (R % 4 = 1 ∨ (R - s) % 4 = 3)) ∨ (s % 2 = 0 ∧ R % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧ ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) (n : ℕ) :
    Nonempty (GaloisGroup (-R / s : ℚ) n ≃* WreathPower n) := by
  have := nonempty_mulEquiv_of_twoAdicClass_of_criteria hRs.neg_left hs (.inl ⟨by lia, rfl⟩)
    (twoAdicClass_neg_one_of_emod hc) (criteria_of_two_mul_le_of_certificate hs hRs hR hsq hcert) n
  rwa [Int.cast_neg] at this

end QuadraticIterates
