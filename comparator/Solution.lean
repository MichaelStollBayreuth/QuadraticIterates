module

public import QuadraticIterates

/-!
# Comparator solutions

Proofs of the challenge statements of `Challenge.lean`, discharged by the library theorems
`QuadraticIterates.section3_main` (`QuadraticIterates.ArchMath1992.Main`),
`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul`, `QuadraticIterates.li2021_theorem_3_9`
(`QuadraticIterates.Li.ArchMath2021`), `QuadraticIterates.li2020_theorem_3_5`
(`QuadraticIterates.Li.ArchMath2020`) and the rational-parameter theorems
`QuadraticIterates.nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCertificate` and
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate`
(`QuadraticIterates.Rational.Main`), whose class and certificate hypotheses are the spelled-out
disjunctions through `QuadraticIterates.twoAdicClass_iff` and
`QuadraticIterates.squarefreeCertificate_iff`. Importing the library brings in the definitions
`iteratedPoly`, `GaloisGroup`, `WreathPower` that the statements refer to; Comparator checks that
these agree with the copies reproduced in `Challenge.lean`.
-/

@[expose] public section

open QuadraticIterates

theorem challenge_section3_main_pos_emod_four_eq_one (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 1) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  section3_main (.inl ⟨ha, ha4⟩)

theorem challenge_section3_main_pos_emod_four_eq_two (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 2) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  section3_main (.inr (.inl ⟨ha, ha4⟩))

theorem challenge_section3_main_neg_emod_four_eq_zero (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) : ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  section3_main (.inr (.inr ⟨ha, ha4, hsq⟩))

theorem challenge_nonempty_mulEquiv_of_eq_neg_mul (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup ((-((4 * k + 2) * (4 * k + 3)) : ℤ) : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_eq_neg_mul rfl

theorem challenge_li2021_theorem_3_9 (k : ℕ) :
    ∀ n ≥ 1,
      Nonempty (GaloisGroup ((-((4 * k + 1) * (4 * k + 2) + 1) : ℤ) : ℚ) n ≃* WreathPower n) :=
  li2021_theorem_3_9 rfl

theorem challenge_li2020_theorem_3_5 (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  li2020_theorem_3_5 ha ha4 hsq

theorem challenge_nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCertificate (r s : ℤ)
    (hs : 0 < s) (hrs : IsCoprime r s) (hr : -s < r) (hsq : ¬IsSquare (-(r * s)))
    (hc : (s % 2 = 1 ∧ (r % 4 = 1 ∨ (r + s) % 4 = 3)) ∨ (s % 2 = 0 ∧ r % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (r : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ r + 2 * s ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ r % 4 = 3 ∧ (r + s) % 8 ≠ 1) ∨
          (¬IsSquare (r + s) ∧
            ∃ M : ℕ, (M : ℤ) ∣ r + s ∧ ¬IsSquare (s : ZMod M))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) := fun n _ ↦
  nonempty_mulEquiv_of_neg_lt_of_twoAdicClass_of_squarefreeCertificate hs hrs hr
    (twoAdicClass_iff.mpr (by simpa using hc)) hsq
    (squarefreeCertificate_iff.mpr (by simpa using hcert)) n

theorem challenge_nonempty_mulEquiv_of_two_mul_le_neg_of_twoAdicClass_of_squarefreeCertificate
    (R s : ℤ) (hs : 0 < s) (hRs : IsCoprime R s) (hR : 2 * s ≤ R) (hsq : ¬IsSquare (R * s))
    (hc : (s % 2 = 1 ∧ (R % 4 = 1 ∨ (R - s) % 4 = 3)) ∨ (s % 2 = 0 ∧ R % 4 = 3))
    (hcert : (∃ M : ℕ, (M : ℤ) ∣ s ∧ ¬IsSquare (R : ZMod M)) ∨
      (∃ M : ℕ, (M : ℤ) ∣ R ∧ ¬IsSquare (-(s : ZMod M))) ∨
        (s % 2 = 0 ∧ R % 4 = 3 ∧ (R - s) % 8 ≠ 1) ∨
          (¬IsSquare (R - s) ∧
            ∃ M : ℕ, (M : ℤ) ∣ R - s ∧ ¬IsSquare (-(s : ZMod M)))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-R / s : ℚ) n ≃* WreathPower n) := fun n _ ↦
  (show ((-1 : ℤ) : ℚ) * R / s = (-R / s : ℚ) by simp) ▸
    nonempty_mulEquiv_of_twoAdicClass_of_squarefreeCertificate hs hRs neg_one_sq
      (wSeq_pos_of_two_mul_le hs hR) (twoAdicClass_iff.mpr (by simpa [sub_eq_add_neg] using hc))
      (by simpa using hsq) (squarefreeCertificate_iff.mpr (by simpa [sub_eq_add_neg] using hcert)) n
