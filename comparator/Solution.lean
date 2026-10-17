module

public import QuadraticIterates

/-!
# Comparator solutions

Proofs of the challenge statements of `Challenge.lean`, discharged by the library theorems
`QuadraticIterates.section3_main`, `QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul`,
`QuadraticIterates.li2021_theorem_3_9`, `QuadraticIterates.li2020_theorem_3_5`
(`QuadraticIterates.Main.Integers`) and the main theorem for rational parameters
`QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria`
(`QuadraticIterates.Main.Theorem`) and its corollaries
`QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`
(`QuadraticIterates.Main.LevelTwo`) and
`QuadraticIterates.nonempty_mulEquiv_of_lt_neg_one_of_criteria` and
`QuadraticIterates.nonempty_mulEquiv_of_lt_neg_one_of_emod` (`QuadraticIterates.Main.Interval`),
whose 2-independence of `c₁, c₂` the challenges spell out by
`QuadraticIterates.twoIndependent_fin_two_iff`. Importing the library brings in the definitions
`iteratedPoly`, `GaloisGroup`, `WreathPower`, `NegAllCriterion`, `NegFirstCriterion`,
`NegTailCriterion`, `TwoAdicClass`, `NegFirstCriterion'` and `NegTailCriterion'` that the
statements refer to; Comparator checks that these
agree with the copies reproduced in `Challenge.lean`.
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

theorem challenge_nonempty_mulEquiv_of_twoAdicClass_of_criteria (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (ε : ℤ)
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε)
    (h : NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_twoAdicClass_of_criteria hrs hs hε hc h n

theorem challenge_forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass (r s : ℤ)
    (hrs : IsCoprime r s) (hs : 0 < s) (ε : ℤ)
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n)) ↔
      ¬IsSquare (-(r / s : ℚ)) ∧ ¬IsSquare ((r / s : ℚ) ^ 2 + r / s) ∧
        ¬IsSquare (-(r / s : ℚ) * ((r / s : ℚ) ^ 2 + r / s)) := by
  rw [forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass hrs hs hε hc,
    twoIndependent_fin_two_iff]
  simp [cSeq_two]

theorem challenge_nonempty_mulEquiv_of_lt_neg_one_of_criteria (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (hr : r < -s) (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (hc : TwoAdicClass r s 1)
    (h2 : ¬IsSquare (-(r / s : ℚ)) ∧ ¬IsSquare ((r / s : ℚ) ^ 2 + r / s) ∧
      ¬IsSquare (-(r / s : ℚ) * ((r / s : ℚ) ^ 2 + r / s)))
    (h : NegAllCriterion r s ∧ NegFirstCriterion' r s ∨ NegAllCriterion r s ∧
      NegTailCriterion' r s ∨ NegFirstCriterion' r s ∧ NegTailCriterion' r s) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_lt_neg_one_of_criteria hrs hs hr hα hc
    (twoIndependent_fin_two_iff.mpr (by simpa [cSeq_two] using h2)) h n

theorem challenge_nonempty_mulEquiv_of_lt_neg_one_of_emod (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (hr : r < -s) (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (h : r % 4 = 1 ∧ s % 2 = 1 ∨ r % 4 = 3 ∧ s % 4 = 2 ∨
      r % 4 = 2 ∧ s % 4 = 1 ∧ (r % 8 = 2 ∨ s % 8 = 5) ∨
      r % 4 = 0 ∧ s % 4 = 3 ∧ ((∀ j : ℕ, ∀ m : ℤ, -r = 4 ^ j * m → m % 8 ≠ 1) ∨
        (r + 2 * s) % 16 = 6 ∨ (r + 2 * s) % 16 = 10) ∨
      r % 8 = 3 ∧ s % 4 = 0 ∧ s % 32 ≠ 4) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_lt_neg_one_of_emod hrs hs hr hα h n
