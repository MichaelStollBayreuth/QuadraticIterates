module

public import QuadraticIterates

/-!
# Comparator solutions

Proofs of the challenge statements of `Challenge.lean`, discharged by the library theorems
`QuadraticIterates.section3_main` (`QuadraticIterates.ArchMath1992.Main`),
`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul`, `QuadraticIterates.li2021_theorem_3_9`
(`QuadraticIterates.Li.ArchMath2021`) and `QuadraticIterates.li2020_theorem_3_5`
(`QuadraticIterates.Li.ArchMath2020`). Importing the library brings in the definitions
`iteratedPoly`, `GaloisGroup`, `WreathPower` that the statements refer to; Comparator checks that
these agree with the copies reproduced in `Challenge.lean`.
-/

@[expose] public section

open QuadraticIterates

theorem challenge_section3_main_pos_emod_four_eq_one (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 1) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  section3_main (.inl ⟨ha, ha4⟩)

theorem challenge_section3_main_pos_emod_four_eq_two (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 2) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  section3_main (.inr (.inl ⟨ha, ha4⟩))

theorem challenge_section3_main_neg_emod_four_eq_zero (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  section3_main (.inr (.inr ⟨ha, ha4, hsq⟩))

theorem challenge_nonempty_mulEquiv_of_eq_neg_mul (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-((4 * k + 2) * (4 * k + 3))) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_eq_neg_mul rfl

theorem challenge_li2021_theorem_3_9 (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (-((4 * k + 1) * (4 * k + 2) + 1)) n ≃* WreathPower n) :=
  li2021_theorem_3_9 rfl

theorem challenge_li2020_theorem_3_5 (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  li2020_theorem_3_5 ha ha4 hsq
