import QuadraticIterates

/-!
# Comparator solution (Section 3 main result)

Proof of `challenge_section3_main` from `Challenge.lean`, discharged by the library theorem
`QuadraticIterates.section3_main` in `QuadraticIterates.ArchMath1992.Main`. Importing the library
brings in the definitions `iteratedPoly`, `GaloisGroup`, `WreathPower` that the statement refers
to; Comparator checks that these agree with the copies reproduced in `Challenge.lean`.
-/

open QuadraticIterates in
theorem challenge_section3_main (a : ℤ)
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  section3_main a hcase
