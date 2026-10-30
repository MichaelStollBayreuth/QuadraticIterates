module

public import QuadraticIterates

/-!
# Comparator solutions along the original papers

Proofs of the six challenge statements of `Challenge.lean` for integer parameters by the theorems
of Part II of the blueprint, which follow the proofs of the original papers: the main result of
Section 3 of M. Stoll, Arch. Math. 59 (1992) (`QuadraticIterates.section3_main`), Theorem 3.5 of
H.-C. Li, Arch. Math. 114 (2020) (`QuadraticIterates.li2020_theorem_3_5`), and Theorem 3.9 of
H.-C. Li, Arch. Math. 117 (2021) (`QuadraticIterates.li2021_theorem_3_9`) together with the family
`a = -(4k+2)(4k+3)` that contains his Theorem 3.3
(`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul`).
These state `Ω_n ≅ [C₂]ⁿ` for `n ≥ 1`, as the papers do; this file supplies the case `n = 0`,
where both groups are trivial, and the parametrizations `ℓ = 4k + 2` and `ℓ = 4k + 1` of the two
families. The configuration is `challenges-1992.json`.
-/

@[expose] public section

open QuadraticIterates

/-- `Ω_n ≅ [C₂]ⁿ` for all `n` once it holds for `n ≥ 1`: for `n = 0` both groups are trivial. -/
private lemma nonempty_mulEquiv_of_forall_one_le {a : ℚ}
    (h : ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n)) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) :=
  n.eq_zero_or_pos.elim (fun hn ↦ hn ▸ (nonempty_mulEquiv_iff_finrank_eq a 0).mpr (by simp)) (h n)

theorem challenge_nonempty_mulEquiv_of_pos_of_emod_four_eq_one (a : ℤ) (ha : 0 < a)
    (ha4 : a % 4 = 1) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_forall_one_le (section3_main (.inl ⟨ha, ha4⟩)) n

theorem challenge_nonempty_mulEquiv_of_pos_of_emod_four_eq_two (a : ℤ) (ha : 0 < a)
    (ha4 : a % 4 = 2) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_forall_one_le (section3_main (.inr (.inl ⟨ha, ha4⟩))) n

theorem challenge_nonempty_mulEquiv_of_neg_of_emod_four_eq_zero (a : ℤ) (ha : a < 0)
    (ha4 : a % 4 = 0) (hsq : ¬IsSquare (-a)) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  nonempty_mulEquiv_of_forall_one_le (section3_main (.inr (.inr ⟨ha, ha4, hsq⟩))) n

theorem challenge_nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two (ℓ : ℤ) (hℓ : 0 < ℓ)
    (hℓ4 : ℓ % 4 = 2) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) * (ℓ + 1))) n ≃* WreathPower n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = 4 * k + 2 := ⟨(ℓ / 4).toNat, by lia⟩
  have hq : ((-((4 * k + 2) * (4 * k + 3)) : ℤ) : ℚ) =
      -(((4 * k + 2 : ℤ) : ℚ) * ((4 * k + 2 : ℤ) + 1)) := by
    push_cast; ring
  exact hq ▸ nonempty_mulEquiv_of_forall_one_le (nonempty_mulEquiv_of_eq_neg_mul (k := k) rfl) n

theorem challenge_nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one (ℓ : ℤ)
    (hℓ : 0 < ℓ) (hℓ4 : ℓ % 4 = 1) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) ^ 2 + ℓ + 1)) n ≃* WreathPower n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = 4 * k + 1 := ⟨(ℓ / 4).toNat, by lia⟩
  have hq : ((-((4 * k + 1) * (4 * k + 2) + 1) : ℤ) : ℚ) =
      -(((4 * k + 1 : ℤ) : ℚ) ^ 2 + (4 * k + 1 : ℤ) + 1) := by
    push_cast; ring
  exact hq ▸ nonempty_mulEquiv_of_forall_one_le (li2021_theorem_3_9 (k := k) rfl) n

theorem challenge_forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three (a : ℤ) (ha : a < 0)
    (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) :
    (∀ n, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  ⟨fun h ↦ (li2020_theorem_3_5 ha ha4 hsq).mp fun n _ ↦ h n,
    fun h ↦ nonempty_mulEquiv_of_forall_one_le ((li2020_theorem_3_5 ha ha4 hsq).mpr h)⟩
