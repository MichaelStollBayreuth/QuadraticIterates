/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.ArchMath1992.Iterates

import QuadraticIterates.ArchMath1992.DegreeCriterion
import QuadraticIterates.ArchMath1992.Irreducibility
import QuadraticIterates.Mathlib.Algebra.Squares
import QuadraticIterates.Mathlib.Data.Int.Order.Units
import QuadraticIterates.Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The main theorems

The integer factors `b_n` of the `c`-sequence (Lemma 1.1 b), the two parts of the Section 1
theorem, the `γ`- and `β`-sequences of the rescaled polynomial `normPoly a`, and the Section 3
theorem of the paper.

## Main statements

* `section1_tfae`: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff `b_1, …, b_n` are
  2-independent (`section1_a_iff_b`, `section1_b_iff_c`).
* `section1_squarefree`: if none of `|b_2|, …, |b_n|` is a square, then `Ω_n ≅ [C₂]ⁿ`.
* `section3_main`: if `a > 0` and `a ≡ 1, 2 mod 4`, or `a < 0`, `a ≡ 0 mod 4` and `-a` is not a
  square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. The proof rescales `X² + a` to
  `normPoly a = |a| X² + sgn a`, whose `γ`-sequence is `|c_n| / |a|`
  (`abs_cSeq_eq_gammaSeq_mul_abs`) and whose `β`-sequence is `|b_n|` (`abs_bSeq_eq_betaSeq`), and
  applies Lemma 2.2 (`not_isSquare_abs_bSeq`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

section

variable {a : ℤ}

/-! ### Lemma 1.1 b): the integer factors `b_n` -/

/-- The constant-valuation shape for `c`: the specialization of `factorization_gammaSeq_shape`
to `X² + a`, `ε = -1`, in the form consumed by `moebiusFactorR_isRelPrime`. -/
lemma factorization_cSeq_shape (ha : ¬IsSquare (-a : ℚ)) :
    ∀ q : ℤ, Prime q → normalize q = q →
      ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1, factorization (cSeq a k) q = if m ∣ k then E else 0 :=
  fun _ ↦ factorization_gammaSeq_shape (evenPoly_X_sq_add_C a) neg_one_sq (cSeq_ne_zero ha)

/-- Lemma 1.1 b): the Möbius product `∏_{ed = n} c_d^{μ(e)}` is the integer `b_n`, since `c` is a
strong divisibility sequence. -/
lemma intCast_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    (bSeq a n : ℚ) = moebiusFactorK (cSeq a) n :=
  algebraMap_moebiusFactorR (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

lemma bSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : bSeq a n ≠ 0 :=
  moebiusFactorR_ne_zero (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

/-- Möbius inversion for the integer factors (Lemma 1.1 b): `c_n = ∏_{d ∣ n} b_d`. -/
lemma cSeq_eq_prod_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    cSeq a n = ∏ d ∈ n.divisors, bSeq a d :=
  prod_moebiusFactorR (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

/-- The integer factors `b_n` are pairwise coprime (Lemma 1.1 b): the valuation of `b_n` at
each prime is supported on a single index, so no prime divides two distinct factors. -/
lemma isCoprime_bSeq (ha : ¬IsSquare (-a : ℚ)) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) : IsCoprime (bSeq a m) (bSeq a n) :=
  (moebiusFactorR_isRelPrime (cSeq_ne_zero ha) (cSeq_associated_gcd a)
    (factorization_cSeq_shape ha) hm hn hmn).isCoprime

/-! ### Theorem (Section 1) -/

/-- Section 1, `(a) ↔ (b)`: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent. By induction on
`n`: `Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}`
(`nonempty_mulEquiv_succ_iff`, Lemma 1.4), the degree condition says that `c_{n+1}` is not a
square in `K_n` (`degree_criterion`, Lemma 1.6), and given `Ω_n ≅ [C₂]ⁿ` this means that
`c_1, …, c_{n+1}` are 2-independent (`kummer_extension_criterion`, Lemma 1.5). -/
theorem section1_a_iff_b (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) := by
  induction n with
  | zero =>
    exact ⟨fun _ S ⟨i, _⟩ ↦ i.elim0, fun _ ↦ (nonempty_mulEquiv_iff_finrank_eq a 0).mpr (by simp)⟩
  | succ n ih =>
    rw [← Fin.snoc_init_self (fun i : Fin (n + 1) ↦ (cSeq a ((i : ℕ) + 1) : ℚ)),
      nonempty_mulEquiv_succ_iff a n]
    refine ⟨fun ⟨hiso, hrel⟩ ↦ ?_, fun h ↦ ?_⟩
    · exact (kummer_extension_criterion hiso (ih.mp hiso)).mp ((degree_criterion ha n).mp hrel)
    · have hiso : Nonempty (GaloisGroup a n ≃* WreathPower n) := ih.mpr h.of_snoc
      exact ⟨hiso, (degree_criterion ha n).mpr
        ((kummer_extension_criterion hiso h.of_snoc).mpr h)⟩

/-- In `ℚˣ/(ℚˣ)²`, the class of `c_m` is the sum of the classes of the `b_d` over `d ∣ m`. -/
lemma sqClass_cSeq_eq_sum_divisors (ha : ¬IsSquare (-a : ℚ)) {m : ℕ} (hm : 1 ≤ m) :
    sqClass (cSeq a m : ℚ) = ∑ d ∈ m.divisors, sqClass (bSeq a d : ℚ) := by
  rw [cSeq_eq_prod_bSeq ha hm, Int.cast_prod]
  exact sqClass_prod fun d hd ↦ mod_cast bSeq_ne_zero ha (Nat.pos_of_mem_divisors hd)

/-- In `ℚˣ/(ℚˣ)²`, the class of `b_m` is the Möbius-weighted sum of the classes of the `c_d`. -/
lemma sqClass_bSeq_eq_sum_divisorsAntidiagonal (ha : ¬IsSquare (-a : ℚ)) {m : ℕ} (hm : 1 ≤ m) :
    sqClass (bSeq a m : ℚ) = ∑ x ∈ m.divisorsAntidiagonal, (μ x.1) • sqClass (cSeq a x.2 : ℚ) := by
  simp only [intCast_bSeq ha hm, moebiusFactorK_eq_prod, eq_intCast]
  exact sqClass_prod_zpow _ fun x hx ↦
    mod_cast ne_zero_of_mem_divisorsAntidiagonal (cSeq_ne_zero ha) hx

/-- `F d` is a value of `fun i : Fin n ↦ F (i + 1)` whenever `d ∣ i + 1` for some `i : Fin n`. -/
private lemma mem_range_of_dvd {α : Type*} (F : ℕ → α) {n : ℕ} {i : Fin n} {d : ℕ}
    (hd : d ∣ (i : ℕ) + 1) : F d ∈ Set.range fun j : Fin n ↦ F ((j : ℕ) + 1) :=
  have h1 := Nat.pos_of_dvd_of_pos hd i.1.succ_pos
  ⟨⟨d - 1, by have := Nat.le_of_dvd i.1.succ_pos hd; lia⟩, by simp [Nat.sub_add_cancel h1]⟩

/-- Section 1, `(b) ↔ (c)`: `c_1, …, c_n` are 2-independent iff `b_1, …, b_n` are 2-independent,
since their classes in `ℚˣ/(ℚˣ)²` span the same `𝔽₂`-subspace (Möbius inversion in both
directions). -/
theorem section1_b_iff_c (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) ↔
      TwoIndependent (fun i : Fin n ↦ (bSeq a ((i : ℕ) + 1) : ℚ)) := by
  simp only [twoIndependent_iff_linearIndependent]
  refine linearIndependent_iff_of_span_range_eq (le_antisymm ?_ ?_) <;>
    rw [Submodule.span_le, Set.range_subset_iff] <;> intro i
  · rw [SetLike.mem_coe, sqClass_cSeq_eq_sum_divisors ha i.1.succ_pos]
    exact Submodule.sum_mem _ fun d hd ↦ Submodule.subset_span
      (mem_range_of_dvd (fun k ↦ sqClass (bSeq a k : ℚ)) (Nat.dvd_of_mem_divisors hd))
  · rw [SetLike.mem_coe, sqClass_bSeq_eq_sum_divisorsAntidiagonal ha i.1.succ_pos]
    exact Submodule.sum_mem _ fun x hx ↦ zsmul_mem (Submodule.subset_span
      (mem_range_of_dvd (fun k ↦ sqClass (cSeq a k : ℚ))
        (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)))) _

/-- Theorem (Section 1), part 1: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff `b_1, …, b_n`
are 2-independent. -/
theorem section1_tfae (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    [Nonempty (GaloisGroup a n ≃* WreathPower n),
     TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)),
     TwoIndependent (fun i : Fin n ↦ (bSeq a ((i : ℕ) + 1) : ℚ))].TFAE := by
  tfae_have 1 ↔ 2 := section1_a_iff_b ha n
  tfae_have 2 ↔ 3 := section1_b_iff_c ha n
  tfae_finish

/-- Theorem (Section 1), part 2: if none of `|b_2|, …, |b_n|` is a square, then
`Ω_n ≅ [C₂]ⁿ`. By pairwise coprimality, the `b_k` are 2-independent as soon as no `b_k` and at
most one `-b_k` is a square; `-b_1 = a` is the only candidate, since `b_1 = -a` is not a square. -/
theorem section1_squarefree (ha : ¬IsSquare (-a : ℚ)) (n : ℕ)
    (h : ∀ k ≥ 2, k ≤ n → ¬IsSquare |bSeq a k|) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  have hzero (i : Fin n) (hi : IsSquare (-bSeq a ((i : ℕ) + 1))) : (i : ℕ) = 0 :=
    Nat.eq_zero_of_not_pos fun hi0 ↦ h _ (by lia) i.2 (isSquare_abs_iff.mpr (.inr hi))
  refine ((section1_tfae ha n).out 2 0).mp ((twoIndependent_intCast_iff _).mpr
    ((twoIndependent_iff_of_pairwise_isCoprime fun i j hij ↦
      isCoprime_bSeq ha i.1.succ_pos j.1.succ_pos (by simpa [Fin.ext_iff] using hij)).mpr
        ⟨fun i ↦ ?_, fun i hi j hj ↦ Fin.ext ((hzero i hi).trans (hzero j hj).symm)⟩))
  rcases eq_or_ne (i : ℕ) 0 with hi | hi
  · rwa [hi, zero_add, bSeq_one, ← Rat.isSquare_intCast_iff, Int.cast_neg]
  · exact fun hsq ↦ h _ (by lia) i.2 (isSquare_abs_iff.mpr (.inl hsq))

/-! ### The `γ`-sequence of the rescaled polynomial -/

/-- `γ_1 = sgn(a) · g(0) = sgn(a)² = 1` for the rescaled polynomial `g = normPoly a`. -/
lemma gammaSeq_normPoly_one (ha0 : a ≠ 0) : gammaSeq (normPoly a) a.sign 1 = 1 := by
  simp [← sq, Int.sign_sq_of_ne_zero ha0]

/-- The `γ`-sequence of the rescaled polynomial `normPoly a` is `|c_n| / |a|`: substituting
`x ↦ |a| x` turns the recursion `c_{n+1} = c_n² + a` into the `γ`-recursion of `normPoly a`.
(At `n = 0` both sides vanish.) -/
theorem abs_cSeq_eq_gammaSeq_mul_abs (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    |cSeq a n| = gammaSeq (normPoly a) a.sign n * |a| := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k
    · simp [gammaSeq_normPoly_one (ne_zero_of_not_isSquare_neg ha)]
    · rw [abs_of_pos (cSeq_pos ha (by lia)), cSeq_succ a k.succ_pos, ← sq_abs (cSeq a _), ih,
        gammaSeq_succ _ _ k.succ_pos, eval_normPoly]
      linear_combination -Int.sign_mul_abs a

/-- The `γ`-sequence of `normPoly a` is positive, as `c_n ≠ 0` for `n ≥ 1`. -/
lemma gammaSeq_normPoly_pos (ha : ¬IsSquare (-a : ℚ)) :
    ∀ n ≥ 1, 0 < gammaSeq (normPoly a) a.sign n := fun n hn ↦
  (mul_pos_iff_of_pos_right (abs_pos.mpr (ne_zero_of_not_isSquare_neg ha))).mp
    (abs_cSeq_eq_gammaSeq_mul_abs ha n ▸ abs_pos.mpr (cSeq_ne_zero ha n hn))

/-- `|b_n| = β_n` for `n ≥ 2`, `β` the `β`-sequence of the rescaled polynomial `normPoly a`: both
are Möbius products, of `|c_d| = γ_d · |a|` and of `γ_d`, and the factors `|a|` cancel because the
exponents `μ(n/d)` sum to zero. -/
theorem abs_bSeq_eq_betaSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) :
    |bSeq a n| = betaSeq (normPoly a) a.sign n := by
  have ha0 := ne_zero_of_not_isSquare_neg ha
  rw [← Int.cast_inj (α := ℚ), Int.cast_abs, intCast_bSeq ha (by lia), abs_moebiusFactorK,
    intCast_betaSeq (evenPoly_normPoly a) (Int.sign_sq_of_ne_zero ha0)
      (fun d hd ↦ (gammaSeq_normPoly_pos ha d hd).ne') (by lia),
    ← moebiusFactorK_mul_const (gammaSeq (normPoly a) a.sign)
      (by simpa using ha0 : algebraMap ℤ ℚ |a| ≠ 0) hn]
  simp only [abs_cSeq_eq_gammaSeq_mul_abs ha]

/-! ### Theorem (Section 3) -/

/-- In each of the three cases of the Section 3 theorem, `-a` is not a square in `ℚ`. -/
lemma not_isSquare_neg_of_cases
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ¬IsSquare (-a : ℚ) :=
  mod_cast show ¬IsSquare (-a) by grind [not_isSquare_of_neg]

/-- Lemma 2.2 applied to the `c`-sequence: in each of the three cases of the Section 3 theorem,
no `|b_n|` with `n ≥ 2` is a square. Case a) gives `g(0) = 1`, `g(1) ≡ 2 mod 4` for the rescaled
polynomial `g = normPoly a`, cases b) and c) give `g(1) ≡ 3 mod 4`. -/
theorem not_isSquare_abs_bSeq
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a)))
    {n : ℕ} (hn : 2 ≤ n) : ¬IsSquare |bSeq a n| := by
  have ha := not_isSquare_neg_of_cases hcase
  rw [abs_bSeq_eq_betaSeq ha hn, ← Rat.isSquare_intCast_iff]
  refine not_isSquare_betaSeq_of_pos (evenPoly_normPoly a)
    (Int.sign_sq_of_ne_zero (ne_zero_of_not_isSquare_neg ha)) (gammaSeq_normPoly_pos ha) ?_ n hn
  grind [eval_normPoly, Int.sign_eq_one_of_pos, Int.sign_eq_neg_one_of_neg, abs_of_pos, abs_of_neg]

/-- Section 3, main result: if `a > 0` and `a ≡ 1 or 2 mod 4`, or `a < 0`, `a ≡ 0 mod 4` and `-a` is
not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem section3_main
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) := fun n _ ↦
  section1_squarefree (not_isSquare_neg_of_cases hcase) n fun _ hk2 _ ↦
    not_isSquare_abs_bSeq hcase hk2

end

end QuadraticIterates
