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
theorem of the paper. The first part of the Section 1 theorem is proved for a rational parameter
`a` whose iterates are irreducible (`QuadraticIterates.section1_tfae_of_irreducible`); the
integer statements are its corollaries through Corollary 1.3.

## Main statements

* `QuadraticIterates.section1_tfae_of_irreducible`: for `a ∈ ℚ` with all `f_k` irreducible,
  `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff `b_1, …, b_n` are 2-independent
  (`QuadraticIterates.section1_a_iff_b_of_irreducible`, which only needs `f_k` irreducible for
  `k ≤ n`, and `QuadraticIterates.section1_b_iff_c`).
* `QuadraticIterates.section1_tfae`: for an integer `a` with `-a` not a square (so that all `f_k`
  are irreducible, Corollary 1.3), `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff
  `b_1, …, b_n` are 2-independent (`QuadraticIterates.section1_a_iff_b`).
* `QuadraticIterates.section1_of_not_isSquare_abs_bSeq`: if none of `|b_2|, …, |b_n|` is a square,
  then `Ω_n ≅ [C₂]ⁿ`.
* `QuadraticIterates.section3_main`: if `a > 0` and `a ≡ 1, 2 mod 4`, or `a < 0`, `a ≡ 0 mod 4` and
  `-a` is not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. The proof rescales `X² + a` to
  `normPoly a = |a| X² + sgn a`, whose `γ`-sequence is `|c_n| / |a|`
  (`QuadraticIterates.abs_cSeq_eq_gammaSeq_mul_abs`) and whose `β`-sequence is `|b_n|`
  (`QuadraticIterates.abs_bSeq_eq_betaSeq`), and applies Lemma 2.2
  (`QuadraticIterates.not_isSquare_abs_bSeq`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

section

variable {a : ℤ}

/-! ### Lemma 1.1 b): the integer factors `b_n` -/

/-- The constant-valuation shape for `c`: the specialization of
`QuadraticIterates.factorization_gammaSeq_shape` to `X² + a`, `ε = -1`, in the form consumed by
`moebiusFactorR_isRelPrime`. -/
lemma factorization_cSeq_shape (ha : ¬IsSquare (-a : ℚ)) :
    ∀ q : ℤ, Prime q → normalize q = q →
      ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1, factorization (cSeq a k) q = if m ∣ k then E else 0 :=
  fun _ ↦ factorization_gammaSeq_shape (evenPoly_X_sq_add_C a) neg_one_sq (cSeq_ne_zero ha)

/-- Lemma 1.1 b): the Möbius product `∏_{ed = n} c_d^{μ(e)}` is the integer `b_n`, since `c` is a
strong divisibility sequence. -/
lemma intCast_bSeq_eq_moebiusFactorK (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    ((bSeq a n : ℤ) : ℚ) = moebiusFactorK (cSeq a) n :=
  algebraMap_moebiusFactorR (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

/-- The integer `b_n` cast to `ℚ` is the rational `b_n` of the cast parameter. -/
lemma intCast_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    ((bSeq a n : ℤ) : ℚ) = bSeq (a : ℚ) n := by
  rw [intCast_bSeq_eq_moebiusFactorK ha hn, bSeq_eq_moebiusFactorK, moebiusFactorK_eq_prod,
    moebiusFactorK_eq_prod]
  simp [intCast_cSeq]

lemma bSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : bSeq a n ≠ 0 :=
  moebiusFactorR_ne_zero (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

/-- Möbius inversion for the integer factors (Lemma 1.1 b): `c_n = ∏_{d ∣ n} b_d`. -/
lemma cSeq_eq_prod_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    cSeq a n = ∏ d ∈ n.divisors, bSeq a d :=
  prod_moebiusFactorR (cSeq_ne_zero ha) (cSeq_associated_gcd a) hn

/-- `b_2 = -a - 1`, from `c_2 = b_1 b_2` with `c_2 = a² + a` and `b_1 = -a`. -/
lemma bSeq_two (ha : ¬IsSquare (-a : ℚ)) : bSeq a 2 = -a - 1 := by
  have h := cSeq_eq_prod_bSeq ha one_le_two
  rw [Nat.prime_two.divisors, Finset.prod_pair one_lt_two.ne, bSeq_one, cSeq_two] at h
  exact mul_left_cancel₀ (neg_ne_zero.mpr (ne_zero_of_not_isSquare_neg ha))
    (h.symm.trans (by ring))

/-- The integer factors `b_n` are pairwise coprime (Lemma 1.1 b): the valuation of `b_n` at
each prime is supported on a single index, so no prime divides two distinct factors. -/
lemma isCoprime_bSeq (ha : ¬IsSquare (-a : ℚ)) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) : IsCoprime (bSeq a m) (bSeq a n) :=
  (moebiusFactorR_isRelPrime (cSeq_ne_zero ha) (cSeq_associated_gcd a)
    (factorization_cSeq_shape ha) hm hn hmn).isCoprime

end

/-! ### Theorem (Section 1) over `ℚ` -/

section

variable {a : ℚ}

/-- Section 1, `(a) ↔ (b)`, for a rational parameter `a` whose iterates `f_0, …, f_n` are
irreducible: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent. By induction on `n`:
`Ω_{n+1} ≅ [C₂]^{n+1}` iff `Ω_n ≅ [C₂]ⁿ` and `[K_{n+1} : K_n] = 2^{2^n}`
(`QuadraticIterates.nonempty_mulEquiv_succ_iff`, Lemma 1.4), the degree condition says that
`c_{n+1}` is not a square in `K_n` (`QuadraticIterates.relfinrank_succ_eq_two_pow_iff`, Lemma 1.6,
which needs `f_n` irreducible and `c_{n+1} ≠ 0`, i.e. `f_{n+1}` irreducible), and given
`Ω_n ≅ [C₂]ⁿ` this means that `c_1, …, c_{n+1}` are 2-independent
(`QuadraticIterates.not_isSquare_algebraMap_iff_twoIndependent_snoc`, Lemma 1.5). -/
theorem section1_a_iff_b_of_irreducible {n : ℕ} (hirr : ∀ k ≤ n, Irreducible fℚ[a, k]) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)) := by
  induction n with
  | zero =>
    exact ⟨fun _ S ⟨i, _⟩ ↦ i.elim0, fun _ ↦ (nonempty_mulEquiv_iff_finrank_eq a 0).mpr (by simp)⟩
  | succ n ih =>
    have ih := ih fun k hk ↦ hirr k (hk.trans n.le_succ)
    have h16 := relfinrank_succ_eq_two_pow_iff (hirr n n.le_succ)
      (cSeq_succ_ne_zero_of_irreducible (hirr (n + 1) le_rfl))
    rw [← Fin.snoc_init_self (fun i : Fin (n + 1) ↦ cSeq a ((i : ℕ) + 1)),
      nonempty_mulEquiv_succ_iff a n]
    refine ⟨fun ⟨hiso, hrel⟩ ↦ ?_, fun h ↦ ?_⟩
    · exact (not_isSquare_algebraMap_iff_twoIndependent_snoc hiso (ih.mp hiso)).mp (h16.mp hrel)
    · have hiso : Nonempty (GaloisGroup a n ≃* WreathPower n) := ih.mpr h.of_snoc
      exact ⟨hiso, h16.mpr ((not_isSquare_algebraMap_iff_twoIndependent_snoc hiso h.of_snoc).mpr h)⟩

lemma bSeq_ne_zero_of_forall_cSeq_ne_zero (hc : ∀ k ≥ 1, cSeq a k ≠ 0) (n : ℕ) : bSeq a n ≠ 0 :=
  bSeq_eq_moebiusFactorK a n ▸ moebiusFactorK_ne_zero hc n

/-- Möbius inversion over `ℚ`: `c_n = ∏_{d ∣ n} b_d` when no `c_k` vanishes. -/
lemma cSeq_eq_prod_bSeq_of_forall_cSeq_ne_zero (hc : ∀ k ≥ 1, cSeq a k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    cSeq a n = ∏ d ∈ n.divisors, bSeq a d := by
  simpa [bSeq_eq_moebiusFactorK] using prod_moebiusFactorK (K := ℚ) hc hn

/-- In `ℚˣ/(ℚˣ)²`, the class of `c_m` is the sum of the classes of the `b_d` over `d ∣ m`, when
no `c_k` vanishes. -/
lemma sqClass_cSeq_eq_sum_divisors (hc : ∀ k ≥ 1, cSeq a k ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    sqClass (cSeq a m) = ∑ d ∈ m.divisors, sqClass (bSeq a d) := by
  rw [cSeq_eq_prod_bSeq_of_forall_cSeq_ne_zero hc hm]
  exact sqClass_prod fun d _ ↦ bSeq_ne_zero_of_forall_cSeq_ne_zero hc d

/-- In `ℚˣ/(ℚˣ)²`, the class of `b_m` is the Möbius-weighted sum of the classes of the `c_d`, when
no `c_k` vanishes. -/
lemma sqClass_bSeq_eq_sum_divisorsAntidiagonal (hc : ∀ k ≥ 1, cSeq a k ≠ 0) (m : ℕ) :
    sqClass (bSeq a m) = ∑ x ∈ m.divisorsAntidiagonal, (μ x.1) • sqClass (cSeq a x.2) := by
  simp only [bSeq_eq_moebiusFactorK, moebiusFactorK_eq_prod, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact sqClass_prod_zpow _ fun x hx ↦ ne_zero_of_mem_divisorsAntidiagonal hc hx

/-- `F d` is a value of `fun i : Fin n ↦ F (i + 1)` whenever `d ∣ i + 1` for some `i : Fin n`. -/
private lemma mem_range_of_dvd {α : Type*} (F : ℕ → α) {n : ℕ} {i : Fin n} {d : ℕ}
    (hd : d ∣ (i : ℕ) + 1) : F d ∈ Set.range fun j : Fin n ↦ F ((j : ℕ) + 1) :=
  have h1 := Nat.pos_of_dvd_of_pos hd i.1.succ_pos
  ⟨⟨d - 1, by have := Nat.le_of_dvd i.1.succ_pos hd; lia⟩, by simp [Nat.sub_add_cancel h1]⟩

/-- Section 1, `(b) ↔ (c)`, for a rational parameter with nonvanishing `c_k`: `c_1, …, c_n` are
2-independent iff `b_1, …, b_n` are 2-independent, since their classes in `ℚˣ/(ℚˣ)²` span the same
`𝔽₂`-subspace (Möbius inversion in both directions). -/
theorem section1_b_iff_c (hc : ∀ k ≥ 1, cSeq a k ≠ 0) (n : ℕ) :
    TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)) ↔
      TwoIndependent (fun i : Fin n ↦ bSeq a ((i : ℕ) + 1)) := by
  simp only [twoIndependent_iff_linearIndependent]
  refine linearIndependent_iff_of_span_range_eq (le_antisymm ?_ ?_) <;>
    rw [Submodule.span_le, Set.range_subset_iff] <;> intro i
  · rw [SetLike.mem_coe, sqClass_cSeq_eq_sum_divisors hc i.1.succ_pos]
    exact Submodule.sum_mem _ fun d hd ↦ Submodule.subset_span
      (mem_range_of_dvd (fun k ↦ sqClass (bSeq a k)) (Nat.dvd_of_mem_divisors hd))
  · rw [SetLike.mem_coe, sqClass_bSeq_eq_sum_divisorsAntidiagonal hc]
    exact Submodule.sum_mem _ fun x hx ↦ zsmul_mem (Submodule.subset_span
      (mem_range_of_dvd (fun k ↦ sqClass (cSeq a k))
        (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)))) _

/-- Theorem (Section 1), part 1, for a rational parameter `a` all of whose iterates are
irreducible: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff `b_1, …, b_n` are
2-independent. -/
theorem section1_tfae_of_irreducible (hirr : ∀ k, Irreducible fℚ[a, k]) (n : ℕ) :
    [Nonempty (GaloisGroup a n ≃* WreathPower n),
     TwoIndependent (fun i : Fin n ↦ cSeq a ((i : ℕ) + 1)),
     TwoIndependent (fun i : Fin n ↦ bSeq a ((i : ℕ) + 1))].TFAE := by
  tfae_have 1 ↔ 2 := section1_a_iff_b_of_irreducible fun k _ ↦ hirr k
  tfae_have 2 ↔ 3 := section1_b_iff_c (cSeq_ne_zero_of_irreducible hirr) n
  tfae_finish

end

/-! ### Theorem (Section 1) for integers -/

section

variable {a : ℤ}

/-- Section 1, `(a) ↔ (b)`, for an integer `a` with `-a` not a square: `Ω_n ≅ [C₂]ⁿ` iff
`c_1, …, c_n` are 2-independent, by Corollary 1.3 and
`QuadraticIterates.section1_a_iff_b_of_irreducible`. -/
theorem section1_a_iff_b (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent (fun i : Fin n ↦ cSeq (a : ℚ) ((i : ℕ) + 1)) :=
  section1_a_iff_b_of_irreducible fun k _ ↦ irreducible_iteratedPoly ha k

/-- Theorem (Section 1), part 1: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent iff `b_1, …, b_n`
are 2-independent. -/
theorem section1_tfae (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    [Nonempty (GaloisGroup a n ≃* WreathPower n),
     TwoIndependent (fun i : Fin n ↦ cSeq (a : ℚ) ((i : ℕ) + 1)),
     TwoIndependent (fun i : Fin n ↦ bSeq (a : ℚ) ((i : ℕ) + 1))].TFAE :=
  section1_tfae_of_irreducible (irreducible_iteratedPoly ha) n

/-- Theorem (Section 1), part 2: if none of `|b_2|, …, |b_n|` is a square, then
`Ω_n ≅ [C₂]ⁿ`. By pairwise coprimality, the `b_k` are 2-independent as soon as no `b_k` and at
most one `-b_k` is a square; `-b_1 = a` is the only candidate, since `b_1 = -a` is not a square. -/
theorem section1_of_not_isSquare_abs_bSeq (ha : ¬IsSquare (-a : ℚ)) (n : ℕ)
    (h : ∀ k ≥ 2, k ≤ n → ¬IsSquare |bSeq a k|) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  have hzero (i : Fin n) (hi : IsSquare (-bSeq a ((i : ℕ) + 1))) : (i : ℕ) = 0 :=
    Nat.eq_zero_of_not_pos fun hi0 ↦ h _ (by lia) i.2 (isSquare_abs_iff.mpr (.inr hi))
  have hsq (i : Fin n) : ¬IsSquare (bSeq a ((i : ℕ) + 1)) := by
    rcases eq_or_ne (i : ℕ) 0 with hi | hi
    · rwa [hi, zero_add, bSeq_one, ← Rat.isSquare_intCast_iff, Int.cast_neg]
    · exact fun hsq ↦ h _ (by lia) i.2 (isSquare_abs_iff.mpr (.inl hsq))
  have hb : TwoIndependent (fun i : Fin n ↦ ((bSeq a ((i : ℕ) + 1) : ℤ) : ℚ)) :=
    (twoIndependent_intCast_iff _).mpr ((twoIndependent_iff_of_pairwise_isCoprime fun i j hij ↦
      isCoprime_bSeq ha i.1.succ_pos j.1.succ_pos (by simpa [Fin.ext_iff] using hij)).mpr
        ⟨hsq, fun i hi j hj ↦ Fin.ext ((hzero i hi).trans (hzero j hj).symm)⟩)
  have hcast : (fun i : Fin n ↦ bSeq (a : ℚ) ((i : ℕ) + 1)) =
      fun i : Fin n ↦ ((bSeq a ((i : ℕ) + 1) : ℤ) : ℚ) :=
    funext fun i ↦ (intCast_bSeq ha i.1.succ_pos).symm
  exact ((section1_tfae ha n).out 3 1).mp (hcast ▸ hb)

/-! ### The `γ`-sequence of the rescaled polynomial -/

/-- `γ[a] n` is the `γ`-sequence of the rescaled polynomial `normPoly a` with `ε = sgn a`,
`gammaSeq (normPoly a) a.sign n`; it is `|c_n| / |a|`
(`QuadraticIterates.abs_cSeq_eq_gammaSeq_mul_abs`). -/
scoped notation:max "γ[" a "]" => gammaSeq (normPoly a) (Int.sign a)

open Lean PrettyPrinter in
/-- Prints `gammaSeq (normPoly a) a.sign` as `γ[a]`. -/
@[scoped app_unexpander gammaSeq]
meta def unexpandGammaNormPoly : Unexpander
  | `($_ $g $s $n) => do `(γ[$(← normPolyArg g s)] $n)
  | `($_ $g $s) => do `(γ[$(← normPolyArg g s)])
  | _ => throw ()
where
  /-- The `a` with `g = normPoly a` and `s = a.sign` (or `Int.sign a`). -/
  normPolyArg (g s : Term) : UnexpandM Term := do
    let `(normPoly $a) := g | throw ()
    let b ← match s with
      | `($(b).sign) => pure b
      | `(Int.sign $b) => pure b
      | _ => throw ()
    unless b.raw.structEq a.raw do throw ()
    return a

/-- `γ_1 = sgn(a) · g(0) = sgn(a)² = 1` for the rescaled polynomial `g = normPoly a`. -/
lemma gammaSeq_normPoly_one (ha0 : a ≠ 0) : γ[a] 1 = 1 := by
  simp [← sq, Int.sign_sq_of_ne_zero ha0]

/-- The `γ`-sequence of the rescaled polynomial `normPoly a` is `|c_n| / |a|`: substituting
`x ↦ |a| x` turns the recursion `c_{n+1} = c_n² + a` into the `γ`-recursion of `normPoly a`.
(At `n = 0` both sides vanish.) -/
theorem abs_cSeq_eq_gammaSeq_mul_abs (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    |cSeq a n| = γ[a] n * |a| := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k
    · simp [gammaSeq_normPoly_one (ne_zero_of_not_isSquare_neg ha)]
    · rw [abs_of_pos (cSeq_pos ha (by lia)), cSeq_succ a k.succ_pos, ← sq_abs (cSeq a _), ih,
        gammaSeq_succ _ _ k.succ_pos, eval_normPoly]
      linear_combination -Int.sign_mul_abs a

/-- The `γ`-sequence of `normPoly a` is positive, as `c_n ≠ 0` for `n ≥ 1`. -/
lemma gammaSeq_normPoly_pos (ha : ¬IsSquare (-a : ℚ)) : ∀ n ≥ 1, 0 < γ[a] n := fun n hn ↦
  (mul_pos_iff_of_pos_right (abs_pos.mpr (ne_zero_of_not_isSquare_neg ha))).mp
    (abs_cSeq_eq_gammaSeq_mul_abs ha n ▸ abs_pos.mpr (cSeq_ne_zero ha n hn))

/-- `|b_n| = β_n` for `n ≥ 2`, `β` the `β`-sequence of the rescaled polynomial `normPoly a`: both
are Möbius products, of `|c_d| = γ_d · |a|` and of `γ_d`, and the factors `|a|` cancel because the
exponents `μ(n/d)` sum to zero. -/
theorem abs_bSeq_eq_betaSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 2 ≤ n) :
    |bSeq a n| = betaSeq (normPoly a) a.sign n := by
  have ha0 := ne_zero_of_not_isSquare_neg ha
  rw [← Int.cast_inj (α := ℚ), Int.cast_abs, intCast_bSeq_eq_moebiusFactorK ha (by lia),
    abs_moebiusFactorK, intCast_betaSeq (evenPoly_normPoly a) (Int.sign_sq_of_ne_zero ha0)
      (fun d hd ↦ (gammaSeq_normPoly_pos ha d hd).ne') (by lia),
    ← moebiusFactorK_mul_const γ[a] (by simpa using ha0 : algebraMap ℤ ℚ |a| ≠ 0) hn]
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
  section1_of_not_isSquare_abs_bSeq (not_isSquare_neg_of_cases hcase) n fun _ hk2 _ ↦
    not_isSquare_abs_bSeq hcase hk2

end

end QuadraticIterates
