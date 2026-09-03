module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Radical.Basic

import Mathlib.RingTheory.Radical.NatInt

/-!
# Sums of the Möbius function over divisors

Restricted Möbius sums over divisors and divisor antidiagonals, and the equal-size
sign partition of the divisors of a squarefree number.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `∑_{d ∣ n} μ d = [n = 1]`: the Möbius function is the Dirichlet inverse of `ζ`. -/
theorem ArithmeticFunction.sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  simpa [moebius_mul_coe_zeta, one_apply] using (coe_mul_zeta_apply (f := μ) (x := n)).symm

/-- `∑_{ed = n} μ e = 0` for `n ≥ 2`. -/
theorem moebius_antidiag_sum_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal, μ x.1 = 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun i _ ↦ μ i), sum_divisors_moebius, if_neg (by lia)]

/-- Rewrites the antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` as a product over the divisors
of the radical `n' = rad n`: `∏_{t ∣ n'} F (k t) ^ μ (n'/t)`, where `k = n / n'`. -/
theorem beta_radical {G : Type*} [DivisionCommMonoid G] (n k n' : ℕ) (hn : 1 ≤ n)
    (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → G) :
    ∏ x ∈ n.divisorsAntidiagonal, F x.2 ^ (μ x.1)
      = ∏ t ∈ n'.divisors, F (k * t) ^ (μ (n' / t)) := by
  have hn0 : n ≠ 0 := by lia
  have hn'0 : n' ≠ 0 := hn' ▸ (Nat.radical_pos n).ne'
  rw [Nat.prod_divisorsAntidiagonal (fun a b ↦ F b ^ (μ a))]
  have hdvd_n' : n' ∣ n := by simp [hk]
  rw [← Finset.prod_subset (Nat.divisors_subset_of_dvd hn0 hdvd_n')]
  · rw [← Nat.prod_div_divisors n' (fun x ↦ F (k * x) ^ (μ (n' / x)))]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hidvd : i ∣ n' := Nat.dvd_of_mem_divisors hi
    simp only [← Nat.mul_div_assoc k hidvd, hk, Nat.div_div_self hidvd hn'0]
  · intro i hiin hinotin
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hsqfree ↦
      hinotin (Nat.mem_divisors.mpr
        ⟨hn' ▸ (UniqueFactorizationMonoid.dvd_radical_iff hsqfree.isRadical hn0).mpr
          (Nat.dvd_of_mem_divisors hiin), hn'0⟩)]

/-- For squarefree `n' > 1`, the divisors of `n'` split into two halves of equal size according
to the sign of `μ(n'/t)`. -/
theorem moebius_sign_partition (n' : ℕ) (hn'1 : 1 < n') (hsf : Squarefree n') :
    ∃ Sp Sm : Finset ℕ, Disjoint Sp Sm ∧ Sp ∪ Sm = n'.divisors ∧ Sp.card = Sm.card ∧
      (∀ t ∈ Sp, μ (n' / t) = 1) ∧ (∀ t ∈ Sm, μ (n' / t) = -1) := by
  have hpm (t : ℕ) (ht : t ∈ n'.divisors) : μ (n' / t) = 1 ∨ μ (n' / t) = -1 :=
    moebius_ne_zero_iff_eq_or.mp (moebius_ne_zero_iff_squarefree.mpr
      (hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ht))))
  refine ⟨n'.divisors.filter fun t ↦ μ (n' / t) = 1, n'.divisors.filter fun t ↦ ¬ μ (n' / t) = 1,
    Finset.disjoint_filter_filter_not _ _ _, Finset.filter_union_filter_not_eq _ _, ?_,
    fun t ht ↦ (Finset.mem_filter.mp ht).2,
    fun t ht ↦ (hpm t (Finset.mem_filter.mp ht).1).resolve_left (Finset.mem_filter.mp ht).2⟩
  have hsum : ∑ t ∈ n'.divisors, (if μ (n' / t) = 1 then (1 : ℤ) else -1) = 0 :=
    calc ∑ t ∈ n'.divisors, (if μ (n' / t) = 1 then (1 : ℤ) else -1)
        = ∑ t ∈ n'.divisors, μ (n' / t) :=
          Finset.sum_congr rfl fun t ht ↦ by rcases hpm t ht with h | h <;> simp [h]
      _ = 0 := by rw [Nat.sum_div_divisors, sum_divisors_moebius, if_neg (by lia)]
  simpa [Finset.sum_ite, add_neg_eq_zero] using hsum

/-- Under a sign partition `(Sp, Sm)` of the divisors of `n' = rad n` (as produced by
`moebius_sign_partition`), the antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` splits as the
quotient `(∏_{t ∈ Sp} F (k t)) / (∏_{t ∈ Sm} F (k t))`, where `k = n / n'`. -/
theorem prod_pow_moebius_eq_div {G : Type*} [DivisionCommMonoid G] (n k n' : ℕ) (hn : 1 ≤ n)
    (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → G)
    {Sp Sm : Finset ℕ} (hdisj : Disjoint Sp Sm) (hunion : Sp ∪ Sm = n'.divisors)
    (hSp : ∀ t ∈ Sp, μ (n' / t) = 1) (hSm : ∀ t ∈ Sm, μ (n' / t) = -1) :
    ∏ x ∈ n.divisorsAntidiagonal, F x.2 ^ (μ x.1)
      = (∏ t ∈ Sp, F (k * t)) / (∏ t ∈ Sm, F (k * t)) := by
  rw [beta_radical n k n' hn hn' hk F, ← hunion, Finset.prod_union hdisj, div_eq_mul_inv,
    ← Finset.prod_inv_distrib]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun t ht ↦ by rw [hSp t ht, zpow_one])
    (Finset.prod_congr rfl fun t ht ↦ by rw [hSm t ht, zpow_neg_one])

/-- The Möbius sum over the antidiagonal pairs `(e, d)` of `n` with `m ∣ d` is `1` if `n = m` and
`0` otherwise (for `m, n ≥ 1`). -/
theorem moebius_restricted_sum (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal with m ∣ x.2, μ x.1 = if n = m then 1 else 0 := by
  by_cases hmn : m ∣ n
  · obtain ⟨N, rfl⟩ := hmn
    rw [Finset.sum_filter, Nat.sum_divisorsAntidiagonal (fun i j ↦ if m ∣ j then μ i else 0),
      ← Finset.sum_filter, Finset.filter_congr (q := (· ∣ N)) fun i hi ↦ by
        rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hi), mul_comm,
          Nat.mul_dvd_mul_iff_left hm],
      Nat.divisors_filter_dvd_of_dvd (by positivity) (dvd_mul_left N m), sum_divisors_moebius]
    simp [mul_eq_left₀ (show m ≠ 0 by lia)]
  · rw [Finset.filter_eq_empty_iff.mpr fun x hx h ↦ hmn (h.trans
      (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))), Finset.sum_empty,
      if_neg fun h ↦ hmn (dvd_of_eq h.symm)]

/-- For a level set `{d : k ≤ g d}` of a `gcd`-`min` function `g`, the antidiagonal Möbius transform
of its indicator (in the second coordinate) over `n` is `0` or `1`; in particular nonnegative. -/
theorem indicator_moebius_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (if k ≤ g x.2 then 1 else 0) := by
  have hmem (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : x.2 ∈ n.divisors :=
    Nat.snd_mem_divisors_of_mem_antidiagonal hx
  simp_rw [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rcases (n.divisors.filter (k ≤ g ·)).eq_empty_or_nonempty with he | hne
  · rw [Finset.filter_false_of_mem fun x hx hkx ↦
      Finset.notMem_empty x.2 (he ▸ Finset.mem_filter.mpr ⟨hmem x hx, hkx⟩), Finset.sum_empty]
  obtain ⟨m, hmS, hmle⟩ := Finset.exists_min_image _ id hne
  obtain ⟨hmn, hmk⟩ := Finset.mem_filter.mp hmS
  have hm1 : 1 ≤ m := Nat.pos_of_mem_divisors hmn
  have hpred (d : ℕ) (hd : d ∈ n.divisors) : k ≤ g d ↔ m ∣ d := by
    have h := hmin m hm1 d (Nat.pos_of_mem_divisors hd)
    refine ⟨fun hkd ↦ ?_, fun hmd ↦ ?_⟩
    · have hgcd : m.gcd d ∈ n.divisors.filter (k ≤ g ·) := Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨(Nat.gcd_dvd_right m d).trans (Nat.dvd_of_mem_divisors hd), by lia⟩,
          h ▸ le_min hmk hkd⟩
      exact Nat.gcd_eq_left_iff_dvd.mp (le_antisymm (Nat.gcd_le_left d hm1) (hmle _ hgcd))
    · rw [Nat.gcd_eq_left hmd] at h
      exact hmk.trans (h ▸ min_le_right _ _)
  rw [Finset.filter_congr fun x hx ↦ hpred x.2 (hmem x hx), moebius_restricted_sum m n hm1 hn]
  split_ifs <;> decide

/-- **Nonnegativity of the Möbius transform of a `gcd`-`min` function.** If `g` satisfies
`g (gcd x y) = min (g x) (g y)`, then `∑_{ed = n} μ e · g d ≥ 0`. This is the arithmetic core of the
integrality of the Möbius factors of a strong divisibility sequence. -/
theorem moebius_transform_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (g x.2 : ℤ) := by
  have hmono (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : g x.2 ≤ g n := by
    have hx2 : x.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hx
    have h := hmin x.2 (Nat.pos_of_mem_divisors hx2) n (by lia)
    rw [Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hx2)] at h
    omega
  have hcard (a : ℕ) (ha : a ≤ g n) :
      (a : ℤ) = ∑ k ∈ Finset.Icc 1 (g n), if k ≤ a then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole, show (Finset.Icc 1 (g n)).filter (· ≤ a) = Finset.Icc 1 a from by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega, Nat.card_Icc]
    simp
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [hcard (g x.2) (hmono x hx), Finset.mul_sum],
    Finset.sum_comm]
  exact Finset.sum_nonneg fun k _ ↦ indicator_moebius_nonneg g hmin n hn k
