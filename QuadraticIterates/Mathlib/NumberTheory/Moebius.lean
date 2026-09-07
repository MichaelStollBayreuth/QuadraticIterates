/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Radical.Basic

import Mathlib.RingTheory.Radical.NatInt
import QuadraticIterates.Mathlib.Algebra.BigOperators

/-!
# Sums of the Möbius function over divisors

Restricted Möbius sums over divisors and divisor antidiagonals; the sign partition of the divisors
`t` of a squarefree `n'` by `μ (n'/t) = ±1`, which is balanced on every set of divisors with
vanishing Möbius sum (all divisors, the odd ones, the even ones), and the resulting quotient form
`ArithmeticFunction.prod_pow_moebius_eq_div` of Möbius products; the parity of the twist exponents
`∑_{t ∣ n} (2^(kt-1) - 1)` of a squarefree `n` (`Squarefree.even_sum_two_pow_mul_sub_one`,
`Squarefree.odd_sum_two_pow_sub_one`).

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Finset

namespace ArithmeticFunction

/-- `∑_{d ∣ n} μ d = [n = 1]`: the Möbius function is the Dirichlet inverse of `ζ`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  simpa [moebius_mul_coe_zeta, one_apply] using (coe_mul_zeta_apply (f := μ) (x := n)).symm

theorem sum_divisorsAntidiagonal_moebius_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal, μ x.1 = 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun i _ ↦ μ i), sum_divisors_moebius, ite_eq_right (by lia)]

/-- The Möbius sum over the divisor antidiagonal of `n ≥ 2` without the pair `(n, 1)` is `-μ n`. -/
theorem sum_erase_divisorsAntidiagonal_moebius_eq_neg {n : ℕ} (hn : 2 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal.erase (n, 1), μ x.1 = -μ n :=
  have hmem : (n, 1) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, by lia⟩
  eq_neg_of_add_eq_zero_right
    ((Finset.add_sum_erase _ _ hmem).trans (sum_divisorsAntidiagonal_moebius_eq_zero hn))

/-- The antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` is a product over the divisors of the
radical `n' = rad n`, namely `∏_{t ∣ n'} F (k t) ^ μ (n'/t)` with `k = n / n'`, because `μ e = 0`
unless `e ∣ n'`. -/
theorem prod_pow_moebius_eq_prod_divisors_radical {G : Type*} [DivisionCommMonoid G] (n k n' : ℕ)
    (hn : 1 ≤ n) (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → G) :
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

theorem sum_divisors_moebius_div_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    ∑ t ∈ n.divisors, μ (n / t) = 0 := by
  rw [Nat.sum_div_divisors, sum_divisors_moebius, ite_eq_right (by lia)]

/-- For squarefree `n'`, every divisor `t` of `n'` has `μ (n'/t) = 1` or `μ (n'/t) = -1`. -/
theorem _root_.Squarefree.moebius_div_eq_one_or_eq_neg_one {n' t : ℕ} (hsf : Squarefree n')
    (ht : t ∈ n'.divisors) : μ (n' / t) = 1 ∨ μ (n' / t) = -1 :=
  moebius_ne_zero_iff_eq_or.mp (moebius_ne_zero_iff_squarefree.mpr
    (hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ht))))

/-- For squarefree `n'`, a set `S` of divisors of `n'` on which `∑ μ (n'/t)` vanishes contains
as many `t` with `μ (n'/t) = 1` as with `μ (n'/t) = -1`. -/
theorem _root_.Squarefree.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one {n' : ℕ}
    (hsf : Squarefree n') {S : Finset ℕ} (hS : S ⊆ n'.divisors)
    (hsum : ∑ t ∈ S, μ (n' / t) = 0) :
    #{t ∈ S | μ (n' / t) = 1} = #{t ∈ S | μ (n' / t) = -1} :=
  Finset.card_filter_eq_one_eq_card_filter_eq_neg_one_of_sum_eq_zero
    (fun _ ht ↦ hsf.moebius_div_eq_one_or_eq_neg_one (hS ht)) hsum

/-- For squarefree `n'`, a set `S` of divisors of `n'` is the union of its two sign classes
`μ (n'/t) = 1` and `μ (n'/t) = -1`. -/
theorem _root_.Squarefree.filter_moebius_div_eq_one_union_filter_eq_neg_one_of_subset {n' : ℕ}
    (hsf : Squarefree n') {S : Finset ℕ} (hS : S ⊆ n'.divisors) :
    {t ∈ S | μ (n' / t) = 1} ∪ {t ∈ S | μ (n' / t) = -1} = S := by
  rw [← Finset.filter_or]
  exact Finset.filter_true_of_mem fun t ht ↦ hsf.moebius_div_eq_one_or_eq_neg_one (hS ht)

theorem _root_.Squarefree.filter_moebius_div_eq_one_union_filter_eq_neg_one {n' : ℕ}
    (hsf : Squarefree n') :
    {t ∈ n'.divisors | μ (n' / t) = 1} ∪ {t ∈ n'.divisors | μ (n' / t) = -1} = n'.divisors :=
  hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one_of_subset subset_rfl

/-- For squarefree `n'`, a product over the divisors of `n'` is the product over the sign class
`μ (n'/t) = 1` times the product over the sign class `μ (n'/t) = -1`. -/
@[to_additive _root_.Squarefree.sum_filter_moebius_div_eq_one_add_sum_filter_eq_neg_one /-- For
squarefree `n'`, a sum over the divisors of `n'` is the sum over the sign class `μ (n'/t) = 1`
plus the sum over the sign class `μ (n'/t) = -1`. -/]
theorem _root_.Squarefree.prod_filter_moebius_div_eq_one_mul_prod_filter_eq_neg_one
    {M : Type*} [CommMonoid M] {n' : ℕ} (hsf : Squarefree n') (f : ℕ → M) :
    (∏ t ∈ n'.divisors with μ (n' / t) = 1, f t) * ∏ t ∈ n'.divisors with μ (n' / t) = -1, f t =
      ∏ t ∈ n'.divisors, f t := by
  rw [← Finset.prod_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia),
    hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one]

/-- A set `S` of divisors of a squarefree `n'` on which `∑ μ (n'/t)` vanishes has twice as many
elements as its sign class `μ (n'/t) = 1`. -/
theorem _root_.Squarefree.card_eq_two_mul_card_filter_moebius_div_eq_one {n' : ℕ}
    (hsf : Squarefree n') {S : Finset ℕ} (hS : S ⊆ n'.divisors)
    (hsum : ∑ t ∈ S, μ (n' / t) = 0) : #S = 2 * #{t ∈ S | μ (n' / t) = 1} := by
  nth_rw 1 [← hsf.filter_moebius_div_eq_one_union_filter_eq_neg_one_of_subset hS]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by lia),
    ← hsf.card_filter_moebius_div_eq_one_eq_card_filter_eq_neg_one hS hsum, two_mul]

/-- A set of divisors of a squarefree `n'` on which `∑ μ (n'/t)` vanishes has evenly many
elements: its two sign classes have the same size. -/
theorem _root_.Squarefree.even_card_of_sum_moebius_div_eq_zero {n' : ℕ} (hsf : Squarefree n')
    {S : Finset ℕ} (hS : S ⊆ n'.divisors) (hsum : ∑ t ∈ S, μ (n' / t) = 0) : Even #S :=
  ⟨_, (hsf.card_eq_two_mul_card_filter_moebius_div_eq_one hS hsum).trans (two_mul _)⟩

/-- A squarefree `n > 1` has `2 #{t ∣ n : μ(n/t) = 1}` divisors: the two halves of the sign
partition have the same size. -/
theorem _root_.Squarefree.card_divisors_eq_two_mul {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n) :
    #n.divisors = 2 * #{t ∈ n.divisors | μ (n / t) = 1} :=
  hsf.card_eq_two_mul_card_filter_moebius_div_eq_one subset_rfl
    (sum_divisors_moebius_div_eq_zero hn1)

/-- The antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` is the quotient of the product of the
`F (k t)` over the divisors `t` of `n' = rad n` with `μ (n'/t) = 1` by the product over those with
`μ (n'/t) = -1`, where `k = n / n'`. -/
theorem prod_pow_moebius_eq_div {G : Type*} [DivisionCommMonoid G] (n k n' : ℕ) (hn : 1 ≤ n)
    (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → G) :
    ∏ x ∈ n.divisorsAntidiagonal, F x.2 ^ (μ x.1)
      = (∏ t ∈ n'.divisors with μ (n' / t) = 1, F (k * t)) /
          ∏ t ∈ n'.divisors with μ (n' / t) = -1, F (k * t) := by
  rw [prod_pow_moebius_eq_prod_divisors_radical n k n' hn hn' hk F, Finset.prod_filter,
    Finset.prod_filter, div_eq_mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rcases moebius_eq_or (n' / t) with h | h | h <;> simp [h]

/-- The Möbius sum `∑_{ed = n, m ∣ d} μ e` over the antidiagonal pairs whose second coordinate is
a multiple of `m` is `1` if `n = m` and `0` otherwise: it is `∑_{e ∣ n/m} μ e` when `m ∣ n`. -/
theorem sum_divisorsAntidiagonal_filter_dvd_moebius {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
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
      ite_eq_right fun h ↦ hmn (dvd_of_eq h.symm)]

/-- The divisor form of `ArithmeticFunction.sum_divisorsAntidiagonal_filter_dvd_moebius`:
`∑ μ (n/t)` over the divisors `t` of `n` that are multiples of `m` is `1` if `n = m` and `0`
otherwise. -/
theorem sum_divisors_filter_dvd_moebius_div {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ t ∈ n.divisors with m ∣ t, μ (n / t) = if n = m then 1 else 0 := by
  rw [← sum_divisorsAntidiagonal_filter_dvd_moebius hm hn, Finset.sum_filter, Finset.sum_filter,
    Nat.sum_divisorsAntidiagonal' fun i j ↦ if m ∣ j then μ i else 0]

/-- For `n ≥ 3`, the Möbius sums `∑ μ (n/t)` over the even and over the odd divisors `t` of `n`
both vanish (the even ones are the multiples of `2 ≠ n`). -/
theorem sum_divisors_filter_mod_two_moebius_div {n : ℕ} (hn : 3 ≤ n) (i : ℕ) :
    ∑ t ∈ n.divisors with t % 2 = i, μ (n / t) = 0 := by
  have h0 : ∑ t ∈ n.divisors with t % 2 = 0, μ (n / t) = 0 := by
    simpa [← Nat.dvd_iff_mod_eq_zero, show n ≠ 2 by lia] using
      sum_divisors_filter_dvd_moebius_div (m := 2) (n := n) one_le_two (by lia)
  rcases lt_trichotomy i 1 with hi | rfl | hi
  · obtain rfl : i = 0 := by lia
    exact h0
  · have h := Finset.sum_filter_add_sum_filter_not n.divisors (· % 2 = 0) fun t ↦ μ (n / t)
    rw [sum_divisors_moebius_div_eq_zero (by lia), h0, zero_add,
      Finset.filter_congr (q := (· % 2 = 1)) fun t _ ↦ by lia] at h
    exact h
  · rw [Finset.filter_false_of_mem fun _ _ h ↦ by lia, Finset.sum_empty]

/-- For squarefree `n ≥ 3`, `n` has evenly many even and evenly many odd divisors. -/
theorem _root_.Squarefree.even_card_filter_divisors_mod_two {n : ℕ} (hsf : Squarefree n)
    (hn : 3 ≤ n) (i : ℕ) : Even #{t ∈ n.divisors | t % 2 = i} :=
  hsf.even_card_of_sum_moebius_div_eq_zero (Finset.filter_subset _ _)
    (sum_divisors_filter_mod_two_moebius_div hn i)

/-! ### The twist exponents -/

/-- The divisors `t` of `n` with `t - 1 ≥ 1` are the divisors other than `1`. -/
theorem _root_.Nat.divisors_filter_one_le_sub_one (n : ℕ) :
    {t ∈ n.divisors | 1 ≤ t - 1} = n.divisors.erase 1 := by
  rw [← Finset.filter_ne']
  exact Finset.filter_congr fun t ht ↦ by have := Nat.pos_of_mem_divisors ht; lia

/-- The parity of `∑_{t ∈ S} (2^(m t) - 1)` is that of the number of `t ∈ S` with `m t ≥ 1`. -/
theorem _root_.Finset.sum_two_pow_sub_one_mod_two (S : Finset ℕ) (m : ℕ → ℕ) :
    (∑ t ∈ S, (2 ^ m t - 1)) % 2 = #{t ∈ S | 1 ≤ m t} % 2 := by
  rw [Finset.sum_nat_mod, Finset.card_eq_sum_ones, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rcases Nat.eq_zero_or_pos (m t) with h | h
  · simp [h]
  · rw [ite_eq_left (show 1 ≤ m t from h)]
    exact Nat.odd_iff.mp
      (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, h.ne'⟩) odd_one)

/-- The twist exponent `F = ∑_{t ∣ n} (2^(kt-1) - 1)` is even for `k ≥ 2` (`n` squarefree,
`n > 1`): all terms are odd and there are evenly many. -/
theorem _root_.Squarefree.even_sum_two_pow_mul_sub_one {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n)
    {k : ℕ} (hk : 2 ≤ k) : Even (∑ t ∈ n.divisors, (2 ^ (k * t - 1) - 1)) := by
  rw [Nat.even_iff, Finset.sum_two_pow_sub_one_mod_two, Finset.filter_true_of_mem fun t ht ↦ ?_,
    hsf.card_divisors_eq_two_mul hn1, Nat.mul_mod_right]
  have := hk.trans (Nat.le_mul_of_pos_right k (Nat.pos_of_mem_divisors ht))
  lia

/-- The twist exponent `F = ∑_{t ∣ n} (2^(t-1) - 1)` is odd for squarefree `n > 1`: all terms
but the one at `t = 1` are odd, and there are evenly many divisors. -/
theorem _root_.Squarefree.odd_sum_two_pow_sub_one {n : ℕ} (hsf : Squarefree n) (hn1 : 1 < n) :
    Odd (∑ t ∈ n.divisors, (2 ^ (t - 1) - 1)) := by
  have hA : 1 ≤ #{t ∈ n.divisors | μ (n / t) = 1} :=
    Finset.card_pos.mpr
      ⟨n, by simp [Nat.mem_divisors_self n (by lia), Nat.div_self (by lia : 0 < n)]⟩
  rw [Nat.odd_iff, Finset.sum_two_pow_sub_one_mod_two, Nat.divisors_filter_one_le_sub_one,
    Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr (by lia)), hsf.card_divisors_eq_two_mul hn1]
  lia

/-- For a `gcd`-`min` function `g` and a least element `m` of the level set `{d ∣ n : k ≤ g d}`,
that level set consists of the multiples of `m` among the divisors of `n`. -/
theorem le_iff_dvd_of_forall_gcd_eq_min (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) {n k m : ℕ} (hmn : m ∈ n.divisors)
    (hmk : k ≤ g m) (hmle : ∀ d ∈ n.divisors, k ≤ g d → m ≤ d) {d : ℕ} (hd : d ∈ n.divisors) :
    k ≤ g d ↔ m ∣ d := by
  have hm := Nat.pos_of_mem_divisors hmn
  have h := hmin m hm d (Nat.pos_of_mem_divisors hd)
  refine ⟨fun hkd ↦ Nat.gcd_eq_left_iff_dvd.mp (le_antisymm (Nat.gcd_le_left d hm)
    (hmle _ ?_ (h ▸ le_min hmk hkd))), fun hmd ↦ ?_⟩
  · exact Nat.mem_divisors.mpr
      ⟨(Nat.gcd_dvd_right m d).trans (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
  · rw [Nat.gcd_eq_left hmd] at h
    exact hmk.trans (h ▸ min_le_right _ _)

/-- For a level set `{d : k ≤ g d}` of a `gcd`-`min` function `g`, the antidiagonal Möbius transform
of its indicator (in the second coordinate) over `n` is `0` or `1`; in particular nonnegative. -/
theorem sum_mul_moebius_boole_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (if k ≤ g x.2 then 1 else 0) := by
  have hmem (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : x.2 ∈ n.divisors :=
    Nat.snd_mem_divisors_of_mem_antidiagonal hx
  simp_rw [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rcases (n.divisors.filter (k ≤ g ·)).eq_empty_or_nonempty with he | hne
  · rw [Finset.filter_false_of_mem fun x hx hkx ↦
      Finset.notMem_empty x.2 (he ▸ Finset.mem_filter.mpr ⟨hmem x hx, hkx⟩), Finset.sum_empty]
  obtain ⟨m, hmS, hmle⟩ := Finset.exists_min_image _ id hne
  obtain ⟨hmn, hmk⟩ := Finset.mem_filter.mp hmS
  rw [Finset.filter_congr fun x hx ↦ le_iff_dvd_of_forall_gcd_eq_min g hmin hmn hmk
      (fun d hd hkd ↦ hmle d (Finset.mem_filter.mpr ⟨hd, hkd⟩)) (hmem x hx),
    sum_divisorsAntidiagonal_filter_dvd_moebius (Nat.pos_of_mem_divisors hmn) hn]
  split_ifs <;> decide

/-- **Nonnegativity of the Möbius transform of a `gcd`-`min` function.** If `g` satisfies
`g (gcd x y) = min (g x) (g y)`, then `∑_{ed = n} μ e · g d ≥ 0`. This is the arithmetic core of the
integrality of the Möbius factors of a strong divisibility sequence. -/
theorem sum_mul_moebius_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (g x.2 : ℤ) := by
  have hmono (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : g x.2 ≤ g n := by
    have hx2 : x.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hx
    have h := hmin x.2 (Nat.pos_of_mem_divisors hx2) n (by lia)
    rw [Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hx2)] at h
    lia
  have hcard (j : ℕ) (hj : j ≤ g n) :
      (j : ℤ) = ∑ k ∈ Finset.Icc 1 (g n), if k ≤ j then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole, show (Finset.Icc 1 (g n)).filter (· ≤ j) = Finset.Icc 1 j by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; lia, Nat.card_Icc]
    simp
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [hcard (g x.2) (hmono x hx), Finset.mul_sum],
    Finset.sum_comm]
  exact Finset.sum_nonneg fun k _ ↦ sum_mul_moebius_boole_nonneg g hmin hn k

end ArithmeticFunction
