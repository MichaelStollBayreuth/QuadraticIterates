module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import QuadraticIterates.Mathlib.NumberTheory.Moebius
public import QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import QuadraticIterates.Mathlib.Algebra.BigOperators
import QuadraticIterates.Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Integrality of Möbius factors of strong divisibility sequences

For a strong divisibility sequence `c` in a UFD `R` (nowhere zero on `n ≥ 1`), the Möbius factor
`∏_{d ∣ n} c_d ^ μ(n/d)`, a priori an element of the fraction field, lies in the image of `R`:
it is the quotient `numProd c n / denProd c n` of two products in `R`, and the denominator
divides the numerator because the Möbius transform of `v_p ∘ c` is nonnegative for every prime
`p` (`sum_mul_moebius_nonneg`). `moebiusFactorR c n` is the unique `R`-preimage; everything
about it follows from the identity `moebiusFactorR_mul_denProd`, in particular
`algebraMap_moebiusFactorR`: its image in any fraction field is the Möbius formula.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius
open UniqueFactorizationMonoid ArithmeticFunction

/-- A sequence that does not vanish at positive indices does not vanish at the second coordinate
of a pair in `n.divisorsAntidiagonal`. -/
theorem ne_zero_of_mem_divisorsAntidiagonal {M : Type*} [Zero M] {c : ℕ → M}
    (hc : ∀ d ≥ 1, c d ≠ 0) {n : ℕ} {x : ℕ × ℕ} (hx : x ∈ n.divisorsAntidiagonal) : c x.2 ≠ 0 :=
  hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/-- The Möbius factor `∏_{ed = n} c_d ^ μ(e)` of `c` in the fraction field. -/
noncomputable def moebiusFactorK (c : ℕ → R) (n : ℕ) : K :=
  ∏ x ∈ n.divisorsAntidiagonal, (algebraMap R K (c x.2)) ^ (μ x.1)

/-- The unfolding lemma of `moebiusFactorK`: rewrite with it instead of unfolding the definition. -/
theorem moebiusFactorK_eq_prod (c : ℕ → R) (n : ℕ) :
    moebiusFactorK (K := K) c n = ∏ x ∈ n.divisorsAntidiagonal, algebraMap R K (c x.2) ^ (μ x.1) :=
  rfl

/-- Scaling a sequence by a constant `t` does not change its Möbius factors of index `n ≥ 2`,
since the exponents `μ(e)` sum to zero. -/
theorem moebiusFactorK_mul_const (c : ℕ → R) {t : R} (ht : algebraMap R K t ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : moebiusFactorK (K := K) (fun d ↦ c d * t) n = moebiusFactorK c n := by
  simp only [moebiusFactorK_eq_prod, map_mul, mul_zpow, Finset.prod_mul_distrib,
    Finset.prod_zpow_eq_zpow_sum₀ ht, sum_divisorsAntidiagonal_moebius_eq_zero hn, zpow_zero,
    mul_one]

/-- In an ordered field, the absolute value of a Möbius factor of an integer sequence is the
Möbius factor of the sequence of absolute values. -/
theorem abs_moebiusFactorK [LinearOrder K] [IsStrictOrderedRing K] (c : ℕ → ℤ) (n : ℕ) :
    |moebiusFactorK (K := K) c n| = moebiusFactorK (K := K) (fun d ↦ |c d|) n := by
  simp [moebiusFactorK_eq_prod, Finset.abs_prod, abs_zpow]

/-- The numerator `∏_{ed = n, μ(e) = 1} c_d` of the Möbius factor, in `R`. -/
noncomputable def numProd (c : ℕ → R) (n : ℕ) : R :=
  ∏ x ∈ n.divisorsAntidiagonal with μ x.1 = 1, c x.2

/-- The denominator `∏_{ed = n, μ(e) = -1} c_d` of the Möbius factor, in `R`. -/
noncomputable def denProd (c : ℕ → R) (n : ℕ) : R :=
  ∏ x ∈ n.divisorsAntidiagonal with μ x.1 = -1, c x.2

/-- The Möbius factor is the quotient of its numerator and denominator products. -/
theorem moebiusFactorK_eq_div (c : ℕ → R) (n : ℕ) :
    moebiusFactorK (K := K) c n
      = algebraMap R K (numProd c n) / algebraMap R K (denProd c n) := by
  rw [moebiusFactorK, Finset.prod_congr rfl (fun x hx ↦ show (algebraMap R K (c x.2)) ^ (μ x.1)
      = (if μ x.1 = 1 then algebraMap R K (c x.2) else 1)
        * (if μ x.1 = -1 then (algebraMap R K (c x.2))⁻¹ else 1) by
    rcases moebius_eq_or x.1 with h | h | h <;> simp [h]),
    Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter, numProd, denProd,
    map_prod, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]

@[simp] lemma moebiusFactorK_one (c : ℕ → R) :
    moebiusFactorK (K := K) c 1 = algebraMap R K (c 1) := by
  simp [moebiusFactorK]

section IsFractionRing

variable [IsFractionRing R K]

/-- A Möbius factor of a nowhere-zero sequence is nonzero in the fraction field. -/
lemma moebiusFactorK_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) :
    moebiusFactorK (K := K) c n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hx ↦ zpow_ne_zero _
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr
      (ne_zero_of_mem_divisorsAntidiagonal hc hx))

/-- Möbius inversion in the fraction field: `c n = ∏_{d ∣ n} moebiusFactorK c d`. -/
lemma prod_moebiusFactorK {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    algebraMap R K (c n) = ∏ d ∈ n.divisors, moebiusFactorK (K := K) c d :=
  ((ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
      (f := moebiusFactorK (K := K) c) (g := fun k ↦ algebraMap R K (c k))
      (fun n _ ↦ moebiusFactorK_ne_zero hc n)
      (fun k hk ↦ (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr (hc k hk))).mpr
    (fun n _ ↦ by simp [moebiusFactorK]) n hn).symm

/-- `algebraMap a / algebraMap b` is integral iff `b ∣ a` (for `b ≠ 0`). -/
theorem isInteger_div_iff_dvd (a : R) {b : R} (hb : b ≠ 0) :
    IsLocalization.IsInteger R (algebraMap R K a / algebraMap R K b) ↔ b ∣ a := by
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hb
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩, fun ⟨q, hq⟩ ↦ ⟨q, ?_⟩⟩
  · rw [eq_div_iff hbK, ← map_mul] at hr
    exact (FaithfulSMul.algebraMap_injective R K hr).symm.trans (mul_comm r b)
  · rw [hq, map_mul, mul_div_cancel_left₀ _ hbK]

end IsFractionRing

section UniqueFactorizationMonoid

variable [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R] [DecidableEq R]

/-- The valuation gap `v_p(numProd) - v_p(denProd)` is the Möbius transform of `v_p ∘ c`. -/
lemma factorization_numProd_sub_denProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) (p : R) :
    (factorization (numProd c n) p : ℤ) - (factorization (denProd c n) p : ℤ)
      = ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (factorization (c x.2) p : ℤ) := by
  rw [numProd, denProd,
    factorization_prod fun x hx ↦
      ne_zero_of_mem_divisorsAntidiagonal hc (Finset.mem_of_mem_filter x hx),
    factorization_prod fun x hx ↦
      ne_zero_of_mem_divisorsAntidiagonal hc (Finset.mem_of_mem_filter x hx),
    Finsupp.finsetSum_apply, Finsupp.finsetSum_apply, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rcases moebius_eq_or x.1 with h | h | h <;> simp [h]

/-- `v_p ∘ c` is a `gcd`-`min` function when `c` is a strong divisibility sequence. -/
lemma factorization_apply_gcd_eq_min {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (p : R) :
    ∀ x ≥ 1, ∀ y ≥ 1, (factorization (c (x.gcd y)) p)
      = min (factorization (c x) p) (factorization (c y) p) := by
  intro x hx y hy
  rw [factorization_eq_count, ← (hsd x y).normalizedFactors_eq, ← factorization_eq_count,
    factorization_gcd_min (hc x hx) (hc y hy)]

end UniqueFactorizationMonoid

variable [IsDomain R]

lemma numProd_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) : numProd c n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun x hx ↦
    ne_zero_of_mem_divisorsAntidiagonal hc (Finset.mem_of_mem_filter x hx)

lemma denProd_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) : denProd c n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun x hx ↦
    ne_zero_of_mem_divisorsAntidiagonal hc (Finset.mem_of_mem_filter x hx)

/-- The `R`-valued Möbius factor: the (unique, by injectivity) preimage of the fraction-field
factor. Junk value if the factor is not integral. -/
noncomputable def moebiusFactorR (c : ℕ → R) (n : ℕ) : R :=
  Function.invFun (algebraMap R (FractionRing R)) (moebiusFactorK c n)

@[simp] lemma moebiusFactorR_one (c : ℕ → R) : moebiusFactorR c 1 = c 1 := by
  rw [moebiusFactorR, moebiusFactorK_one,
    Function.leftInverse_invFun (FaithfulSMul.algebraMap_injective R (FractionRing R))]

variable [IsFractionRing R K] [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R]

/-- The denominator product of a nowhere-zero strong divisibility sequence divides the numerator
product: prime by prime, `v_p(numProd) - v_p(denProd)` is a nonnegative Möbius transform. -/
theorem denProd_dvd_numProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    denProd c n ∣ numProd c n := by
  classical
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (denProd_ne_zero hc n) (numProd_ne_zero hc n),
    Multiset.le_iff_count]
  intro p
  rw [← factorization_eq_count, ← factorization_eq_count]
  have hge := sum_mul_moebius_nonneg (fun d ↦ factorization (c d) p)
    (factorization_apply_gcd_eq_min hc hsd p) hn
  have heq := factorization_numProd_sub_denProd hc n p
  omega

/-- **Integrality.** For a nowhere-zero strong divisibility sequence `c` in a UFD `R`, the
fraction-field Möbius factor `moebiusFactorK c n` lies in the image of `R`. -/
theorem moebiusFactorK_isInteger {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    IsLocalization.IsInteger R (moebiusFactorK (K := K) c n) := by
  rw [moebiusFactorK_eq_div c]
  exact (isInteger_div_iff_dvd (numProd c n) (denProd_ne_zero hc n)).mpr
    (denProd_dvd_numProd hc hsd hn)

/-- The defining identity of the `R`-valued factor: `β_n · denProd = numProd`. -/
theorem moebiusFactorR_mul_denProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    moebiusFactorR c n * denProd c n = numProd c n := by
  obtain ⟨r, hr⟩ := moebiusFactorK_isInteger (K := FractionRing R) hc hsd hn
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_mul, moebiusFactorR, ← hr,
    Function.leftInverse_invFun (FaithfulSMul.algebraMap_injective R (FractionRing R)) r, hr,
    moebiusFactorK_eq_div c, div_mul_cancel₀ _
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R _)).mpr (denProd_ne_zero hc n))]

/-- **API lemma.** In any fraction field `K` of `R`, the image of `moebiusFactorR c n` is the
Möbius formula (for a nowhere-zero strong divisibility sequence). -/
theorem algebraMap_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    algebraMap R K (moebiusFactorR c n) = moebiusFactorK (K := K) c n := by
  rw [moebiusFactorK_eq_div c, eq_div_iff ((map_ne_zero_iff _
    (FaithfulSMul.algebraMap_injective R K)).mpr (denProd_ne_zero hc n)), ← map_mul,
    moebiusFactorR_mul_denProd hc hsd hn]

theorem moebiusFactorR_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    moebiusFactorR c n ≠ 0 := fun h0 ↦
  numProd_ne_zero hc n (by rw [← moebiusFactorR_mul_denProd hc hsd hn, h0, zero_mul])

/-- Möbius inversion in `R`: `c n = ∏_{d ∣ n} moebiusFactorR c d` for a nowhere-zero strong
divisibility sequence. -/
theorem prod_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) :
    c n = ∏ d ∈ n.divisors, moebiusFactorR c d := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_prod, Finset.prod_congr rfl fun d hd ↦
      algebraMap_moebiusFactorR hc hsd (Nat.pos_of_mem_divisors hd),
    prod_moebiusFactorK hc hn]

variable [DecidableEq R]

/-- `v_p(β_n)` is the Möbius transform of `v_p ∘ c`. -/
theorem factorization_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) {n : ℕ} (hn : 1 ≤ n) (p : R) :
    (factorization (moebiusFactorR c n) p : ℤ)
      = ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (factorization (c x.2) p : ℤ) := by
  have hkey : factorization (moebiusFactorR c n) p + factorization (denProd c n) p
      = factorization (numProd c n) p := by
    rw [← Finsupp.add_apply, ← factorization_mul (moebiusFactorR_ne_zero hc hsd hn)
      (denProd_ne_zero hc n), moebiusFactorR_mul_denProd hc hsd hn]
  have := factorization_numProd_sub_denProd hc n p
  omega

/-- If `v_p ∘ c` has the constant-valuation shape (value `E` exactly on the multiples of `m`),
then `v_p(β_n)` is supported at the single index `n = m`. -/
theorem factorization_moebiusFactorR_shape {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (p : R) {m E : ℕ} (hm : 1 ≤ m)
    (hshape : ∀ k ≥ 1, factorization (c k) p = if m ∣ k then E else 0) {n : ℕ} (hn : 1 ≤ n) :
    factorization (moebiusFactorR c n) p = if n = m then E else 0 := by
  have hmain : (factorization (moebiusFactorR c n) p : ℤ) = if n = m then (E : ℤ) else 0 := by
    rw [factorization_moebiusFactorR hc hsd hn p, Finset.sum_congr rfl fun x hx ↦
        congrArg (μ x.1 * ·) (by rw [hshape x.2 (Nat.pos_of_mem_divisors
          (Nat.snd_mem_divisors_of_mem_antidiagonal hx)), Nat.cast_ite, Nat.cast_zero]),
      Finset.sum_mul_ite_const n.divisorsAntidiagonal,
      sum_divisorsAntidiagonal_filter_dvd_moebius hm hn]
    split_ifs <;> simp
  exact_mod_cast hmain

/-- **Pairwise relative primality of the Möbius factors** of a strong divisibility sequence with
the constant-valuation property: distinct factors share no prime. -/
theorem moebiusFactorR_isRelPrime {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n)))
    (hshape : ∀ p : R, Prime p → normalize p = p →
      ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1, factorization (c k) p = if m ∣ k then E else 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    IsRelPrime (moebiusFactorR c m) (moebiusFactorR c n) := by
  intro d hdm hdn
  by_contra hdu
  have hd0 : d ≠ 0 := fun h ↦ moebiusFactorR_ne_zero hc hsd hm (zero_dvd_iff.mp (h ▸ hdm))
  obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hd0 hdu
  have hpp : Prime p := prime_of_normalized_factor p hp
  have hpn : normalize p = p := normalize_normalized_factor p hp
  obtain ⟨M, hM1, E, hE⟩ := hshape p hpp hpn
  have hcount (k : ℕ) (hk : 1 ≤ k) (hdvd : d ∣ moebiusFactorR c k) :
      1 ≤ factorization (moebiusFactorR c k) p :=
    (one_le_factorization_iff_dvd hpp hpn (moebiusFactorR_ne_zero hc hsd hk)).mpr
      ((dvd_of_mem_normalizedFactors hp).trans hdvd)
  have hm' := hcount m hm hdm
  have hn' := hcount n hn hdn
  rw [factorization_moebiusFactorR_shape hc hsd p hM1 hE hm] at hm'
  rw [factorization_moebiusFactorR_shape hc hsd p hM1 hE hn] at hn'
  split_ifs at hm' hn' with e1 e2
  · exact hmn (e1.trans e2.symm)
  all_goals lia
