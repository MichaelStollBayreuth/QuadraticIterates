module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Auxiliary results on p-adic valuations

Valuations of negatives, products and gcds, the UFD `factorization` over `ℤ`, and integrality
via valuations (`padicValRat p q < 0 ↔ p ∣ q.den`). No longer used by the project itself — the
corresponding steps now run through the UFD `factorization` API — but kept as self-contained
upstreaming candidates.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

@[simp]
protected theorem padicValInt.neg {p : ℕ} (a : ℤ) : padicValInt p (-a) = padicValInt p a := by
  simp [padicValInt]

/-- Over `ℤ`, the number of normalized factors equal to a prime `p` is the `p`-adic valuation. -/
theorem Int.factorization_eq_padicValInt (p : ℕ) [Fact p.Prime] {x : ℤ} (hx : x ≠ 0) :
    factorization x (p : ℤ) = padicValInt p x := by
  have h : (factorization x (p : ℤ) : ℕ∞) = emultiplicity (p : ℤ) x := by
    rw [factorization_eq_count, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Nat.prime_iff_prime_int.mp Fact.out).irreducible hx, Int.normalize_of_nonneg p.cast_nonneg]
  exact_mod_cast h.trans ((Int.emultiplicity_natAbs p x).symm.trans
    (padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hx)).symm)

/-- The `p`-adic valuation of a `gcd` is the minimum of the valuations. -/
theorem padicValNat_gcd (p : ℕ) [Fact p.Prime] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  simp only [← Nat.factorization_def _ (Fact.out : p.Prime), Nat.factorization_gcd ha hb,
    Finsupp.inf_apply]

namespace padicValRat

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `p`-adic valuation is additive over a finite product of nonzero rationals. -/
protected theorem prod {ι : Type*} {s : Finset ι} {f : ι → ℚ} (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValRat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValRat p (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2), ih hf.2]

/-- The `p`-adic valuation of a rational is negative iff `p` divides its denominator. -/
theorem lt_zero_iff_dvd_den {q : ℚ} : padicValRat p q < 0 ↔ p ∣ q.den := by
  rw [padicValRat_def]
  refine ⟨fun h ↦ by_contra fun hpd ↦ ?_, fun h ↦ ?_⟩
  · rw [padicValNat.eq_zero_of_not_dvd hpd] at h
    lia
  · have hnum : ¬ (p : ℤ) ∣ q.num := fun hpn ↦ hp.out.one_lt.ne' <|
      (Nat.Coprime.coprime_dvd_left (by simpa using Int.natAbs_dvd_natAbs.mpr hpn)
        q.reduced).eq_one_of_dvd h
    have := one_le_padicValNat_of_dvd q.pos.ne' h
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    lia

end padicValRat

/-- A rational whose `p`-adic valuation is nonnegative at every prime is an integer (`den = 1`). -/
theorem Rat.den_eq_one_of_padicValRat_nonneg {q : ℚ}
    (h : ∀ (p : ℕ) [Fact p.Prime], 0 ≤ padicValRat p q) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := q.den.exists_prime_and_dvd hden
  have : Fact p.Prime := ⟨hp⟩
  exact (padicValRat.lt_zero_iff_dvd_den.mpr hpd).not_ge (h p)
