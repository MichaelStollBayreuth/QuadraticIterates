module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

import QuadraticIterates.Mathlib.Algebra.GCDMonoid.Basic
import QuadraticIterates.Mathlib.Data.Multiset

/-!
# Unique factorization lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open UniqueFactorizationMonoid

/-- If `σ` is a multiplicative automorphism of a normalization UFD and `σ p` is associated to
`p`, then `normalize ∘ σ` permutes the multiset of normalized factors of `p`. -/
lemma normalizedFactors_map_mulEquiv_eq {α : Type*} [CommMonoidWithZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α] (σ : α ≃* α) {p : α} (hp0 : p ≠ 0)
    (hassoc : Associated (σ p) p) :
    (normalizedFactors p).map (fun q ↦ normalize (σ q)) = normalizedFactors p := by
  have hirr : ∀ q ∈ (normalizedFactors p).map σ, Irreducible q :=
    Multiset.forall_mem_map_iff.mpr fun q hq ↦
      (MulEquiv.irreducible_iff σ).mpr (irreducible_of_normalized_factor q hq)
  have hprod : Associated ((normalizedFactors p).map σ).prod p := by
    rw [← map_multiset_prod]
    exact ((prod_normalizedFactors hp0).map σ.toMonoidHom).trans hassoc
  calc (normalizedFactors p).map (fun q ↦ normalize (σ q))
      = ((normalizedFactors p).map σ).map normalize := (Multiset.map_map normalize σ _).symm
    _ = normalizedFactors ((normalizedFactors p).map σ).prod :=
        (normalizedFactors_prod_eq _ hirr).symm
    _ = normalizedFactors p := hprod.normalizedFactors_eq

/-- If `σ` is an involutive multiplicative automorphism of a normalization UFD, `σ p` is
associated to `p`, `p` is not irreducible, and every divisor of `p` that is `σ`-invariant up to
associates is trivial, then the normalized factors of `p` pair up under `normalize ∘ σ`. -/
theorem exists_normalizedFactors_eq_add_map {α : Type*} [CommMonoidWithZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α] {σ : α ≃* α} (hσ : Function.Involutive σ)
    {p : α} (hp0 : p ≠ 0) (hσp : Associated (σ p) p) (hp : ¬Irreducible p)
    (h : ∀ d, d ∣ p → Associated (σ d) d → IsUnit d ∨ Associated d p) :
    ∃ N : Multiset α, normalizedFactors p = N + N.map fun q ↦ normalize (σ q) := by
  refine Multiset.exists_add_map_of_involutive (fun q ↦ normalize (σ q)) _ (fun q hq ↦ ?_)
    (normalizedFactors_map_mulEquiv_eq σ hp0 hσp) fun q hq hfix ↦ ?_
  · rw [normalize_map_normalize, hσ q, normalize_normalized_factor q hq]
  · have hirr := irreducible_of_normalized_factor q hq
    have hσq : Associated (σ q) q := (normalize_associated (σ q)).symm.trans (by rw [hfix])
    rcases h q (dvd_of_mem_normalizedFactors hq) hσq with hu | hap
    · exact hirr.not_isUnit hu
    · exact hp (hap.irreducible hirr)

section Factorization

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R]

/-- The multiplicity of a normalized prime `p` in `x ≠ 0`, as an `emultiplicity`. -/
lemma emultiplicity_eq_factorization {p x : R} (hp : Prime p) (hpn : normalize p = p)
    (hx : x ≠ 0) : emultiplicity p x = factorization x p := by
  rw [factorization_eq_count, emultiplicity_eq_count_normalizedFactors hp.irreducible hx, hpn]

/-- `p ^ k ∣ x` iff `k` is at most the multiplicity of a normalized prime `p` in `x ≠ 0`. -/
lemma _root_.Associated.factorization_eq {a b : R} (h : Associated a b) :
    factorization a = factorization b :=
  congrArg Multiset.toFinsupp h.normalizedFactors_eq

lemma pow_dvd_iff_le_factorization {p x : R} (hp : Prime p) (hpn : normalize p = p) (hx : x ≠ 0)
    {k : ℕ} : p ^ k ∣ x ↔ k ≤ factorization x p := by
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_factorization hp hpn hx, Nat.cast_le]

/-- A normalized prime `p` divides `x ≠ 0` iff its multiplicity in `x` is positive. -/
lemma one_le_factorization_iff_dvd {p x : R} (hp : Prime p) (hpn : normalize p = p) (hx : x ≠ 0) :
    1 ≤ factorization x p ↔ p ∣ x := by
  simpa using (pow_dvd_iff_le_factorization hp hpn hx (k := 1)).symm

/-- The multiplicity of a normalized prime `p` in `x ≠ 0` vanishes iff `p ∤ x`. -/
lemma factorization_eq_zero_iff_not_dvd {p x : R} (hp : Prime p) (hpn : normalize p = p)
    (hx : x ≠ 0) : factorization x p = 0 ↔ ¬p ∣ x := by
  rw [← one_le_factorization_iff_dvd hp hpn hx]
  lia

/-- The factorization of a product of nonzero elements is the sum of the factorizations. -/
lemma factorization_prod {ι : Type*} {s : Finset ι} {f : ι → R} (hf : ∀ i ∈ s, f i ≠ 0) :
    factorization (∏ i ∈ s, f i) = ∑ i ∈ s, factorization (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have := nontrivial_of_ne _ _ (hf a (Finset.mem_insert_self a s))
    rw [Finset.prod_insert ha, factorization_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      Finset.sum_insert ha, ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

end Factorization

section GCD

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    [NormalizedGCDMonoid R] [DecidableEq R]

/-- The normalized factors of a gcd form the intersection of the normalized factors: the gcd is
the meet in the divisibility lattice, which `normalizedFactors` embeds into the multisets. -/
theorem UniqueFactorizationMonoid.normalizedFactors_gcd (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedFactors (gcd a b) = normalizedFactors a ⊓ normalizedFactors b := by
  have := nontrivial_of_ne a 0 ha
  have hg : gcd a b ≠ 0 := gcd_ne_zero_of_left ha
  refine le_antisymm (le_inf
    ((dvd_iff_normalizedFactors_le_normalizedFactors hg ha).mp (gcd_dvd_left a b))
    ((dvd_iff_normalizedFactors_le_normalizedFactors hg hb).mp (gcd_dvd_right a b))) ?_
  set s := normalizedFactors a ⊓ normalizedFactors b
  have hmem (q : R) (hq : q ∈ s) : q ∈ normalizedFactors a := Multiset.mem_of_le inf_le_left hq
  have hirr (q : R) (hq : q ∈ s) : Irreducible q := irreducible_of_normalized_factor q (hmem q hq)
  have hs0 : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 ↦ (hirr 0 h0).ne_zero rfl
  have hfac : normalizedFactors s.prod = s := (normalizedFactors_prod_eq s hirr).trans
    ((Multiset.map_congr rfl fun q hq ↦ normalize_normalized_factor q (hmem q hq)).trans
      (Multiset.map_id' s))
  have hdvd (x : R) (hx : x ≠ 0) (hle : s ≤ normalizedFactors x) : s.prod ∣ x :=
    (dvd_iff_normalizedFactors_le_normalizedFactors hs0 hx).mpr (by rwa [hfac])
  rw [← hfac]
  exact (dvd_iff_normalizedFactors_le_normalizedFactors hs0 hg).mp
    (dvd_gcd (hdvd a ha inf_le_left) (hdvd b hb inf_le_right))

/-- The `p`-multiplicity of a gcd is the minimum of the multiplicities. -/
theorem factorization_gcd_min (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (p : R) :
    factorization (gcd a b) p = min (factorization a p) (factorization b p) := by
  simp only [factorization_eq_count, normalizedFactors_gcd a b ha hb, Multiset.inf_eq_inter,
    Multiset.count_inter]

end GCD

section PeriodicShape

variable {S : Type*} [CommRing S] [UniqueFactorizationMonoid S]
    [NormalizationMonoid S] [DecidableEq S]

/-- The multiplicity at `p` is determined by the residue mod `p ^ (E+1)`: if `v_p y = E` and
`p ^ (E+1) ∣ x - y`, then `v_p x = E`. -/
theorem factorization_eq_of_dvd_sub {p : S} (hp : Prime p) (hpn : normalize p = p)
    {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) {E : ℕ} (hyE : factorization y p = E)
    (hcong : p ^ (E + 1) ∣ x - y) : factorization x p = E := by
  have h := emultiplicity_add_of_gt (p := p) (a := x - y) (b := y) (by
    rw [emultiplicity_eq_factorization hp hpn hy, hyE]
    exact lt_of_lt_of_le (mod_cast E.lt_succ_self) (pow_dvd_iff_le_emultiplicity.mp hcong))
  rw [sub_add_cancel, emultiplicity_eq_factorization hp hpn hx,
    emultiplicity_eq_factorization hp hpn hy, hyE] at h
  exact_mod_cast h

/-- If a sequence `x` in a UFD is nonzero on `[1,∞)`, first `p`-divisible at index `m ≥ 2` with
`p ∤ x (m+1)`, and periodic modulo `p ^ (E+1)` with period `m` from index `2` on (where
`E = v_p (x m)`), then `v_p (x n) = E` when `m ∣ n` and `0` otherwise. -/
theorem factorization_periodic_shape {p : S} (hp : Prime p) (hpn : normalize p = p)
    {x : ℕ → S} {m E : ℕ} (hm : 2 ≤ m) (hne : ∀ n ≥ 1, x n ≠ 0)
    (hE : factorization (x m) p = E) (hmin : ∀ k < m, 1 ≤ k → ¬ p ∣ x k)
    (hpm1 : ¬ p ∣ x (m + 1)) (hper : ∀ n ≥ 2, p ^ (E + 1) ∣ x (n + m) - x n) :
    ∀ n ≥ 1, factorization (x n) p = if m ∣ n then E else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n (m + 2) with hsmall | hbig
  · rcases eq_or_ne n m with rfl | hnm
    · simp [hE]
    have hmn : ¬ m ∣ n := fun h ↦ by
      have := Nat.le_of_dvd hn h
      obtain rfl : n = m + 1 := by lia
      exact Nat.not_dvd_of_pos_of_lt one_pos hm (Nat.dvd_add_self_left.mp h)
    rw [if_neg hmn, factorization_eq_zero_iff_not_dvd hp hpn (hne n hn)]
    rcases Nat.lt_or_ge n m with hlt | hge
    · exact hmin n hlt hn
    · exact (show n = m + 1 by lia) ▸ hpm1
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by lia⟩
    have hk : 1 ≤ k := by lia
    simp only [Nat.dvd_add_self_right]
    exact factorization_eq_of_dvd_sub hp hpn (hne _ hn) (hne k hk) (ih k (by lia) hk)
      ((pow_dvd_pow p (by split_ifs <;> lia)).trans (hper k (by lia)))

end PeriodicShape
