module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

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

section Factorization

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R]

/-- The multiplicity of a normalized prime `p` in `x ≠ 0`, as an `emultiplicity`. -/
lemma emultiplicity_eq_factorization {p x : R} (hp : Prime p) (hpn : normalize p = p)
    (hx : x ≠ 0) : emultiplicity p x = factorization x p := by
  rw [factorization_eq_count, emultiplicity_eq_count_normalizedFactors hp.irreducible hx, hpn]

/-- `p ^ k ∣ x` iff `k` is at most the multiplicity of a normalized prime `p` in `x ≠ 0`. -/
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

end Factorization

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
