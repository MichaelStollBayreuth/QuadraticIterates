module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Polynomial.Expand

import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Polynomial.FieldDivision
import QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Even polynomials as polynomials in `X² + c`

An even polynomial (one fixed by `X ↦ -X`) over a domain of characteristic `≠ 2` is a polynomial
in `X² + c`. Consequently, for an irreducible `F` over a field of characteristic `≠ 2`, every even
divisor of `F ∘ (X² + c)` is trivial. A monic even polynomial over a field that is reducible but
has no nontrivial even divisor is, up to sign, of the form `g · g(-X)`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- `expand R p` inverts `contract p` on the polynomials whose coefficients vanish away from the
multiples of `p`. -/
theorem expand_contract_of_forall_coeff_eq_zero {R : Type*} [CommSemiring R] {p : ℕ} (hp : p ≠ 0)
    {f : R[X]} (hf : ∀ n, ¬ p ∣ n → f.coeff n = 0) : expand R p (contract p f) = f := by
  ext n
  rw [coeff_expand hp.bot_lt, coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · exact (hf n h).symm

variable {R : Type*} [CommRing R]

/-- `X² + c` is fixed by `X ↦ -X`. -/
@[simp] lemma X_sq_add_C_comp_neg_X (c : R) : (X ^ 2 + C c).comp (-X) = X ^ 2 + C c := by
  simp only [add_comp, pow_comp, X_comp, C_comp]
  ring

/-- `X ↦ -X` preserves the degree. -/
@[simp] theorem natDegree_comp_neg_X (p : R[X]) : (p.comp (-X)).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq degree_comp_neg_X

/-- Over a domain, a polynomial whose reflection is merely *associated* to it is fixed by
`X ↦ -X` up to a sign. -/
theorem comp_neg_X_eq_or_eq_neg_of_associated [IsDomain R] {p : R[X]} (hp : p ≠ 0)
    (h : Associated (p.comp (-X)) p) : p.comp (-X) = p ∨ p.comp (-X) = -p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hcu⟩ := isUnit_iff.mp u.isUnit
  rw [← hcu] at hu
  have h2 : p * C c = p.comp (-X) := by
    simpa only [mul_comp, comp_neg_X_comp_neg_X, C_comp] using congrArg (·.comp (-X)) hu
  have hcsq : c * c = 1 := by
    have : p * C (c * c) = p * 1 := by rw [mul_one, C_mul, ← mul_assoc, h2, hu]
    exact C_inj.mp ((mul_left_cancel₀ hp this).trans C_1.symm)
  rcases mul_self_eq_one_iff.mp hcsq with rfl | rfl
  · exact .inl (by simpa using hu)
  · exact .inr (neg_eq_iff_eq_neg.mp (by simpa using hu))

/-- A polynomial in `X²` is fixed by `X ↦ -X`. -/
@[simp] theorem expand_two_comp_neg_X (h : R[X]) : (expand R 2 h).comp (-X) = expand R 2 h := by
  simp [expand_eq_comp_X_pow, comp_assoc]

section NeZero

variable [NoZeroDivisors R] [NeZero (2 : R)] {b : R[X]}

/-- Over a domain of characteristic `≠ 2`, the odd coefficients of a polynomial fixed by
`X ↦ -X` vanish. -/
theorem coeff_eq_zero_of_comp_neg_X_eq_of_not_two_dvd (hb : b.comp (-X) = b) {n : ℕ}
    (hn : ¬ 2 ∣ n) : b.coeff n = 0 := by
  have hcoeff : (b.comp (-X)).coeff n = b.coeff n * (-1) ^ n := by
    simpa using comp_C_mul_X_coeff (p := b) (r := -1) (n := n)
  rw [hb, Odd.neg_one_pow (Nat.odd_iff.mpr (by lia))] at hcoeff
  exact (mul_eq_zero.mp (by linear_combination hcoeff : (2 : R) * b.coeff n = 0)).resolve_left
    two_ne_zero

/-- Over a domain of characteristic `≠ 2`, a polynomial fixed by `X ↦ -X` is a polynomial
in `X²`. -/
theorem eq_expand_two_contract_of_comp_neg_X (hb : b.comp (-X) = b) :
    b = expand R 2 (contract 2 b) :=
  (expand_contract_of_forall_coeff_eq_zero two_ne_zero fun _ ↦
    coeff_eq_zero_of_comp_neg_X_eq_of_not_two_dvd hb).symm

/-- An even polynomial over a domain of characteristic `≠ 2` is a polynomial in `X² + c`. -/
theorem even_eq_comp_X_sq_add_C (c : R) {b : R[X]} (hb : b.comp (-X) = b) :
    ∃ e : R[X], b = e.comp (X ^ 2 + C c) :=
  ⟨(contract 2 b).comp (X - C c), by
    rw [comp_assoc, show (X - C c : R[X]).comp (X ^ 2 + C c) = X ^ 2 by simp,
      ← expand_eq_comp_X_pow, ← eq_expand_two_contract_of_comp_neg_X hb]⟩

end NeZero

section Field

variable {K : Type*} [Field K]

private theorem Monic.eq_C_neg_one_pow_mul_of_associated {g p : K[X]} (hg : g.Monic) (hp : p.Monic)
    (h : Associated p (g * g.comp (-X))) : p = C ((-1) ^ g.natDegree) * (g * g.comp (-X)) := by
  refine eq_of_monic_of_associated hp ?_ (h.trans (associated_unit_mul_left _ _
    (isUnit_C.mpr (isUnit_one.neg.pow _))).symm)
  simpa [mul_left_comm] using hg.mul hg.neg_one_pow_natDegree_mul_comp_neg_X

-- The pairing of the irreducible factors of an even polynomial without nontrivial even divisors
-- under `X ↦ -X`, as an instance of `exists_normalizedFactors_eq_add_map`.
private theorem exists_normalizedFactors_eq_add_map_normalize_comp_neg_X [DecidableEq K]
    {p : K[X]} (hp0 : p ≠ 0) (heven : p.comp (-X) = p) (hirr : ¬Irreducible p)
    (h : ∀ d : K[X], d ∣ p → Associated (d.comp (-X)) d → IsUnit d ∨ Associated d p) :
    ∃ N : Multiset K[X], UniqueFactorizationMonoid.normalizedFactors p =
      N + N.map fun q ↦ normalize (q.comp (-X)) := by
  set σ : K[X] ≃* K[X] := (algEquivAevalNegX (R := K)).toMulEquiv
  have hσ (q : K[X]) : σ q = q.comp (-X) := comp_eq_aeval.symm
  simpa only [hσ] using exists_normalizedFactors_eq_add_map σ
    (fun q ↦ by rw [hσ, hσ, comp_neg_X_comp_neg_X]) hp0 (by rw [hσ, heven]; exact .refl p) hirr
    (by simpa only [hσ] using h)

/-- A reducible monic even polynomial with no nontrivial even divisors factors as
`g · g(-X) = (-1)^{deg g} · p` with `2 deg g = deg p`: its irreducible factors pair up under
`X ↦ -X`. -/
theorem Monic.exists_mul_comp_neg_X_eq_of_not_irreducible {p : K[X]} (hp : p.Monic)
    (heven : p.comp (-X) = p) (hirr : ¬Irreducible p)
    (h : ∀ d : K[X], d ∣ p → Associated (d.comp (-X)) d → IsUnit d ∨ Associated d p) :
    ∃ g : K[X], 2 * g.natDegree = p.natDegree ∧ g * g.comp (-X) = C ((-1) ^ g.natDegree) * p := by
  classical
  obtain ⟨N, hN⟩ :=
    exists_normalizedFactors_eq_add_map_normalize_comp_neg_X hp.ne_zero heven hirr h
  have hg : N.prod.Monic := by
    simpa using monic_multiset_prod_of_monic N id fun q hq ↦
      ((Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp
        (hN ▸ Multiset.mem_add.mpr (.inl hq))).2.1
  have hτ : (N.map fun q ↦ normalize (q.comp (-X))).prod = normalize (N.prod.comp (-X)) := by
    rw [multiset_prod_comp, ← coe_normalizeHom, map_multiset_prod normalizeHom, Multiset.map_map,
      Function.comp_def]
  have hassoc : Associated p (N.prod * N.prod.comp (-X)) := by
    have h1 := UniqueFactorizationMonoid.prod_normalizedFactors hp.ne_zero
    rw [hN, Multiset.prod_add, hτ] at h1
    exact h1.symm.trans (Associated.mul_left _ (normalize_associated _))
  have hpw := hg.eq_C_neg_one_pow_mul_of_associated hp hassoc
  refine ⟨N.prod, ?_, ?_⟩
  · rw [hpw, natDegree_C_mul (isUnit_one.neg.pow _).ne_zero, Polynomial.natDegree_mul hg.ne_zero
      (comp_neg_X_eq_zero_iff.not.mpr hg.ne_zero), natDegree_comp_neg_X, two_mul]
  · simp [hpw, ← mul_assoc, ← mul_pow]

/-- For irreducible `F`, every even divisor (`d(-X) = d`) of `F ∘ (X² + c)` is trivial — a unit
or associated to `F ∘ (X² + c)` — since it is `e ∘ (X² + c)` for a divisor `e` of `F`. -/
theorem _root_.Irreducible.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq [NeZero (2 : K)]
    {F : K[X]} (hF : Irreducible F) {c : K} {d : K[X]}
    (hd : d ∣ F.comp (X ^ 2 + C c)) (heven : d.comp (-X) = d) :
    IsUnit d ∨ Associated d (F.comp (X ^ 2 + C c)) := by
  obtain ⟨e, rfl⟩ := even_eq_comp_X_sq_add_C c heven
  rw [comp_dvd_comp_iff (by simp), hF.dvd_iff] at hd
  exact hd.imp (·.map (compRingHom (X ^ 2 + C c))) (·.symm.map (compRingHom (X ^ 2 + C c)))

/-- Variant of `Irreducible.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq` for divisors that
are even only up to associates: if `F` is irreducible and `F(c) ≠ 0`, then any divisor `d` of
`F ∘ (X² + c)` with `d(-X)` associated to `d` is a unit or associated to `F ∘ (X² + c)`. (Without
`F(c) ≠ 0` the odd divisor `X` of `F ∘ (X² + c)` would be a counterexample.) -/
theorem _root_.Irreducible.isUnit_or_associated_of_dvd_comp_of_associated_comp_neg_X
    [NeZero (2 : K)] {F : K[X]} (hF : Irreducible F) {c : K} (hc : F.eval c ≠ 0)
    {d : K[X]} (hd : d ∣ F.comp (X ^ 2 + C c)) (hassoc : Associated (d.comp (-X)) d) :
    IsUnit d ∨ Associated d (F.comp (X ^ 2 + C c)) := by
  have h0 : (F.comp (X ^ 2 + C c)).eval 0 ≠ 0 := by simpa using hc
  rcases comp_neg_X_eq_or_eq_neg_of_associated
    (ne_zero_of_dvd_ne_zero (fun h ↦ h0 (by simp [h])) hd) hassoc with heven | hodd
  · exact hF.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq hd heven
  · have hd0 : d.eval 0 = 0 := by
      have h1 : d.eval 0 = -d.eval 0 := by simpa using congrArg (eval 0) hodd
      grind [two_ne_zero]
    have h2 := eval_dvd (x := (0 : K)) hd
    rw [hd0, zero_dvd_iff] at h2
    exact absurd h2 h0

end Field

end Polynomial
