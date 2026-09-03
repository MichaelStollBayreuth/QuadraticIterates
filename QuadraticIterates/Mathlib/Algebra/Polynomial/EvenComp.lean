module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Polynomial.Expand

import Mathlib.Tactic.LinearCombination
import QuadraticIterates.Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Even polynomials as polynomials in `X² + c`

An even polynomial (one fixed by `X ↦ -X`) over a domain of characteristic `≠ 2` is a polynomial
in `X² + c`. Consequently, for an irreducible `F` over a field of characteristic `≠ 2`, every even
divisor of `F ∘ (X² + c)` is trivial.

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

/-- `X ↦ -X` preserves being associated. -/
lemma _root_.Associated.comp_neg_X {p q : R[X]} (h : Associated p q) :
    Associated (p.comp (-X)) (q.comp (-X)) :=
  h.map (algEquivAevalNegX (R := R)).toMulEquiv.toMonoidHom

/-- Normalizing before reflecting does not change the normalized reflection. -/
lemma normalize_normalize_comp_neg_X [IsDomain R] [NormalizationMonoid R[X]] (p : R[X]) :
    normalize ((normalize p).comp (-X)) = normalize (p.comp (-X)) :=
  have h := (normalize_associated p).comp_neg_X
  normalize_eq_normalize h.dvd h.symm.dvd

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
theorem even_eq_comp_X_sq_add_C (c : R) (b : R[X]) (hb : b.comp (-X) = b) :
    ∃ e : R[X], b = e.comp (X ^ 2 + C c) :=
  ⟨(contract 2 b).comp (X - C c), by
    rw [comp_assoc, show (X - C c : R[X]).comp (X ^ 2 + C c) = X ^ 2 by simp,
      ← expand_eq_comp_X_pow, ← eq_expand_two_contract_of_comp_neg_X hb]⟩

/-- For irreducible `F`, every even divisor (`d(-X) = d`) of `F ∘ (X² + c)` is trivial — a unit
or associated to `F ∘ (X² + c)` — since it is `e ∘ (X² + c)` for a divisor `e` of `F`. -/
theorem _root_.Irreducible.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq {K : Type*} [Field K]
    [NeZero (2 : K)] {F : K[X]} (hF : Irreducible F) {c : K} {d : K[X]}
    (hd : d ∣ F.comp (X ^ 2 + C c)) (heven : d.comp (-X) = d) :
    IsUnit d ∨ Associated d (F.comp (X ^ 2 + C c)) := by
  obtain ⟨e, rfl⟩ := even_eq_comp_X_sq_add_C c d heven
  rw [comp_dvd_comp_iff (by rw [natDegree_X_pow_add_C]; exact two_pos), hF.dvd_iff] at hd
  exact hd.imp (fun hu ↦ by simpa only [comp_eq_aeval] using hu.map (aeval (X ^ 2 + C c)))
    fun h ↦ by simpa only [comp_eq_aeval] using h.symm.map (aeval (X ^ 2 + C c))

/-- Variant of `Irreducible.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq` for divisors that
are even only up to associates: if `F` is irreducible and `F(c) ≠ 0`, then any divisor `d` of
`F ∘ (X² + c)` with `d(-X)` associated to `d` is a unit or associated to `F ∘ (X² + c)`. (Without
`F(c) ≠ 0` the odd divisor `X` of `F ∘ (X² + c)` would be a counterexample.) -/
theorem _root_.Irreducible.isUnit_or_associated_of_dvd_comp_of_associated_comp_neg_X {K : Type*}
    [Field K] [NeZero (2 : K)] {F : K[X]} (hF : Irreducible F) {c : K} (hc : F.eval c ≠ 0)
    {d : K[X]} (hd : d ∣ F.comp (X ^ 2 + C c)) (hassoc : Associated (d.comp (-X)) d) :
    IsUnit d ∨ Associated d (F.comp (X ^ 2 + C c)) := by
  have h0 : (F.comp (X ^ 2 + C c)).eval 0 ≠ 0 := by simpa using hc
  rcases comp_neg_X_eq_or_eq_neg_of_associated
    (ne_zero_of_dvd_ne_zero (fun h ↦ h0 (by simp [h])) hd) hassoc with heven | hodd
  · exact hF.isUnit_or_associated_of_dvd_comp_of_comp_neg_X_eq hd heven
  · have hd0 : d.eval 0 = 0 := by
      have h1 : d.eval 0 = -d.eval 0 := by simpa using congrArg (eval 0) hodd
      exact (mul_eq_zero.mp (by linear_combination h1 : (2 : K) * d.eval 0 = 0)).resolve_left
        two_ne_zero
    have h2 := eval_dvd (x := (0 : K)) hd
    rw [hd0, zero_dvd_iff] at h2
    exact (h0 h2).elim

end NeZero

end Polynomial
