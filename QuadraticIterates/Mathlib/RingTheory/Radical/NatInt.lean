module

public import Mathlib.RingTheory.Radical.NatInt

/-!
# The radical of a natural number

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

open UniqueFactorizationMonoid

/-- If `n ≠ 0` is not squarefree, then `n / rad n ≥ 2`. -/
theorem Nat.two_le_div_radical_of_not_squarefree {n : ℕ} (hn : n ≠ 0) (h : ¬Squarefree n) :
    2 ≤ n / radical n := by
  by_contra! hlt
  have h1 : n / radical n = 1 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      radical_dvd_self) (Nat.radical_pos n)
    lia
  refine h ?_
  rw [← Nat.div_mul_cancel (radical_dvd_self (a := n)), h1, one_mul]
  exact squarefree_radical

theorem Nat.radical_eq_self_of_squarefree {n : ℕ} (hsf : Squarefree n) : radical n = n :=
  Nat.dvd_antisymm radical_dvd_self (hsf.isRadical.dvd_radical hsf.ne_zero)
