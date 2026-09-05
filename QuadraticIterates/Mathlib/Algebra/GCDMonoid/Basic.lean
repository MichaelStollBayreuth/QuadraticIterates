module

public import Mathlib.Algebra.GCDMonoid.Basic

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Normalization under homomorphisms; strong divisibility from a translation congruence

Normalizing before applying a monoid homomorphism does not change the normalized image
(`normalize_map_normalize`).

A sequence `a` in a GCD domain with `a 0 = 0` satisfying the *translation congruence*
`a m ∣ a (m + j) - a j` for all `m, j` is a strong divisibility sequence:
`gcd (a m) (a n) = normalize (a (gcd m n))`. This is the arithmetic engine behind the
Fibonacci-style `Int.gcd_fib`, isolated from the specific recurrence.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Normalizing before applying a monoid homomorphism does not change the normalized image. -/
theorem normalize_map_normalize {α : Type*} [MonoidWithZero α] [NormalizationMonoid α]
    [IsLeftCancelMulZero α] {F : Type*} [FunLike F α α] [MonoidHomClass F α α] (f : F) (x : α) :
    normalize (f (normalize x)) = normalize (f x) :=
  normalize_eq_normalize_iff_associated.mpr ((normalize_associated x).map f)

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]

/- TODO:
add lemmas `gcd a (b + a * c) = gcd a b` and variants at the correct level of generality. -/
private theorem gcd_add_self_right_of_dvd_sub {a : ℕ → R} (hdvd : ∀ m j, a m ∣ a (m + j) - a j)
    (m n : ℕ) : gcd (a m) (a (n + m)) = gcd (a m) (a n) := by
  obtain ⟨t, ht⟩ := hdvd m n
  rw [add_comm, sub_eq_iff_eq_add'] at ht
  rw [ht]
  refine dvd_antisymm_of_normalize_eq (normalize_gcd ..) (normalize_gcd ..)
    (dvd_gcd (gcd_dvd_left ..) ?_) (dvd_gcd (gcd_dvd_left ..) ?_)
  · simpa using dvd_sub (gcd_dvd_right (a m) (a n + a m * t))
      ((gcd_dvd_left (a m) (a n + a m * t)).mul_right t)
  · exact dvd_add (gcd_dvd_right ..) ((gcd_dvd_left ..).mul_right t)

private theorem gcd_add_mul_self_right_of_dvd_sub {a : ℕ → R}
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    ∀ k, gcd (a m) (a (n + k * m)) = gcd (a m) (a n)
  | 0 => by simp
  | k + 1 => by
    rw [← gcd_add_mul_self_right_of_dvd_sub hdvd m n k, add_mul, ← add_assoc, one_mul,
      gcd_add_self_right_of_dvd_sub hdvd]

/-- If `a 0 = 0` and `a m ∣ a (m + j) - a j` for all `m, j` (the *translation congruence*), then
`a` is a strong divisibility sequence: `gcd (a m) (a n) = normalize (a (gcd m n))`. -/
theorem gcd_eq_normalize_of_dvd_sub {a : ℕ → R} (h0 : a 0 = 0)
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    gcd (a m) (a n) = normalize (a (m.gcd n)) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp [h0]
  | H1 m n _ ih =>
    rw [Nat.gcd_rec, ← ih]
    conv_lhs => rw [← Nat.mod_add_div' n m]
    rw [gcd_add_mul_self_right_of_dvd_sub hdvd m (n % m) (n / m), gcd_comm]

/-- The `Associated` form of `gcd_eq_normalize_of_dvd_sub`. -/
theorem associated_gcd_of_dvd_sub {a : ℕ → R} (h0 : a 0 = 0)
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    Associated (gcd (a m) (a n)) (a (m.gcd n)) :=
  gcd_eq_normalize_of_dvd_sub h0 hdvd m n ▸ normalize_associated _
