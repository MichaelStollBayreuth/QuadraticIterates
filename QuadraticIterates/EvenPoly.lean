/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Expand

import QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp

/-!
# Even polynomials and their iteration sequences

A polynomial `g ∈ R[X]` is even if it lies in `R[X²]`. Its iteration sequence with sign `ε` is
`γ_1 = ε · g(0)`, `γ_{n+1} = g(γ_n)`; the sequence `c_n` of the iterates of `X² + a` is the case
`g = X² + a`, `ε = -1` (`QuadraticIterates.cSeq`).

## Main definitions

* `QuadraticIterates.EvenPoly g`: `g` is even, i.e. `g ∈ R[X²]`; over a domain of characteristic
  `≠ 2` this is `g(-X) = g` (`QuadraticIterates.evenPoly_iff_comp_neg_X`).
* `QuadraticIterates.gammaSeq g ε`: the iteration sequence `γ` of `g` with sign `ε`.

## Main statements

* `QuadraticIterates.map_gammaSeq`: `γ` commutes with ring homomorphisms, which is how congruences
  for `γ` are computed in `ZMod m`.
* `QuadraticIterates.gammaSeq_eq_ite_even_of_add_two_eq`: if `γ_{n₀+2} = γ_{n₀}` for some
  `n₀ ≥ 1`, the sequence is `2`-periodic from `n₀` on.
-/

@[expose] public section

open Polynomial

namespace QuadraticIterates

/-! ### Even polynomials -/

section EvenPoly

variable {R : Type*} [CommSemiring R]

/-- `g` is an even polynomial (`g ∈ R[X²]`): `g = Polynomial.expand R 2 h` for some `h`. -/
def EvenPoly (g : R[X]) : Prop := ∃ h : R[X], g = expand R 2 h

namespace EvenPoly

variable {g : R[X]}

theorem eval_congr (hg : EvenPoly g) {x y : R} (h : x ^ 2 = y ^ 2) : g.eval x = g.eval y := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval, h]

theorem map {S : Type*} [CommSemiring S] (hg : EvenPoly g) (φ : R →+* S) : EvenPoly (g.map φ) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h.map φ, map_expand⟩

end EvenPoly

end EvenPoly

section EvenPoly

variable {R : Type*} [CommRing R] {g : R[X]}

namespace EvenPoly

theorem eval_neg (hg : EvenPoly g) (y : R) : g.eval (-y) = g.eval y := hg.eval_congr (neg_sq y)

lemma comp_neg_X (hg : EvenPoly g) : g.comp (-X) = g := by
  obtain ⟨h, rfl⟩ := hg
  exact expand_two_comp_neg_X h

end EvenPoly

/-- Over a domain of characteristic `≠ 2`, `g` lies in `R[X²]` (`QuadraticIterates.EvenPoly g`) iff
it is invariant under `X ↦ -X`; the forward implication, `QuadraticIterates.EvenPoly.comp_neg_X`,
holds over every commutative ring. -/
lemma evenPoly_iff_comp_neg_X [NoZeroDivisors R] [NeZero (2 : R)] : EvenPoly g ↔ g.comp (-X) = g :=
  ⟨EvenPoly.comp_neg_X, fun h ↦ ⟨contract 2 g, eq_expand_two_contract_of_comp_neg_X_eq h⟩⟩

end EvenPoly

/-! ### The iteration sequence `γ` -/

/-- The iteration sequence `γ_n` of `g ∈ R[X]` with sign choice `ε`: `γ_1 = ε · g(0)`, `γ_{n+1} =
g(γ_n)`; the value at index `0` is `0`, so that for even `g` and `ε = ±1`, `γ_n = ±g^{∘n}(0)` for
all `n` (over `ℤ`, a strong divisibility sequence up to sign). -/
def gammaSeq {R : Type*} [CommSemiring R] (g : R[X]) (ε : R) : ℕ → R
  | 0 => 0
  | 1 => ε * g.eval 0
  | n + 2 => g.eval (gammaSeq g ε (n + 1))

section

variable {R : Type*} [CommSemiring R] (g : R[X])

@[simp] lemma gammaSeq_zero (ε : R) : gammaSeq g ε 0 = 0 := rfl

@[simp] lemma gammaSeq_one (ε : R) : gammaSeq g ε 1 = ε * g.eval 0 := rfl

lemma gammaSeq_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε (n + 1) = g.eval (gammaSeq g ε n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hn
  rfl

lemma map_gammaSeq {S : Type*} [CommSemiring S] (φ : R →+* S) (ε : R) (n : ℕ) :
    φ (gammaSeq g ε n) = gammaSeq (g.map φ) (φ ε) n := by
  fun_induction gammaSeq g ε n with
  | case1 => simp
  | case2 => simp [gammaSeq]
  | case3 n ih => simp [gammaSeq, ← ih, eval_map_apply]

/-- If `γ_{n₀+2} = γ_{n₀}` (`n₀ ≥ 1`), then the sequence is `2`-periodic from index `n₀` on:
`γ_n = γ_{n₀}` for `n ≡ n₀ mod 2` and `γ_n = γ_{n₀+1}` otherwise, for all `n ≥ n₀`. -/
theorem gammaSeq_eq_ite_even_of_add_two_eq {ε : R} {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (h : gammaSeq g ε (n₀ + 2) = gammaSeq g ε n₀) :
    ∀ n ≥ n₀,
      gammaSeq g ε n = if Even (n + n₀) then gammaSeq g ε n₀ else gammaSeq g ε (n₀ + 1) := by
  have h1 : g.eval (gammaSeq g ε n₀) = gammaSeq g ε (n₀ + 1) := (gammaSeq_succ g ε hn₀).symm
  have h2 : g.eval (gammaSeq g ε (n₀ + 1)) = gammaSeq g ε n₀ := by
    rw [← h, gammaSeq_succ g ε (n := n₀ + 1) (by lia)]
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => grind [Nat.even_add_one]
  | succ n hn ih => grind [gammaSeq_succ g ε (by lia : 1 ≤ n), Nat.even_add_one]

end

end QuadraticIterates
