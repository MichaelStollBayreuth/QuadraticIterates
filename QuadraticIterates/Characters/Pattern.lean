/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

import QuadraticIterates.Mathlib.NumberTheory.MulChar.Basic

/-!
# Sign patterns of characters along a sequence

A sign pattern `ε : ℕ → ℤ` is realized along a sequence `v` from `n` on if some multiplicative
character `χ` with values in `ℤ` has `χ (v m) = ε m` for all `m ≥ n`
(`QuadraticIterates.HasCharPattern`). Realized patterns are closed under pointwise products; this
file derives the patterns used for the sequence `c_n` from simpler ones. For `c_n` we write `φ_n`
for the pattern `Pi.mulSingle n (-1)` (`-1` at `n`, `1` after `n`), `φ₀` for the constant pattern
`-1` and `τ` for `-Pi.mulSingle 1 (-1)`.

## Main definitions

* `QuadraticIterates.HasCharPattern v n ε`: the pattern `ε` is realized along `v` from `n` on.

## Main statements

* `QuadraticIterates.hasCharPattern_neg_mulSingle_of_neg_of_mulSingle` and its two siblings: any
  two of the patterns `-1`, `Pi.mulSingle k (-1)` and `-Pi.mulSingle k (-1)` give the third.
* `QuadraticIterates.hasCharPattern_mulSingle_one_of_apply`,
  `QuadraticIterates.hasCharPattern_neg_mulSingle_one_of_apply`: `φ₁` and `τ` from the values of
  one character.
* `QuadraticIterates.hasCharPattern_mulSingle_of_neg_of_forall_lt`: `φ₀` and a character that
  changes sign after `n` give `φ_n`.
* `QuadraticIterates.hasCharPattern_mulSingle_of_neg_of_alternating`: `φ₀`, a character
  alternating from `n` on and a character with the pattern `(x, y, -x, y, -x, …)` from `n` on
  give `φ_n`.
-/

@[expose] public section

namespace QuadraticIterates

variable {M : Type*} [CommMonoid M]

/-- The sign pattern `ε` is realized along the sequence `v` from index `n` on: some multiplicative
character `χ` with values in `ℤ` has `χ (v m) = ε m` for all `m ≥ n`. The values of `ε` before `n`
play no role. -/
def HasCharPattern (v : ℕ → M) (n : ℕ) (ε : ℕ → ℤ) : Prop :=
  ∃ χ : MulChar M ℤ, ∀ m ≥ n, χ (v m) = ε m

variable {v : ℕ → M} {n : ℕ} {ε ε' : ℕ → ℤ}

namespace HasCharPattern

theorem mul (h : HasCharPattern v n ε) (h' : HasCharPattern v n ε') :
    HasCharPattern v n (ε * ε') :=
  let ⟨χ, hχ⟩ := h
  let ⟨χ', hχ'⟩ := h'
  ⟨χ * χ', fun m hm ↦ by simp [hχ m hm, hχ' m hm]⟩

theorem mono (h : HasCharPattern v n ε) {n' : ℕ} (hn : n ≤ n') : HasCharPattern v n' ε :=
  let ⟨χ, hχ⟩ := h
  ⟨χ, fun m hm ↦ hχ m (hn.trans hm)⟩

theorem congr (h : HasCharPattern v n ε) (he : ∀ m ≥ n, ε m = ε' m) : HasCharPattern v n ε' :=
  let ⟨χ, hχ⟩ := h
  ⟨χ, fun m hm ↦ (hχ m hm).trans (he m hm)⟩

/-- A sequence has no zero term where a realized pattern is nonzero. -/
theorem ne_zero {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] {u : ℕ → M₀}
    (h : HasCharPattern u n ε) {m : ℕ} (hm : n ≤ m) (hε : ε m ≠ 0) :
    u m ≠ 0 := fun hu ↦ hε <| by
  obtain ⟨χ, hχ⟩ := h
  rw [← hχ m hm, hu, MulChar.map_zero]

end HasCharPattern

/-! ### Two of three -/

variable {k : ℕ}

theorem hasCharPattern_neg_mulSingle_of_neg_of_mulSingle (h₀ : HasCharPattern v n (-1))
    (h₁ : HasCharPattern v n (Pi.mulSingle k (-1))) :
    HasCharPattern v n (-Pi.mulSingle k (-1)) := by
  simpa using h₀.mul h₁

theorem hasCharPattern_mulSingle_of_neg_of_neg_mulSingle (h₀ : HasCharPattern v n (-1))
    (h₁ : HasCharPattern v n (-Pi.mulSingle k (-1))) :
    HasCharPattern v n (Pi.mulSingle k (-1)) := by
  simpa using h₀.mul h₁

theorem hasCharPattern_neg_of_mulSingle_of_neg_mulSingle
    (h₀ : HasCharPattern v n (Pi.mulSingle k (-1)))
    (h₁ : HasCharPattern v n (-Pi.mulSingle k (-1))) :
    HasCharPattern v n (-1) := by
  simpa [← Pi.mulSingle_mul] using h₀.mul h₁

/-! ### Patterns from values -/

/-- A character that is `-1` at `v 1` and `1` at all later terms realizes `φ₁` (the pattern
`Pi.mulSingle 1 (-1)`) from `1` on. -/
theorem hasCharPattern_mulSingle_one_of_apply (χ : MulChar M ℤ) (h₁ : χ (v 1) = -1)
    (h : ∀ n ≥ 2, χ (v n) = 1) :
    HasCharPattern v 1 (Pi.mulSingle 1 (-1)) :=
  ⟨χ, fun n hn ↦ by
    rcases hn.eq_or_lt with rfl | hn
    · simpa using h₁
    · rw [h n hn, Pi.mulSingle_eq_of_ne (by lia)]⟩

/-- A character that is `1` at `v 1` and `-1` at all later terms realizes `τ` (the pattern
`-Pi.mulSingle 1 (-1)`) from `1` on. -/
theorem hasCharPattern_neg_mulSingle_one_of_apply (χ : MulChar M ℤ) (h₁ : χ (v 1) = 1)
    (h : ∀ n ≥ 2, χ (v n) = -1) :
    HasCharPattern v 1 (-Pi.mulSingle 1 (-1)) :=
  ⟨χ, fun n hn ↦ by
    rcases hn.eq_or_lt with rfl | hn
    · simpa using h₁
    · rw [h n hn, Pi.neg_apply, Pi.mulSingle_eq_of_ne (by lia)]⟩

/-! ### Jumps -/

/-- Given `φ₀` (the constant pattern `-1`) from `n`, a character `ψ` with `ψ (v n) ≠ 0` whose
later values are all `-ψ (v n)` yields `φ_n` (the pattern `Pi.mulSingle n (-1)`): `ψ` itself if
`ψ (v n) = -1`, `φ₀ ψ` if `ψ (v n) = 1`. -/
theorem hasCharPattern_mulSingle_of_neg_of_forall_lt (h₀ : HasCharPattern v n (-1))
    {ψ : MulChar M ℤ} (hψ : ψ (v n) ≠ 0) (h : ∀ m > n, ψ (v m) = -ψ (v n)) :
    HasCharPattern v n (Pi.mulSingle n (-1)) := by
  obtain ⟨χ, hχ⟩ := h₀
  rcases (ψ.isQuadratic_int (v n)).resolve_left hψ with h1 | h1
  · refine ⟨χ * ψ, fun m hm ↦ ?_⟩
    rcases hm.eq_or_lt with rfl | hm
    · simp [hχ _ le_rfl, h1]
    · simp [hχ m hm.le, h m hm, h1, hm.ne']
  · refine ⟨ψ, fun m hm ↦ ?_⟩
    rcases hm.eq_or_lt with rfl | hm
    · simp [h1]
    · simp [h m hm, h1, hm.ne']

/-- A function that is `2`-periodic from `n + 1` on and takes the value `c` at `n + 1` and `n + 2`
is `c` at all `m > n`. -/
private lemma eq_of_lt_of_add_two_eq {f : ℕ → ℤ} {c : ℤ} (h₁ : f (n + 1) = c)
    (h₂ : f (n + 2) = c) (hp : ∀ m ≥ n + 1, f (m + 2) = f m) (m : ℕ) (hm : n < m) :
    f m = c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  induction k using Nat.twoStepInduction with
  | zero => exact h₁
  | one => exact h₂
  | more k ih _ => simpa [hp (n + k + 1) (by lia), ← add_assoc] using ih (by lia)

/-- Given `φ₀` (the constant pattern `-1`) from `n` and a character `ψ` alternating from `n` on, a
character `χ` with the pattern `(x, y, -x, y, -x, …)` from `n` on yields `φ_n`
(`Pi.mulSingle n (-1)`): `χ` itself has the pattern `(x, -x, -x, …)` of
`QuadraticIterates.hasCharPattern_mulSingle_of_neg_of_forall_lt` if `y = -x`, and `χ ψ` has such
a pattern if `y = x`. -/
theorem hasCharPattern_mulSingle_of_neg_of_alternating (h₀ : HasCharPattern v n (-1))
    {ψ : MulChar M ℤ} (hψ₀ : ψ (v n) ≠ 0) (hψ : ∀ m ≥ n, ψ (v (m + 1)) = -ψ (v m))
    {χ : MulChar M ℤ} (hχ₀ : χ (v n) ≠ 0) (hχ₁ : χ (v (n + 1)) ≠ 0)
    (hχ₂ : χ (v (n + 2)) = -χ (v n)) (hχ : ∀ m ≥ n + 1, χ (v (m + 2)) = χ (v m)) :
    HasCharPattern v n (Pi.mulSingle n (-1)) := by
  have hψ₂ : ∀ m ≥ n, ψ (v (m + 2)) = ψ (v m) := fun m hm ↦ by
    rw [hψ (m + 1) (by lia), hψ m hm, neg_neg]
  have hxy : χ (v (n + 1)) = -χ (v n) ∨ χ (v (n + 1)) = χ (v n) := by
    grind [(χ.isQuadratic_int (v n)).resolve_left hχ₀,
      (χ.isQuadratic_int (v (n + 1))).resolve_left hχ₁]
  rcases hxy with hy | hy
  · exact hasCharPattern_mulSingle_of_neg_of_forall_lt h₀ hχ₀
      (eq_of_lt_of_add_two_eq (f := fun m ↦ χ (v m)) hy hχ₂ hχ)
  · refine hasCharPattern_mulSingle_of_neg_of_forall_lt h₀ (ψ := χ * ψ)
      (by simpa using mul_ne_zero hχ₀ hψ₀) fun m hm ↦ ?_
    refine eq_of_lt_of_add_two_eq (f := fun m ↦ χ (v m) * ψ (v m)) ?_ ?_ (fun m hm ↦ ?_) m hm
    · simp [hy, hψ n le_rfl]
    · simp [hχ₂, hψ₂ n le_rfl]
    · simp [hχ m hm, hψ₂ m (by lia)]

end QuadraticIterates
