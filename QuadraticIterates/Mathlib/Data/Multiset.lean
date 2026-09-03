module

public import Mathlib.Data.Multiset.MapFold

import Mathlib.Data.Multiset.Basic

/-!
# Splitting a multiset along a fixed-point-free involution

A multiset invariant under a fixed-point-free involution `τ` splits as `N + N.map τ`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- A multiset `M` invariant under an involution `τ` that is fixed-point-free on its support
splits as `N + N.map τ`. -/
theorem Multiset.exists_add_map_of_involutive {β : Type*} (τ : β → β) (M : Multiset β)
    (hτ : ∀ x ∈ M, τ (τ x) = x) (hinv : M.map τ = M) (hfix : ∀ x ∈ M, τ x ≠ x) :
    ∃ N : Multiset β, M = N + N.map τ := by
  induction M using Multiset.strongInductionOn with
  | _ M ih =>
  rcases M.empty_or_exists_mem with rfl | ⟨x, hx⟩
  · exact ⟨0, rfl⟩
  obtain ⟨M₀, rfl⟩ := exists_cons_of_mem hx
  have hτx : τ x ∈ M₀ := (mem_cons.mp (hinv ▸ mem_map_of_mem τ hx)).resolve_left (hfix x hx)
  obtain ⟨M', rfl⟩ := exists_cons_of_mem hτx
  have hmem {y : β} (hy : y ∈ M') : y ∈ x ::ₘ τ x ::ₘ M' := mem_cons_of_mem (mem_cons_of_mem hy)
  have hinv' : M'.map τ = M' := by
    simp only [map_cons, hτ x hx] at hinv
    rw [cons_swap] at hinv
    exact (cons_inj_right _).mp ((cons_inj_right _).mp hinv)
  obtain ⟨N', rfl⟩ := ih M' ((lt_cons_self _ _).trans (lt_cons_self _ _))
    (fun y hy ↦ hτ y (hmem hy)) hinv' (fun y hy ↦ hfix y (hmem hy))
  exact ⟨x ::ₘ N', by rw [map_cons, cons_add, add_cons]⟩
