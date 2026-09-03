module

public import Mathlib.Data.Fintype.Basic

/-!
# Subsets of `Fin (n + 1)`

A finset of `Fin (n + 1)` is the image of a finset of `Fin n` under `Fin.castSucc`, with
`Fin.last n` possibly inserted.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Every finset `T` of `Fin (n + 1)` is `S.map Fin.castSuccEmb` or
`insert (Fin.last n) (S.map Fin.castSuccEmb)`, for `S` the finset of `i : Fin n` with
`i.castSucc ∈ T`. -/
theorem Fin.exists_eq_map_castSuccEmb_or_insert_last {n : ℕ} (T : Finset (Fin (n + 1))) :
    ∃ S : Finset (Fin n),
      T = S.map Fin.castSuccEmb ∨ T = insert (Fin.last n) (S.map Fin.castSuccEmb) := by
  refine ⟨Finset.univ.filter (fun i : Fin n ↦ i.castSucc ∈ T), ?_⟩
  by_cases hlast : Fin.last n ∈ T
  · right
    ext x
    rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl <;> simp [hlast]
  · left
    ext x
    rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl <;> simp [hlast]
