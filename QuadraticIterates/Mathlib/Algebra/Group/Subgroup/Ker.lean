module

-- Beyond the sibling `Mathlib.Algebra.Group.Subgroup.Ker`: `IsSquare` lives in `Group.Even`,
-- which the sibling does not import; a Mathlib PR would add that import there.
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The range of `powMonoidHom 2` on units

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- A unit lies in the range of `powMonoidHom 2` iff its value is a square. -/
theorem Units.mem_range_powMonoidHom_two_iff {M : Type*} [CommMonoid M] (u : Mˣ) :
    u ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range ↔ IsSquare (u : M) := by
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨v, ?_⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  · rw [← hv]; simp [sq]
  · obtain ⟨t, rfl⟩ := isUnit_of_mul_isUnit_left (ht ▸ u.isUnit)
    exact ⟨t, Units.ext (by simp [ht, sq])⟩
