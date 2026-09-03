module

-- Beyond the sibling `Mathlib.Algebra.Group.Subgroup.Ker`: `IsSquare` lives in `Group.Even`,
-- which the sibling does not import; a Mathlib PR would add that import there.
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Squares and the range of `powMonoidHom 2`

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- An element lies in the range of `powMonoidHom 2` iff it is a square. -/
theorem mem_mrange_powMonoidHom_two_iff {M : Type*} [CommMonoid M] (a : M) :
    a ∈ MonoidHom.mrange (powMonoidHom 2 : M →* M) ↔ IsSquare a := by
  simp [isSquare_iff_exists_sq, eq_comm]

/-- The value of a unit is a square iff the unit is one. -/
theorem Units.isSquare_val_iff {M : Type*} [CommMonoid M] (u : Mˣ) :
    IsSquare (u : M) ↔ IsSquare u := by
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun h ↦ h.map (Units.coeHom M)⟩
  obtain ⟨t, rfl⟩ := isUnit_of_mul_isUnit_left (ht ▸ u.isUnit)
  exact ⟨t, Units.ext (by simpa using ht)⟩

/-- A unit lies in the range of `powMonoidHom 2` iff its value is a square. -/
theorem Units.mem_range_powMonoidHom_two_iff {M : Type*} [CommMonoid M] (u : Mˣ) :
    u ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range ↔ IsSquare (u : M) :=
  MonoidHom.mem_range.trans <| MonoidHom.mem_mrange.symm.trans <|
    (mem_mrange_powMonoidHom_two_iff u).trans (Units.isSquare_val_iff u).symm
