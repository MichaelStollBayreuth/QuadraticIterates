module

-- Beyond the sibling `Mathlib.GroupTheory.PGroup`: the results below concern a `p`-group acting
-- on an `𝔽_p`-module, so they need the `Module` API as well (their Mathlib home is unsettled
-- for the same reason; see the implementation note below).
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.GroupTheory.PGroup

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# Fixed points of `p`-groups on `𝔽_p`-modules

A `p`-group acting on an `𝔽_p`-module fixes a nonzero vector of every finite nonzero invariant
subspace; if the group acts transitively on the coordinates of `𝔽_p^ι`, a nonzero invariant
subspace therefore contains the all-ones vector.

## Main statements

* `IsPGroup.exists_ne_zero_mem_fixedPoints_of_smul_mem`: the nonzero fixed vector in an
  invariant subspace, from Mathlib's `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`.
* `IsPGroup.one_mem_of_comp_smul_mem_of_ne_bot`: the all-ones vector under a pretransitive
  coordinate action.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.

## Implementation notes

The eventual Mathlib home of these results is not obvious (they sit between
`GroupTheory.PGroup`, `RepresentationTheory`, and the linear-algebra `Module` files); they are
grouped here for now and will be placed during upstreaming.
-/

@[expose] public section

open MulAction

theorem IsPGroup.domMulAct {p : ℕ} {G : Type*} [Group G] (hG : IsPGroup p G) : IsPGroup p Gᵈᵐᵃ :=
  hG.of_equiv (MulEquiv.inv' G)

theorem MulAction.apply_eq_apply_of_forall_smul_eq {G ι β : Type*} [SMul G ι]
    [IsPretransitive G ι] {w : ι → β} (hw : ∀ (g : G) (i : ι), w (g • i) = w i) (i j : ι) :
    w i = w j :=
  let ⟨g, hg⟩ := exists_smul_eq G i j
  hg ▸ (hw g i).symm

/-- A `p`-group acting on an `𝔽_p`-module fixes a nonzero vector of every finite nonzero
invariant subspace. -/
theorem IsPGroup.exists_ne_zero_mem_fixedPoints_of_smul_mem {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] (hG : IsPGroup p G) {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] {V : Submodule (ZMod p) M} [Finite V]
    (hV : ∀ (g : G), ∀ v ∈ V, g • v ∈ V) (hne : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 0 ∧ v ∈ fixedPoints G M := by
  let S : SubMulAction G M := ⟨V, fun g ↦ hV g _⟩
  have e : S ≃ V := Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  have : Finite S := Finite.of_equiv V e.symm
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hcard : p ∣ Nat.card S := by
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p Module.finrank_pos.ne'
  obtain ⟨⟨v, hvV⟩, hv, hv0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point S hcard
    (a := ⟨0, V.zero_mem⟩) fun g ↦ Subtype.ext (smul_zero g)
  exact ⟨v, hvV, fun h ↦ hv0 (Subtype.ext h.symm), fun g ↦ congrArg Subtype.val (hv g)⟩

/-- A nonzero `𝔽_p`-subspace of `ι → 𝔽_p` invariant under a `p`-group `G` acting pretransitively
on the coordinates `ι` contains the all-ones vector. -/
theorem IsPGroup.one_mem_of_comp_smul_mem_of_ne_bot {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hG : IsPGroup p G) {ι : Type*} [Finite ι] [MulAction G ι] [IsPretransitive G ι]
    {V : Submodule (ZMod p) (ι → ZMod p)} (hV : ∀ (g : G), ∀ v ∈ V, (fun i ↦ v (g • i)) ∈ V)
    (hne : V ≠ ⊥) : 1 ∈ V := by
  obtain ⟨w, hwV, hwne, hwfix⟩ := hG.domMulAct.exists_ne_zero_mem_fixedPoints_of_smul_mem
    (fun g v hv ↦ hV (DomMulAct.mk.symm g) v hv) hne
  obtain ⟨i₀⟩ : Nonempty ι := not_isEmpty_iff.mp fun _ ↦ hne Submodule.eq_bot_of_subsingleton
  obtain ⟨b, rfl⟩ : ∃ b, w = fun _ ↦ b := ⟨w i₀, funext fun i ↦
    apply_eq_apply_of_forall_smul_eq (fun g i ↦ congrFun (hwfix (DomMulAct.mk g)) i) i i₀⟩
  have hb : b ≠ 0 := fun h ↦ hwne (funext fun _ ↦ h)
  exact (funext fun _ ↦ (inv_mul_cancel₀ hb).symm : (1 : ι → ZMod p) = b⁻¹ • fun _ ↦ b) ▸
    V.smul_mem b⁻¹ hwV
