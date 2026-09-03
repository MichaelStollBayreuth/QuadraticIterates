module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A cardinality criterion for group isomorphism

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Two finite groups admitting an injective homomorphism from one to the other are isomorphic
iff they have the same cardinality. The homomorphism cannot be dispensed with (nonisomorphic
groups of the same order exist); to get it as the isomorphism itself, combine
`Nat.bijective_iff_injective_and_card` with `MulEquiv.ofBijective`. -/
theorem MonoidHom.nonempty_mulEquiv_iff_card_eq {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (φ : G →* H) (hφ : Function.Injective φ) :
    Nonempty (G ≃* H) ↔ Nat.card G = Nat.card H :=
  ⟨fun ⟨e⟩ ↦ Nat.card_congr e.toEquiv,
    fun h ↦ ⟨MulEquiv.ofBijective φ ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, h⟩)⟩⟩
