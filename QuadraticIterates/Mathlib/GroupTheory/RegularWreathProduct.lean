module

-- Beyond the sibling `Mathlib.GroupTheory.RegularWreathProduct`: homomorphisms into `C₂` are
-- counted through the `𝔽_p`-dual of an elementary abelian group, whence the `ZMod` imports.
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.RegularWreathProduct

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Homomorphisms from wreath products to abelian groups

A homomorphism from `D ≀ᵣ Q` to a commutative group `A` is the same as a pair of homomorphisms
`D →* A` and `Q →* A` (`RegularWreathProduct.homEquiv`), so
`#(D ≀ᵣ Q →* A) = #(D →* A) · #(Q →* A)` and `#(IteratedWreathProduct D n →* A) = #(D →* A) ^ n`.
Combined with `#(H →* C₂) = #H` for an elementary abelian `2`-group `H`, the maximal elementary
abelian `2`-quotient of the `n`-fold iterated wreath power of `C₂` has order `2 ^ n`.

## Main statements

* `RegularWreathProduct.homEquiv`: `(D ≀ᵣ Q →* A) ≃ (D →* A) × (Q →* A)` for commutative `A`.
* `RegularWreathProduct.card_hom`, `IteratedWreathProduct.card_hom`: the resulting counts.
* `Nat.card_monoidHom_multiplicative_zmod`: `#(H →* Multiplicative (ZMod p)) = #H` for a finite
  abelian group `H` of exponent dividing `p`; `Nat.card_monoidHom_multiplicative_zmod_two` needs
  no commutativity hypothesis.
* `wreath_max_elem_ab`: `#([C₂]ⁿ →* C₂) = 2 ^ n`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace RegularWreathProduct

variable {D Q : Type*} [Group D] [Group Q]

/-- The base group `Q → D` of `D ≀ᵣ Q`: the elements with trivial `Q`-component. -/
def inr : (Q → D) →* D ≀ᵣ Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp

@[simp] theorem left_inr (f : Q → D) : (inr f : D ≀ᵣ Q).left = f := rfl

@[simp] theorem right_inr (f : Q → D) : (inr f : D ≀ᵣ Q).right = 1 := rfl

theorem inr_left_mul_inl_right (w : D ≀ᵣ Q) : inr w.left * inl w.right = w := by ext <;> simp

/-- Conjugating the base group by `inl x` permutes the coordinates. -/
theorem inl_mul_inr_mul_inl_inv (x : Q) (f : Q → D) :
    inl x * inr f * (inl x)⁻¹ = inr fun y ↦ f (x⁻¹ * y) := by
  ext <;> simp

section CommGroup

variable {A : Type*} [CommGroup A]

/-- A homomorphism to a commutative group takes the same values on all coordinate copies of
`D` in the base group. -/
theorem map_inr_mulSingle [DecidableEq Q] (φ : D ≀ᵣ Q →* A) (x : Q) (d : D) :
    φ (inr (Pi.mulSingle x d)) = φ (inr (Pi.mulSingle 1 d)) := by
  have : (Pi.mulSingle x d : Q → D) = fun y ↦ (Pi.mulSingle 1 d : Q → D) (x⁻¹ * y) := by
    ext y; simp [Pi.mulSingle_apply, inv_mul_eq_one, eq_comm]
  rw [this, ← inl_mul_inr_mul_inl_inv, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

section Fintype

variable [Fintype Q]

/-- The homomorphism `D ≀ᵣ Q →* A` induced by `α : D →* A`: `w ↦ ∏ x, α (w.left x)`. -/
def prodLeftHom (α : D →* A) : D ≀ᵣ Q →* A where
  toFun w := ∏ x, α (w.left x)
  map_one' := by simp
  map_mul' w₁ w₂ := by
    simp only [mul_left, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp (Equiv.mulLeft w₁.right⁻¹) fun x ↦ α (w₂.left x)

@[simp] theorem prodLeftHom_apply (α : D →* A) (w : D ≀ᵣ Q) :
    prodLeftHom α w = ∏ x, α (w.left x) := rfl

variable [DecidableEq Q]

/-- A homomorphism to a commutative group is determined on the base group by its values on the
single coordinates. -/
theorem map_inr_eq_prod (φ : D ≀ᵣ Q →* A) (f : Q → D) :
    φ (inr f) = ∏ x, φ (inr (Pi.mulSingle x (f x))) :=
  (congrArg (φ ∘ inr) (Finset.noncommProd_mulSingle f).symm).trans <|
    (congrArg φ (Finset.map_noncommProd _ _ _ inr)).trans <|
      (Finset.map_noncommProd _ _ _ φ).trans (Finset.noncommProd_eq_prod _ _)

/-- Homomorphisms from `D ≀ᵣ Q` to a commutative group are pairs of a homomorphism on `D` (any
coordinate of the base group, they all agree by `map_inr_mulSingle`) and one on `Q`. -/
def homEquiv : (D ≀ᵣ Q →* A) ≃ (D →* A) × (Q →* A) where
  toFun φ := (φ.comp (inr.comp (MonoidHom.mulSingle (fun _ ↦ D) 1)), φ.comp inl)
  invFun p := prodLeftHom p.1 * p.2.comp rightHom
  left_inv φ := by
    ext w
    conv_rhs => rw [← inr_left_mul_inl_right w, map_mul, map_inr_eq_prod]
    simp only [MonoidHom.mul_apply, prodLeftHom_apply, MonoidHom.comp_apply,
      MonoidHom.mulSingle_apply, rightHom_eq_right]
    rw [Finset.prod_congr rfl fun x _ ↦ (map_inr_mulSingle φ x (w.left x)).symm]
  right_inv p := by
    refine Prod.ext (MonoidHom.ext fun d ↦ ?_) (MonoidHom.ext fun q ↦ ?_)
    · simp only [MonoidHom.mul_apply, prodLeftHom_apply, MonoidHom.comp_apply,
        MonoidHom.mulSingle_apply, rightHom_eq_right, left_inr, right_inr, map_one, mul_one]
      rw [Fintype.prod_eq_single 1 fun x hx ↦ by simp [Pi.mulSingle_eq_of_ne hx]]
      simp
    · simp

end Fintype

variable (D Q A) in
/-- `#(D ≀ᵣ Q →* A) = #(D →* A) · #(Q →* A)` for a finite group `Q` and a commutative group `A`. -/
theorem card_hom [Finite Q] : Nat.card (D ≀ᵣ Q →* A) = Nat.card (D →* A) * Nat.card (Q →* A) := by
  classical
  let := Fintype.ofFinite Q
  rw [Nat.card_congr homEquiv, Nat.card_prod]

end CommGroup

end RegularWreathProduct

/-- `#(IteratedWreathProduct D n →* A) = #(D →* A) ^ n` for a finite group `D` and a commutative
group `A`. -/
theorem IteratedWreathProduct.card_hom (D A : Type*) [Group D] [CommGroup A] [Finite D] (n : ℕ) :
    Nat.card (IteratedWreathProduct D n →* A) = Nat.card (D →* A) ^ n := by
  induction n with
  | zero => exact Nat.card_unique (α := PUnit →* A)
  | succ n ih => exact (RegularWreathProduct.card_hom _ D A).trans (by rw [ih, pow_succ])

/-- A finite `𝔽_p`-vector space has as many additive characters `V →+ ZMod p` as elements. -/
theorem Nat.card_addMonoidHom_zmod (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] : Nat.card (V →+ ZMod p) = Nat.card V :=
  calc Nat.card (V →+ ZMod p)
      = Nat.card (Module.Dual (ZMod p) V) :=
        Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv p).toEquiv
    _ = Nat.card V := (Nat.card_congr (Module.finBasis (ZMod p) V).toDualEquiv.toEquiv).symm

/-- A finite abelian group `H` of exponent dividing the prime `p` has as many characters
`H →* Multiplicative (ZMod p)` as elements. -/
theorem Nat.card_monoidHom_multiplicative_zmod {H : Type*} [CommGroup H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hexp : ∀ h : H, h ^ p = 1) :
    Nat.card (H →* Multiplicative (ZMod p)) = Nat.card H :=
  calc Nat.card (H →* Multiplicative (ZMod p))
      = Nat.card (Additive H →+ ZMod p) :=
        Nat.card_congr (MonoidHom.toAdditiveLeftMulEquiv.toEquiv.trans Multiplicative.toAdd)
    _ = Nat.card (Additive H) := @Nat.card_addMonoidHom_zmod p _ (Additive H) _
        (AddCommGroup.zmodModule fun x ↦ Additive.toMul.injective (by simpa using hexp x.toMul)) _
    _ = Nat.card H := Nat.card_congr Additive.toMul

/-- A finite group of exponent dividing `2` (automatically abelian) has as many characters
`H →* Multiplicative (ZMod 2)` as elements. -/
theorem Nat.card_monoidHom_multiplicative_zmod_two {H : Type*} [Group H] [Finite H]
    (hexp : ∀ h : H, h ^ 2 = 1) : Nat.card (H →* Multiplicative (ZMod 2)) = Nat.card H := by
  have hinv (a : H) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, hexp])
  let : CommGroup H :=
    { ‹Group H› with mul_comm a b := by rw [← hinv (a * b), mul_inv_rev, hinv a, hinv b] }
  exact card_monoidHom_multiplicative_zmod hexp

private theorem card_hom_c2 :
    Nat.card (Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_monoidHom_multiplicative_zmod_two (by decide), Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

/-- `#([C_2]^n →* C_2) = 2^n`: the maximal elementary-abelian 2-quotient of the `n`-fold iterated
wreath power of `C_2` has `𝔽₂`-dimension `n`. -/
theorem wreath_max_elem_ab (n : ℕ) :
    Nat.card (IteratedWreathProduct (Multiplicative (ZMod 2)) n →* Multiplicative (ZMod 2))
      = 2 ^ n := by
  rw [IteratedWreathProduct.card_hom, card_hom_c2]
