module

public import Mathlib.Algebra.Field.ZMod

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Big-operator lemmas

Sums and products with `if`s, and the balanced-classes lemma
`prod_eq_neg_prod_of_forall_card_filter_eq` for products over a partitioned index set.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Finset

theorem sum_mul_ite_const {ι R : Type*} [CommSemiring R] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → R) (c : R) :
    ∑ x ∈ s, g x * (if p x then c else 0) = c * ∑ x ∈ s with p x, g x := by
  simp [mul_ite, sum_filter, mul_sum, mul_comm]

/-- An `𝔽₂`-linear combination is the sum over the support of the coefficient function. -/
theorem sum_zmod_two_smul_eq_sum_filter {ι M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {s : Finset ι} (m : ι → M) (g : ι → ZMod 2) :
    ∑ i ∈ s, g i • m i = ∑ i ∈ s with g i = 1, m i := by
  rw [sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases (show g i = 0 ∨ g i = 1 by generalize g i = z; decide +revert) with h | h <;> simp [h]

/-- If `f` takes only the values `±1` on `S` and sums to `0` there, then `S` has as many elements
with `f = 1` as with `f = -1`. -/
theorem card_filter_eq_one_eq_card_filter_eq_neg_one_of_sum_eq_zero {α : Type*} {S : Finset α}
    {f : α → ℤ} (hpm : ∀ t ∈ S, f t = 1 ∨ f t = -1) (hsum : ∑ t ∈ S, f t = 0) :
    #{t ∈ S | f t = 1} = #{t ∈ S | f t = -1} := by
  have h : ∑ t ∈ S, (if f t = 1 then (1 : ℤ) else -1) = 0 :=
    (sum_congr rfl fun t ht ↦ by rcases hpm t ht with h | h <;> simp [h]).symm.trans hsum
  rw [filter_congr (p := fun t ↦ f t = -1) (q := fun t ↦ ¬f t = 1) fun t ht ↦ by
    rcases hpm t ht with h | h <;> simp [h]]
  simpa [sum_ite, add_neg_eq_zero] using h

/-- **Balanced classes.** Let `x` agree on `Sp ∪ Sm` with `w ∘ κ`, except for the sign at one
element `a`, `x a = -w (κ a)`. If the disjoint sets `Sp` and `Sm` contain equally many elements
of each class `κ⁻¹ i`, then `∏_{t ∈ Sp} x t = -∏_{t ∈ Sm} x t`: both products are the same
product of powers of the `w i`, and the sign comes from whichever set contains `a`. -/
theorem prod_eq_neg_prod_of_forall_card_filter_eq {R α ι : Type*} [CommMonoid R] [HasDistribNeg R]
    [DecidableEq α] [DecidableEq ι] {Sp Sm : Finset α} (hdisj : Disjoint Sp Sm) {x : α → R}
    {w : ι → R} {κ : α → ι} {a : α} (ha : a ∈ Sp ∪ Sm) (hxa : x a = -w (κ a))
    (hx : ∀ t ∈ Sp ∪ Sm, t ≠ a → x t = w (κ t))
    (hcard : ∀ i, #{t ∈ Sp | κ t = i} = #{t ∈ Sm | κ t = i}) :
    ∏ t ∈ Sp, x t = -∏ t ∈ Sm, x t := by
  have hprod (S : Finset α) (hS : S ⊆ Sp ∪ Sm) : ∏ t ∈ S, x t =
      (if a ∈ S then -1 else 1) * ∏ i ∈ (Sp ∪ Sm).image κ, w i ^ #{t ∈ S | κ t = i} := by
    rw [← prod_ite_eq' S a (fun _ ↦ (-1 : R)), ← prod_subset (image_subset_image hS)
      fun i _ hi ↦ by rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun t ht h ↦
        hi (mem_image.mpr ⟨t, ht, h⟩)), pow_zero], ← prod_comp, ← prod_mul_distrib]
    refine prod_congr rfl fun t ht ↦ ?_
    rcases eq_or_ne t a with rfl | h
    · rw [hxa, if_pos rfl, neg_one_mul]
    · rw [hx t (hS ht) h, if_neg h, one_mul]
  rw [hprod Sp subset_union_left, hprod Sm subset_union_right]
  simp only [hcard]
  rcases mem_union.mp ha with h | h
  · simp [h, disjoint_left.mp hdisj h]
  · simp [h, disjoint_right.mp hdisj h]

end Finset
