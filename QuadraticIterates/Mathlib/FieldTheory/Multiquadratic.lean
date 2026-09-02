module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.Pi

import QuadraticIterates.Mathlib.Algebra.BigOperators
import QuadraticIterates.Mathlib.Algebra.BigOperators.Group.Finset.Basic
import QuadraticIterates.Mathlib.Algebra.Group.Subgroup.Ker
import QuadraticIterates.Mathlib.GroupTheory.PGroup
import QuadraticIterates.Mathlib.LinearAlgebra.Pi

/-!
# Multiquadratic field extensions

The degree of a multiquadratic extension `L(√c₁, …, √cₘ)/L` over a field of characteristic `≠ 2`
is `2 ^ (m - dim V)`, where `V ≤ 𝔽₂^m` is the space of square relations between the radicands,
realized as the kernel of a linear map to `Lˣ/(Lˣ)²`; descent of squares along such extensions.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IntermediateField

variable {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]

/-- Adjoining `insert x S` to `L` is adjoining `x` to `L(S)`, viewed over `L`. -/
theorem adjoin_insert (S : Set E) (x : E) :
    adjoin L (insert x S) = ((adjoin L S)⟮x⟯).restrictScalars L := by
  rw [adjoin_adjoin_left, Set.union_singleton]

/-- The relative degree of `L(S, x)` over `L(S)` is the degree of `x` over `L(S)`. -/
theorem relfinrank_adjoin_insert (S : Set E) (x : E) :
    (adjoin L S).relfinrank (adjoin L (insert x S)) =
      Module.finrank (adjoin L S) (adjoin L S)⟮x⟯ := by
  have hle : adjoin L S ≤ ((adjoin L S)⟮x⟯).restrictScalars L := by
    rw [← adjoin_insert]; exact adjoin.mono L _ _ (Set.subset_insert x S)
  rw [adjoin_insert, relfinrank_eq_finrank_of_le hle,
    restrictScalars_injective L (extendScalars_restrictScalars hle)]

/-- Tower law for adjoining one more element: `[L(S, x) : L] = [L(S) : L] · [L(S)(x) : L(S)]`. -/
theorem finrank_adjoin_insert (S : Set E) (x : E) :
    Module.finrank L (adjoin L (insert x S)) =
      Module.finrank L (adjoin L S) * Module.finrank (adjoin L S) (adjoin L S)⟮x⟯ := by
  rw [← relfinrank_adjoin_insert,
    finrank_bot_mul_relfinrank (adjoin.mono L _ _ (Set.subset_insert x S))]

/-- Adjoining a single square root `x` (with `x² ∈ L`) to a field `L` gives degree at most `2`. -/
theorem finrank_adjoin_sqrt_le {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c) :
    Module.finrank L (adjoin L {x}) ≤ 2 := by
  have hmonic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  rw [adjoin.finrank ⟨_, hmonic, by simp [hc]⟩]
  simpa using Polynomial.natDegree_le_natDegree (minpoly.min L x hmonic (by simp [hc]))

/-- Adjoining a square root `x` of an element of `L` to `L(t)` gives relative degree at most
`2`. -/
theorem relfinrank_adjoin_insert_sqrt_le {t : Set E} {x : E} {c : L}
    (hc : x ^ 2 = algebraMap L E c) :
    (adjoin L t).relfinrank (adjoin L (insert x t)) ≤ 2 :=
  (relfinrank_adjoin_insert t x).trans_le <|
    finrank_adjoin_sqrt_le (hc.trans (IsScalarTower.algebraMap_apply L (adjoin L t) E c))

/-- Adjoining a finite set of square roots (each squaring into `L`) gives degree at most
`2 ^ |s|`. -/
theorem finrank_adjoin_finset_sqrt_le {s : Finset E}
    (hs : ∀ x ∈ s, ∃ c : L, x ^ 2 = algebraMap L E c) :
    Module.finrank L (adjoin L (s : Set E)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Finset.card_empty, pow_zero, adjoin_empty, IntermediateField.finrank_bot]
  | insert x t hxt ih =>
    obtain ⟨c, hc⟩ := hs x (Finset.mem_insert_self x t)
    rw [Finset.coe_insert, ← finrank_bot_mul_relfinrank (adjoin.mono L _ _ (Set.subset_insert x _)),
      Finset.card_insert_of_notMem hxt, pow_succ]
    exact Nat.mul_le_mul (ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
      (relfinrank_adjoin_insert_sqrt_le hc)

/-- Adjoining a square root of `c` gives degree `1` if `c` is already a square in `L`, and `2`
otherwise. -/
theorem finrank_adjoin_sqrt_eq {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c)
    [Decidable (IsSquare c)] :
    Module.finrank L L⟮x⟯ = if IsSquare c then 1 else 2 := by
  have hone_iff : Module.finrank L L⟮x⟯ = 1 ↔ IsSquare c := by
    rw [finrank_adjoin_simple_eq_one_iff, mem_bot, IsSquare, Set.mem_range]
    refine ⟨fun ⟨y, hy⟩ ↦ ⟨y, ?_⟩, fun ⟨r, hr⟩ ↦ ?_⟩
    · rw [← hy, ← map_pow, pow_two, eq_comm] at hc
      exact RingHom.injective (algebraMap L E) hc
    · rw [hr, map_mul, ← pow_two, sq_eq_sq_iff_eq_or_eq_neg] at hc
      rcases hc with hc | hc
      · exact ⟨_, hc.symm⟩
      · exact ⟨-r, by grind⟩
  have : FiniteDimensional L L⟮x⟯ :=
    adjoin.finiteDimensional ⟨_, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hc]⟩
  have : 0 < Module.finrank L L⟮x⟯ := Module.finrank_pos
  grind [finrank_adjoin_sqrt_le hc]

/-- Adjoining a square root `w` of `c` doubles the degree when `c` is not a square in `L(S)`. -/
theorem finrank_adjoin_insert_of_not_isSquare {S : Set E} {w : E} {c : L}
    (hw : w ^ 2 = algebraMap L E c) (h : ¬ IsSquare (algebraMap L (adjoin L S) c)) :
    Module.finrank L (adjoin L (insert w S)) = 2 * Module.finrank L (adjoin L S) := by
  classical
  rw [finrank_adjoin_insert,
    finrank_adjoin_sqrt_eq (hw.trans (IsScalarTower.algebraMap_apply L (adjoin L S) E c)),
    if_neg h, mul_comm]

/-- If `p + q·x = 0` with `p, q ∈ L` and `q ≠ 0`, then `x` lies in the base field. -/
theorem mem_bot_of_add_mul_eq_zero {x : E} {p q : L} (hq : q ≠ 0)
    (h : algebraMap L E p + algebraMap L E q * x = 0) : x ∈ (⊥ : IntermediateField L E) := by
  refine mem_bot.mpr ⟨-p / q, ?_⟩
  rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero _).mpr hq)]
  linear_combination -h

/-- One-step square descent: over `L(x)` with `x² = c` and `x ∉ L`, the image of `d ∈ L` is a
square iff `d` or `d · c` is a square in `L`. -/
theorem square_descent_step [NeZero (2 : L)] {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c)
    (hx : x ∉ (⊥ : IntermediateField L E)) (d : L) :
    (∃ u v : L, algebraMap L E d = (algebraMap L E u + algebraMap L E v * x) ^ 2)
      ↔ (IsSquare d ∨ IsSquare (d * c)) := by
  refine ⟨fun ⟨u, v, huv⟩ ↦ ?_,
    fun h ↦ h.elim (fun ⟨w, hw⟩ ↦ ⟨w, 0, by simp [hw, sq]⟩) fun ⟨w, hw⟩ ↦ ?_⟩
  · have h : algebraMap L E (u ^ 2 + v ^ 2 * c - d) + algebraMap L E (2 * (u * v)) * x = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination -huv - (algebraMap L E v) ^ 2 * hc
    have hq : 2 * (u * v) = 0 :=
      by_contra fun hq ↦ hx (mem_bot_of_add_mul_eq_zero hq h)
    have hd : u ^ 2 + v ^ 2 * c - d = 0 := by
      rwa [hq, map_zero, zero_mul, add_zero, map_eq_zero] at h
    rcases (by simpa [two_ne_zero] using hq : u = 0 ∨ v = 0) with rfl | rfl
    · exact .inr ⟨v * c, by grind⟩
    · exact .inl ⟨u, by grind⟩
  · have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx ((pow_eq_zero_iff two_ne_zero).mp (hc.trans (map_zero _)) ▸ zero_mem _)
    refine ⟨0, w / c, ?_⟩
    rw [map_zero, zero_add, mul_pow, hc, ← map_pow, ← map_mul]
    congr 1
    grind

/-- For an intermediate field `K` of `E/L` and `e : L`, the image of `e` in `K` is a square
iff some element of `K` squares to the image of `e` in `E`. -/
theorem isSquare_algebraMap_iff (K : IntermediateField L E) (e : L) :
    IsSquare (algebraMap L ↥K e) ↔ ∃ z ∈ K, z ^ 2 = algebraMap L E e := by
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, w.2, ?_⟩, fun ⟨z, hz, hz2⟩ ↦ ⟨⟨z, hz⟩, Subtype.ext ?_⟩⟩
  · simpa [sq] using congrArg Subtype.val hw.symm
  · simpa [sq] using hz2.symm

/-- If `w` is a square root of `algebraMap e` lying outside an intermediate field `K`, then `e`
is not a square in `K`. -/
theorem not_isSquare_algebraMap_of_sqrt_notMem {K : IntermediateField L E} {e : L} {w : E}
    (hw : w ^ 2 = algebraMap L E e) (hwK : w ∉ K) : ¬ IsSquare (algebraMap L ↥K e) := fun h ↦ by
  obtain ⟨z, hzK, hz⟩ := (isSquare_algebraMap_iff K e).mp h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hw.trans hz.symm) with rfl | rfl
  exacts [hwK hzK, hwK (neg_mem hzK)]

/-- An element of the base field is a square in the bottom intermediate field iff it is a square
in the base field. -/
theorem isSquare_algebraMap_bot_iff (x : L) :
    IsSquare (algebraMap L ↥(⊥ : IntermediateField L E) x) ↔ IsSquare x := by
  rw [← botEquiv_symm]
  exact ⟨fun h ↦ by simpa using h.map (botEquiv L E), fun h ↦ h.map _⟩

open Polynomial in
/-- An element of the simple extension `L(y)` with `y² ∈ L` is exactly an `L`-linear combination
`u + v · y`. -/
theorem mem_adjoin_sqrt_iff {y : E} {c : L} (hy : y ^ 2 = algebraMap L E c) {z : E} :
    z ∈ L⟮y⟯ ↔ ∃ u v : L, z = algebraMap L E u + algebraMap L E v * y := by
  classical
  have hmonic : (X ^ 2 - C c).Monic := monic_X_pow_sub_C c two_ne_zero
  have hroot : aeval y (X ^ 2 - C c) = 0 := by simp [hy]
  rw [← mem_toSubalgebra,
    adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.isAlgebraic ⟨_, hmonic, hroot⟩),
    ← Subalgebra.mem_toSubmodule, ← Submodule.span_range_natDegree_eq_adjoin hmonic hroot,
    natDegree_X_pow_sub_C, show Finset.image (y ^ ·) (Finset.range 2) = {1, y} by
      simp [show Finset.range 2 = {0, 1} by decide],
    Finset.coe_pair, Submodule.mem_span_pair]
  simp [Algebra.smul_def, eq_comm]

/-- If `d · ∏_{i ∈ t} r i` is a square in `L` for some `t ⊆ s`, then `d` has a square root in
`L(x i : i ∈ s)`: divide the root by `∏_{i ∈ t} x i`. -/
theorem exists_sq_eq_algebraMap_of_isSquare_mul_prod {ι : Type*} {s : Finset ι} {x : ι → E}
    {r : ι → L} (hx : ∀ i ∈ s, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i ∈ s, r i ≠ 0) {d : L}
    {t : Finset ι} (ht : t ⊆ s) (hsq : IsSquare (d * ∏ i ∈ t, r i)) :
    ∃ z ∈ adjoin L (x '' s), z ^ 2 = algebraMap L E d := by
  obtain ⟨w, hw⟩ := hsq
  have hP : (∏ i ∈ t, x i) ^ 2 = algebraMap L E (∏ i ∈ t, r i) := by
    rw [map_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i hi ↦ hx i (ht hi)
  have hrne : algebraMap L E (∏ i ∈ t, r i) ≠ 0 :=
    (map_ne_zero _).mpr (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hr i (ht hi))
  refine ⟨algebraMap L E w / ∏ i ∈ t, x i, div_mem (algebraMap_mem _ _)
    (prod_mem fun i hi ↦ subset_adjoin L _ ⟨i, ht hi, rfl⟩), ?_⟩
  rw [div_pow, hP, div_eq_iff hrne, ← map_pow, ← map_mul, hw, sq]

/-- Iterated square descent: some element of `L(x i : i ∈ s)` squares to `d` iff
`d * ∏_{i ∈ t} r i` is a square in `L` for some subset `t ⊆ s`. -/
theorem square_descent [NeZero (2 : L)] {ι : Type*} {s : Finset ι} {x : ι → E} {r : ι → L}
    (hx : ∀ i ∈ s, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i ∈ s, r i ≠ 0) (d : L) :
    (∃ z ∈ adjoin L (x '' s), z ^ 2 = algebraMap L E d)
      ↔ ∃ t ⊆ s, IsSquare (d * ∏ i ∈ t, r i) := by
  classical
  refine ⟨?_, fun ⟨t, ht, hsq⟩ ↦ exists_sq_eq_algebraMap_of_isSquare_mul_prod hx hr ht hsq⟩
  induction s using Finset.induction_on generalizing d with
  | empty =>
    refine fun ⟨z, hz, hz2⟩ ↦ ?_
    rw [Finset.coe_empty, Set.image_empty, adjoin_empty, mem_bot] at hz
    obtain ⟨w, rfl⟩ := hz
    refine ⟨∅, Finset.empty_subset _, w, (algebraMap L E).injective ?_⟩
    simpa [sq] using hz2.symm
  | insert j s hjs ih =>
    refine fun ⟨z, hz, hz2⟩ ↦ ?_
    have hx' : ∀ i ∈ s, x i ^ 2 = algebraMap L E (r i) :=
      fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    have hr' : ∀ i ∈ s, r i ≠ 0 := fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)
    set K := adjoin L (x '' s)
    rw [Finset.coe_insert, Set.image_insert_eq] at hz
    by_cases hjK : x j ∈ K
    · obtain ⟨t, ht, hsq⟩ := ih hx' hr' d
        ⟨z, adjoin_le_iff.mpr (Set.insert_subset hjK (subset_adjoin L _)) hz, hz2⟩
      exact ⟨t, ht.trans (Finset.subset_insert j s), hsq⟩
    · have : NeZero (2 : K) := ⟨map_ofNat (algebraMap L K) 2 ▸ (map_ne_zero _).mpr two_ne_zero⟩
      have hxj : x j ^ 2 = algebraMap K E (algebraMap L K (r j)) :=
        (hx j (Finset.mem_insert_self j s)).trans (IsScalarTower.algebraMap_apply L K E (r j))
      rw [adjoin_insert, mem_restrictScalars, mem_adjoin_sqrt_iff hxj] at hz
      obtain ⟨u, v, rfl⟩ := hz
      have hjbot : x j ∉ (⊥ : IntermediateField K E) := by
        rwa [← mem_restrictScalars L, restrictScalars_bot_eq_self]
      rcases (square_descent_step hxj hjbot (algebraMap L K d)).mp
        ⟨u, v, by rw [← IsScalarTower.algebraMap_apply, hz2]⟩ with h | h
      · obtain ⟨t, ht, hsq⟩ := ih hx' hr' d ((isSquare_algebraMap_iff K d).mp h)
        exact ⟨t, ht.trans (Finset.subset_insert j s), hsq⟩
      · rw [← map_mul] at h
        obtain ⟨t, ht, hsq⟩ := ih hx' hr' (d * r j) ((isSquare_algebraMap_iff K _).mp h)
        refine ⟨insert j t, Finset.insert_subset_insert j ht, ?_⟩
        rwa [Finset.prod_insert fun h ↦ hjs (ht h), ← mul_assoc]

end IntermediateField

section

variable {L : Type*} [Field L]

/-- The group `Lˣ/(Lˣ)²` of nonzero square classes of the field `L`, written additively so that
it becomes a `ZMod 2`-module. -/
abbrev SquareClasses (L : Type*) [Field L] : Type _ :=
  Additive (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)

instance : Module (ZMod 2) (SquareClasses L) :=
  AddCommGroup.zmodModule (G := SquareClasses L) fun x ↦ by
    apply Additive.toMul.injective
    have hsq : Additive.toMul x ^ 2 = 1 := by
      refine QuotientGroup.induction_on (Additive.toMul x) fun u ↦ ?_
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
    simpa [two_nsmul, pow_two] using hsq

variable [DecidableEq L]

/-- The class of a nonzero field element in `Lˣ/(Lˣ)²` (junk value `0` at `r = 0`). -/
noncomputable def sqClass (r : L) : SquareClasses L :=
  if hr : r = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 r hr))

@[simp] theorem sqClass_zero : sqClass (0 : L) = 0 := by rw [sqClass, dif_pos rfl]

/-- The square class of `r` vanishes iff `r` is a square in `L` (at `r = 0` both sides hold). -/
theorem sqClass_eq_zero_iff (r : L) : sqClass r = 0 ↔ IsSquare r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [sqClass, dif_neg hr, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_one_iff,
    Units.mem_range_powMonoidHom_two_iff, Units.val_mk0]

@[simp] theorem sqClass_one : sqClass (1 : L) = 0 := (sqClass_eq_zero_iff 1).mpr IsSquare.one

theorem sqClass_mul {r t : L} (hr : r ≠ 0) (ht : t ≠ 0) :
    sqClass (r * t) = sqClass r + sqClass t := by
  rw [sqClass, sqClass, sqClass, dif_neg hr, dif_neg ht, dif_neg (mul_ne_zero hr ht),
    ← ofMul_mul, ← QuotientGroup.mk_mul]
  congr 2
  ext
  simp

theorem sqClass_prod {ι : Type*} {s : Finset ι} {r : ι → L} (hr : ∀ i ∈ s, r i ≠ 0) :
    sqClass (∏ i ∈ s, r i) = ∑ i ∈ s, sqClass (r i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      sqClass_mul (hr a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

/-- `sqClass` sends a `zpow` to a `ZMod 2`-scalar multiple (the class is written additively). -/
theorem sqClass_zpow (x : L) (k : ℤ) : sqClass (x ^ k) = k • sqClass x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [zero_zpow k hk, sqClass_zero, ← ofMul_one, ← ofMul_zpow, one_zpow]
  rw [sqClass, sqClass, dif_neg (zpow_ne_zero k hx), dif_neg hx,
    show Units.mk0 (x ^ k) (zpow_ne_zero k hx) = (Units.mk0 x hx) ^ k from
      Units.ext (by push_cast; simp),
    QuotientGroup.mk_zpow, ofMul_zpow]

/-- A product over `s` is a square iff the classes in `Lˣ/(Lˣ)²` sum to zero. -/
theorem isSquare_prod_iff_sum_sqClass_eq_zero {ι : Type*} {s : Finset ι} {r : ι → L}
    (hr : ∀ i ∈ s, r i ≠ 0) : IsSquare (∏ i ∈ s, r i) ↔ ∑ i ∈ s, sqClass (r i) = 0 := by
  rw [← sqClass_prod hr, sqClass_eq_zero_iff _]

/-- `sqClass` linearises a product of `zpow`s: `[∏ rᵢ ^ eᵢ] = ∑ eᵢ • [rᵢ]`. -/
theorem sqClass_prod_zpow {ι : Type*} {s : Finset ι} {r : ι → L} (e : ι → ℤ)
    (hr : ∀ i ∈ s, r i ≠ 0) :
    sqClass (∏ i ∈ s, r i ^ e i) = ∑ i ∈ s, e i • sqClass (r i) :=
  (sqClass_prod fun i hi ↦ zpow_ne_zero _ (hr i hi)).trans <|
    Finset.sum_congr rfl fun i _ ↦ sqClass_zpow (r i) (e i)

/-- The `𝔽₂`-relation submodule of a finite family of radicands `r : ι → L`: the kernel of
`ε ↦ ∑ ε i • [r i]` in `Lˣ/(Lˣ)²`. For nonzero radicands, `ε` is a relation iff
`∏_{i : ε i = 1} r i` is a square in `L` (see `mem_rootRelations`). -/
noncomputable def rootRelations {ι : Type*} [Fintype ι] (r : ι → L) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.ker (Fintype.linearCombination (ZMod 2) fun i ↦ sqClass (r i))

/-- `ε` is a root relation iff the product of the `r i` over `{i : ε i = 1}` is a square in
`L`. -/
theorem mem_rootRelations {ι : Type*} [Fintype ι] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    {ε : ι → ZMod 2} :
    ε ∈ rootRelations r ↔ IsSquare (∏ i ∈ Finset.univ.filter (fun i ↦ ε i = 1), r i) := by
  rw [rootRelations, LinearMap.mem_ker, Fintype.linearCombination_apply,
    sum_zmod_two_smul_eq_sum_filter (fun i ↦ sqClass (r i)) ε,
    ← isSquare_prod_iff_sum_sqClass_eq_zero (fun i _ ↦ hr i)]

/-- There are no nontrivial root relations iff the classes `[r i]` are `𝔽₂`-linearly
independent. -/
theorem rootRelations_eq_bot_iff {ι : Type*} [Fintype ι] (r : ι → L) :
    rootRelations r = ⊥ ↔ LinearIndependent (ZMod 2) fun i ↦ sqClass (r i) :=
  LinearMap.ker_eq_bot.trans linearIndependent_iff_injective_fintypeLinearCombination.symm

end

section

variable {L : Type*} [Field L] [DecidableEq L] {ι : Type*}

/-- The `𝔽₂`-relation submodule of the radicands `r i`, `i ∈ s`: the extension by zero of the
relation submodule of the family `r|_s` (see `mem_multiquadraticRelations`). -/
noncomputable def multiquadraticRelations (s : Finset ι) (r : ι → L) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.map (Function.ExtendByZero.linearMap (ZMod 2) (Subtype.val : ↥s → ι))
    (rootRelations fun i : ↥s ↦ r i.1)

/-- `ε ∈ multiquadraticRelations s r` iff `ε` is supported on `s` and
`∏_{i ∈ s, ε i = 1} r i` is a square in `L`. -/
theorem mem_multiquadraticRelations {s : Finset ι} {r : ι → L} (hr : ∀ i ∈ s, r i ≠ 0)
    {ε : ι → ZMod 2} :
    ε ∈ multiquadraticRelations s r
      ↔ (∀ i ∉ s, ε i = 0) ∧ IsSquare (∏ i ∈ s.filter (fun i ↦ ε i = 1), r i) := by
  have hrne (i : ↥s) : r i.1 ≠ 0 := hr i.1 i.2
  have hoff (v : ↥s → ZMod 2) {i : ι} (hi : i ∉ s) :
      Function.ExtendByZero.linearMap (ZMod 2) (Subtype.val : ↥s → ι) v i = 0 := by
    have hnot : ¬∃ a : ↥s, (a : ι) = i := fun ⟨y, hyi⟩ ↦ hi (hyi ▸ y.2)
    simp [Function.extend_apply' _ _ _ hnot]
  refine ⟨fun h ↦ ?_, fun ⟨hsupp, hsq⟩ ↦ ⟨fun i : ↥s ↦ ε i.1, ?_, ?_⟩⟩
  · obtain ⟨v, hv, rfl⟩ := h
    refine ⟨fun i hi ↦ hoff v hi, ?_⟩
    rw [← Finset.prod_filter_coe_sort]
    simpa using (mem_rootRelations hrne).mp hv
  · rwa [SetLike.mem_coe, mem_rootRelations hrne,
      Finset.prod_filter_coe_sort s (fun i ↦ ε i = 1) r]
  · funext i
    by_cases hi : i ∈ s
    · simpa using Subtype.val_injective.extend_apply (fun y : ↥s ↦ ε y.1) 0 ⟨i, hi⟩
    · rw [hoff _ hi, hsupp i hi]

/-- The indicator vector of `t ⊆ s` is a relation iff `∏_{i ∈ t} r i` is a square. -/
theorem indicator_mem_multiquadraticRelations_iff {s t : Finset ι} (hts : t ⊆ s) {r : ι → L}
    (hr : ∀ i ∈ s, r i ≠ 0) :
    (t : Set ι).indicator 1 ∈ multiquadraticRelations s r ↔ IsSquare (∏ i ∈ t, r i) := by
  classical
  rw [mem_multiquadraticRelations hr,
    show s.filter _ = t from Finset.ext fun i ↦ by simpa [Set.indicator_apply] using @hts i]
  exact and_iff_right fun i hi ↦ Set.indicator_of_notMem (mt (hts ·) hi) 1

end

/-- The relation space of an `ι`-indexed family has `𝔽₂`-dimension at most `|ι|`. -/
theorem rootRelations_finrank_le {ι : Type*} [Fintype ι] {L : Type*} [Field L] [DecidableEq L]
    (r : ι → L) :
    Module.finrank (ZMod 2) (rootRelations r) ≤ Fintype.card ι := by
  simpa [Module.finrank_pi] using Submodule.finrank_le (rootRelations r)

/-- `multiquadraticRelations s r` has the same `𝔽₂`-dimension as the relation space of the
restricted family `r|_s`. -/
theorem multiquadraticRelations_finrank_eq_rootRelations {L : Type*} [Field L] [DecidableEq L]
    {ι : Type*} (s : Finset ι) (r : ι → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s r)
      = Module.finrank (ZMod 2) (rootRelations fun i : ↥s ↦ r i.1) :=
  (Submodule.equivMapOfInjective _
    (Function.ExtendByZero.linearMap_injective _ Subtype.val_injective) _).symm.finrank_eq

/-- `multiquadraticRelations s r` has `𝔽₂`-dimension at most `|s|`. -/
theorem multiquadraticRelations_finrank_le {L : Type*} [Field L] [DecidableEq L] {ι : Type*}
    (s : Finset ι) (r : ι → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s r) ≤ s.card := by
  rw [multiquadraticRelations_finrank_eq_rootRelations, ← Fintype.card_coe s]
  exact rootRelations_finrank_le _

instance {L : Type*} [Field L] [DecidableEq L] {ι : Type*} (s : Finset ι) (r : ι → L) :
    Module.Finite (ZMod 2) (multiquadraticRelations s r) :=
  Module.Finite.equiv (Submodule.equivMapOfInjective _
    (Function.ExtendByZero.linearMap_injective _ Subtype.val_injective) _)

/-- For the full family, the relation submodule is `rootRelations`. -/
theorem multiquadraticRelations_univ {L : Type*} [Field L] [DecidableEq L] {ι : Type*} [Fintype ι]
    {r : ι → L} (hr : ∀ i, r i ≠ 0) : multiquadraticRelations Finset.univ r = rootRelations r := by
  ext ε
  simp [mem_multiquadraticRelations fun i _ ↦ hr i, mem_rootRelations hr]

/-- Intersecting `V (insert j s)` with the hyperplane `ε j = 0` recovers `V s`. -/
theorem multiquadraticRelations_insert_inf_ker_proj {L : Type*} [Field L] [DecidableEq L]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {j : ι} (hjs : j ∉ s) {r : ι → L}
    (hr : ∀ i ∈ insert j s, r i ≠ 0) :
    multiquadraticRelations (insert j s) r ⊓ LinearMap.ker (LinearMap.proj j)
      = multiquadraticRelations s r := by
  have hr' : ∀ i ∈ s, r i ≠ 0 := fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)
  ext ε
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    mem_multiquadraticRelations hr, mem_multiquadraticRelations hr']
  refine ⟨fun ⟨⟨hsupp, hsq⟩, hj⟩ ↦ ⟨fun i hi ↦ ?_, ?_⟩,
    fun ⟨hsupp, hsq⟩ ↦ ⟨⟨fun i hi ↦ hsupp i (mt Finset.mem_insert_of_mem hi), ?_⟩, hsupp j hjs⟩⟩
  · grind
  · simpa [Finset.filter_insert, hj] using hsq
  · simpa [Finset.filter_insert, hsupp j hjs] using hsq

/-- Some relation of `V (insert j s)` has `j`-coordinate `1` iff `r j` is a square in
`L(x i : i ∈ s)`. -/
theorem exists_mem_multiquadraticRelations_insert_iff {L : Type*} [Field L] [DecidableEq L]
    [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {j : ι} (hjs : j ∉ s) {x : ι → E} {r : ι → L}
    (hx : ∀ i ∈ insert j s, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i ∈ insert j s, r i ≠ 0) :
    (∃ ε ∈ multiquadraticRelations (insert j s) r, ε j = 1)
      ↔ IsSquare (algebraMap L (IntermediateField.adjoin L (x '' s)) (r j)) := by
  rw [IntermediateField.isSquare_algebraMap_iff,
    IntermediateField.square_descent (fun i hi ↦ hx i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hr i (Finset.mem_insert_of_mem hi))]
  refine ⟨fun ⟨ε, hε, hεj⟩ ↦ ?_, fun ⟨t, hts, hsq⟩ ↦ ?_⟩
  · obtain ⟨-, hsq⟩ := (mem_multiquadraticRelations hr).mp hε
    refine ⟨s.filter (fun i ↦ ε i = 1), Finset.filter_subset _ _, ?_⟩
    simpa [Finset.filter_insert, hεj,
      Finset.prod_insert fun h ↦ hjs (Finset.mem_of_mem_filter j h)] using hsq
  · refine ⟨((insert j t : Finset ι) : Set ι).indicator 1,
      (indicator_mem_multiquadraticRelations_iff (Finset.insert_subset_insert j hts) hr).mpr ?_,
      by simp⟩
    rwa [Finset.prod_insert fun h ↦ hjs (hts h)]

/-- Adjoining `x j` raises `dim V` by `1` when `r j` is a square in `L(x i : i ∈ s)`, and leaves
it unchanged otherwise. -/
theorem multiquadraticRelations_insert_finrank {L : Type*} [Field L] [DecidableEq L]
    [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {j : ι} (hjs : j ∉ s) {x : ι → E} {r : ι → L}
    (hx : ∀ i ∈ insert j s, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i ∈ insert j s, r i ≠ 0)
    [Decidable (IsSquare (algebraMap L (IntermediateField.adjoin L (x '' s)) (r j)))] :
    Module.finrank (ZMod 2) (multiquadraticRelations (insert j s) r)
      = Module.finrank (ZMod 2) (multiquadraticRelations s r)
        + (if IsSquare (algebraMap L (IntermediateField.adjoin L (x '' s)) (r j))
            then 1 else 0) := by
  set W := multiquadraticRelations (insert j s) r
  let evj : W →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj j).comp W.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker evj
  have hker : Module.finrank (ZMod 2) (LinearMap.ker evj)
      = Module.finrank (ZMod 2) (multiquadraticRelations s r) := by
    rw [← Submodule.finrank_map_subtype_eq W, LinearMap.ker_comp, Submodule.map_comap_subtype,
      multiquadraticRelations_insert_inf_ker_proj hjs hr]
  have hone : (1 : ZMod 2) ∈ LinearMap.range evj
      ↔ IsSquare (algebraMap L (IntermediateField.adjoin L (x '' s)) (r j)) := by
    rw [← exists_mem_multiquadraticRelations_insert_iff hjs hx hr]
    simp [evj, W]
  rcases Ideal.eq_bot_or_top (LinearMap.range evj) with h | h <;> rw [h] at hone hrn <;>
    simp only [finrank_bot, finrank_top, Module.finrank_self, Submodule.mem_bot, Submodule.mem_top,
      one_ne_zero, true_iff, false_iff] at hone hrn <;> grind

/-- Degree of a multiquadratic extension: `[L(x i : i ∈ s) : L] = 2 ^ (|s| - dim V)`, where `V` is
the `𝔽₂`-space of square relations among the radicands `r i = (x i)²`. -/
theorem multiquadratic_degree {L : Type*} [Field L] [DecidableEq L] [NeZero (2 : L)] {E : Type*}
    [Field E] [Algebra L E] {ι : Type*} {s : Finset ι} {x : ι → E} {r : ι → L}
    (hx : ∀ i ∈ s, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i ∈ s, r i ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (x '' s))
      = 2 ^ (s.card - Module.finrank (ZMod 2) (multiquadraticRelations s r)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    have hx' : ∀ i ∈ s, x i ^ 2 = algebraMap L E (r i) :=
      fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    have hr' : ∀ i ∈ s, r i ≠ 0 := fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)
    have hle := multiquadraticRelations_finrank_le s r
    rw [Finset.coe_insert, Set.image_insert_eq, IntermediateField.finrank_adjoin_insert,
      ih hx' hr', IntermediateField.finrank_adjoin_sqrt_eq
        ((hx j (Finset.mem_insert_self j s)).trans
          (IsScalarTower.algebraMap_apply L (IntermediateField.adjoin L (x '' s)) E (r j))),
      multiquadraticRelations_insert_finrank hjs hx hr, Finset.card_insert_of_notMem hjs]
    split_ifs
    · rw [mul_one, Nat.add_sub_add_right]
    · rw [add_zero, ← pow_succ, Nat.sub_add_comm hle]

/-- Family form of `multiquadratic_degree`: for a family `x : ι → E` of square roots of nonzero
radicands `r : ι → L`, the degree of `L(x i : i)` over `L` is `2 ^ (|ι| - dim rootRelations r)`.
No injectivity of `x` is needed: a repeated root counts once in `|ι|` and once in the
relations. -/
theorem multiquadratic_degree_family {L : Type*} [Field L] [DecidableEq L] [NeZero (2 : L)]
    {E : Type*} [Field E] [Algebra L E] {ι : Type*} [Fintype ι] {x : ι → E} {r : ι → L}
    (hx : ∀ i, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i, r i ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (Set.range x))
      = 2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (rootRelations r)) := by
  rw [← Set.image_univ, ← Finset.coe_univ, multiquadratic_degree (fun i _ ↦ hx i) (fun i _ ↦ hr i),
    multiquadraticRelations_univ hr, Finset.card_univ]

/-- If every `g ∈ G` acts on the radicands through a field automorphism, the relation space is
invariant under the coordinate action. -/
theorem rootRelations_invariant {G : Type*} [Group G] {ι : Type*} [Fintype ι] [MulAction G ι]
    {L : Type*} [Field L] [DecidableEq L] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    (hcompat : ∀ g : G, ∃ φ : L ≃+* L, ∀ j, φ (r j) = r (g • j)) :
    ∀ (g : G) (v : ι → ZMod 2), v ∈ rootRelations r → (fun i ↦ v (g⁻¹ • i)) ∈ rootRelations r := by
  classical
  intro g v hv
  rw [mem_rootRelations hr] at hv ⊢
  obtain ⟨φ, hφ⟩ := hcompat g
  rw [show (∏ i ∈ Finset.univ.filter (fun i ↦ v (g⁻¹ • i) = 1), r i)
      = ∏ j ∈ Finset.univ.filter (fun j ↦ v j = 1), r (g • j) from by
    apply Finset.prod_nbij' (fun i ↦ g⁻¹ • i) (fun j ↦ g • j) <;>
      simp [inv_smul_smul, smul_inv_smul],
    Finset.prod_congr rfl (fun j _ ↦ (hφ j).symm), ← map_prod]
  exact IsSquare.map φ hv

/-- For a finite `2`-group acting pretransitively with automorphism-compatible radicands, a
nonzero relation space contains the all-ones vector. -/
theorem rootRelations_all_ones {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {ι : Type*} [Fintype ι] [Nonempty ι] [MulAction G ι] [MulAction.IsPretransitive G ι]
    {L : Type*} [Field L] [DecidableEq L] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    (hcompat : ∀ g : G, ∃ φ : L ≃+* L, ∀ j, φ (r j) = r (g • j)) (hne : rootRelations r ≠ ⊥) :
    (fun _ ↦ 1) ∈ rootRelations r :=
invariant_submodule_all_ones hG (rootRelations r) (rootRelations_invariant hr hcompat) hne

/-- The all-ones vector is a relation iff `∏ i, r i` is a square in `L`. -/
theorem all_ones_mem_rootRelations {ι : Type*} [Fintype ι] {L : Type*} [Field L] [DecidableEq L]
    {r : ι → L} (hr : ∀ i, r i ≠ 0) :
    (fun _ ↦ (1 : ZMod 2)) ∈ rootRelations r ↔ IsSquare (∏ i, r i) := by
  classical
  rw [mem_rootRelations hr, Finset.filter_true_of_mem (fun i _ ↦ rfl)]

section AdjoinSquareRoots

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An `F`-automorphism fixes or negates any square root of an element of `F`. -/
lemma apply_eq_or_eq_neg_of_sq_eq_algebraMap (φ : E ≃ₐ[F] E) {y : E} {q : F}
    (hy : y ^ 2 = algebraMap F E q) : φ y = y ∨ φ y = -y :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hy, AlgEquiv.commutes])

/-- Such a subfield has exponent `2`: every `F`-automorphism of it is an involution. -/
lemma algEquiv_adjoin_sq_eq_one {t : Finset E}
    (ht : ∀ y ∈ t, ∃ q : F, y ^ 2 = algebraMap F E q)
    (τ : ↥(IntermediateField.adjoin F (t : Set E)) ≃ₐ[F]
          ↥(IntermediateField.adjoin F (t : Set E))) :
    τ ^ 2 = 1 := by
  have hgen (x : E) (hx : x ∈ (t : Set E)) :
      (τ ^ 2) ⟨x, IntermediateField.subset_adjoin F _ hx⟩
        = ⟨x, IntermediateField.subset_adjoin F _ hx⟩ := by
    obtain ⟨q, hq⟩ := ht x hx
    set g : ↥(IntermediateField.adjoin F (t : Set E)) :=
      ⟨x, IntermediateField.subset_adjoin F _ hx⟩ with hg
    have hgq : g ^ 2 = algebraMap F ↥(IntermediateField.adjoin F (t : Set E)) q := by
      apply Subtype.ext
      push_cast
      simpa [hg] using hq
    rcases apply_eq_or_eq_neg_of_sq_eq_algebraMap τ hgq with h | h
    · rw [pow_two, AlgEquiv.mul_apply, h, h]
    · rw [pow_two, AlgEquiv.mul_apply, h, map_neg, h, neg_neg]
  have key : (τ ^ 2).toAlgHom = AlgHom.id F _ := IntermediateField.adjoin_algHom_ext F hgen
  ext z
  simpa using DFunLike.congr_fun key z
variable [Normal F E]

/-- A subfield of `E` generated by square roots of elements of `F` is Galois over `F`. -/
lemma isGalois_adjoin_of_sq_eq_algebraMap [PerfectField F] {t : Finset E}
    (ht : ∀ y ∈ t, ∃ q : F, y ^ 2 = algebraMap F E q) :
    IsGalois F ↥(IntermediateField.adjoin F (t : Set E)) := by
  set K := IntermediateField.adjoin F (t : Set E) with hK
  have hmaple (σ : E ≃ₐ[F] E) : IntermediateField.map (σ : E →ₐ[F] E) K ≤ K := by
    rw [hK, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro x ⟨y, hyt, rfl⟩
    obtain ⟨q, hq⟩ := ht y hyt
    have hy_mem := IntermediateField.subset_adjoin F (t : Set E) hyt
    rcases apply_eq_or_eq_neg_of_sq_eq_algebraMap σ hq with h | h
    · simpa [h] using hy_mem
    · simpa [h] using neg_mem hy_mem
  have : Normal F ↥K := IntermediateField.normal_iff_forall_map_le'.mpr hmaple
  have := Algebra.IsAlgebraic.isSeparable_of_perfectField (K := F) (L := ↥K)
  exact IsGalois.mk

end AdjoinSquareRoots
