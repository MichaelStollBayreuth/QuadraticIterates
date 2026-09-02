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

end

section

variable {L : Type*} [Field L] [DecidableEq L] {E : Type*} [DecidableEq E]

/-- The `𝔽₂`-relation submodule of a multiquadratic extension: the extension by zero of the
relation submodule of the family `c|_s` (see `mem_multiquadraticRelations`). -/
noncomputable def multiquadraticRelations (s : Finset E) (c : E → L) :
    Submodule (ZMod 2) (E → ZMod 2) :=
  Submodule.map (Function.ExtendByZero.linearMap (ZMod 2) (Subtype.val : ↥s → E))
    (rootRelations fun x : ↥s ↦ c x.1)

/-- `ε ∈ multiquadraticRelations s c` iff `ε` is supported on `s` and
`∏_{x ∈ s, ε x = 1} c x` is a square in `L`. -/
theorem mem_multiquadraticRelations {s : Finset E} {c : E → L} (hc : ∀ x ∈ s, c x ≠ 0)
    {ε : E → ZMod 2} :
    ε ∈ multiquadraticRelations s c
      ↔ (∀ x ∉ s, ε x = 0) ∧ IsSquare (∏ x ∈ s.filter (fun x ↦ ε x = 1), c x) := by
  have hrne (x : ↥s) : c x.1 ≠ 0 := hc x.1 x.2
  have hoff (v : ↥s → ZMod 2) {x : E} (hx : x ∉ s) :
      Function.ExtendByZero.linearMap (ZMod 2) (Subtype.val : ↥s → E) v x = 0 := by
    have hnot : ¬∃ a : ↥s, (a : E) = x := fun ⟨y, hyx⟩ ↦ hx (hyx ▸ y.2)
    simp [Function.extend_apply' _ _ _ hnot]
  refine ⟨fun h ↦ ?_, fun ⟨hsupp, hsq⟩ ↦ ⟨fun x : ↥s ↦ ε x.1, ?_, ?_⟩⟩
  · obtain ⟨v, hv, rfl⟩ := h
    refine ⟨fun x hx ↦ hoff v hx, ?_⟩
    rw [← Finset.prod_filter_coe_sort]
    simpa using (mem_rootRelations hrne).mp hv
  · rwa [SetLike.mem_coe, mem_rootRelations hrne,
      Finset.prod_filter_coe_sort s (fun x ↦ ε x = 1) c]
  · funext x
    by_cases hx : x ∈ s
    · simpa using Subtype.val_injective.extend_apply (fun y : ↥s ↦ ε y.1) 0 ⟨x, hx⟩
    · rw [hoff _ hx, hsupp x hx]

/-- The indicator vector of `t ⊆ s` is a relation iff `∏_{x ∈ t} c x` is a square. -/
theorem indicator_mem_multiquadraticRelations_iff {s t : Finset E} (hts : t ⊆ s) {c : E → L}
    (hc : ∀ x ∈ s, c x ≠ 0) :
    (t : Set E).indicator 1 ∈ multiquadraticRelations s c ↔ IsSquare (∏ x ∈ t, c x) := by
  classical
  rw [mem_multiquadraticRelations hc,
    show s.filter _ = t from Finset.ext fun x ↦ by simpa [Set.indicator_apply] using @hts x]
  exact and_iff_right fun x hx ↦ Set.indicator_of_notMem (mt (hts ·) hx) 1

end

open IntermediateField in
/-- Adjoining a square root of `c` gives degree `1` if `c` is already a square in `L`, and `2`
otherwise. -/
theorem finrank_adjoin_sqrt_eq {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c) [Decidable (IsSquare c)] :
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
theorem IntermediateField.finrank_adjoin_insert_of_not_isSquare {L : Type*} [Field L] {E : Type*}
    [Field E] [Algebra L E] {S : Set E} {w : E} {c : L} (hw : w ^ 2 = algebraMap L E c)
    (h : ¬ IsSquare (algebraMap L (adjoin L S) c)) :
    Module.finrank L (adjoin L (insert w S)) = 2 * Module.finrank L (adjoin L S) := by
  classical
  rw [finrank_adjoin_insert,
    finrank_adjoin_sqrt_eq (hw.trans (IsScalarTower.algebraMap_apply L (adjoin L S) E c)),
    if_neg h, mul_comm]

/-- If `p + q·x = 0` with `p, q ∈ L` and `q ≠ 0`, then `x` lies in the base field. -/
theorem IntermediateField.mem_bot_of_add_mul_eq_zero {L : Type*} [Field L] {E : Type*} [Field E]
    [Algebra L E] {x : E} {p q : L} (hq : q ≠ 0) (h : algebraMap L E p + algebraMap L E q * x = 0) :
    x ∈ (⊥ : IntermediateField L E) := by
  refine mem_bot.mpr ⟨-p / q, ?_⟩
  rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero _).mpr hq)]
  linear_combination -h

/-- One-step square descent: over `L(x)` with `x² = c` and `x ∉ L`, the image of `d ∈ L` is a
square iff `d` or `d · c` is a square in `L`. -/
theorem square_descent_step {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*} [Field E]
    [Algebra L E] {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c)
    (hx : x ∉ (⊥ : IntermediateField L E)) (d : L) :
    (∃ u v : L, algebraMap L E d = (algebraMap L E u + algebraMap L E v * x) ^ 2)
      ↔ (IsSquare d ∨ IsSquare (d * c)) := by
  refine ⟨fun ⟨u, v, huv⟩ ↦ ?_,
    fun h ↦ h.elim (fun ⟨w, hw⟩ ↦ ⟨w, 0, by simp [hw, sq]⟩) fun ⟨w, hw⟩ ↦ ?_⟩
  · have h : algebraMap L E (u ^ 2 + v ^ 2 * c - d) + algebraMap L E (2 * (u * v)) * x = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination -huv - (algebraMap L E v) ^ 2 * hc
    have hq : 2 * (u * v) = 0 :=
      by_contra fun hq ↦ hx (IntermediateField.mem_bot_of_add_mul_eq_zero hq h)
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
theorem isSquare_algebraMap_iff {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    (K : IntermediateField L E) (e : L) :
    IsSquare (algebraMap L ↥K e) ↔ ∃ z ∈ K, z ^ 2 = algebraMap L E e := by
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, w.2, ?_⟩, fun ⟨z, hz, hz2⟩ ↦ ⟨⟨z, hz⟩, Subtype.ext ?_⟩⟩
  · simpa [sq] using congrArg Subtype.val hw.symm
  · simpa [sq] using hz2.symm

/-- If `w` is a square root of `algebraMap e` lying outside an intermediate field `K`, then `e`
is not a square in `K`. -/
theorem not_isSquare_algebraMap_of_sqrt_notMem {L : Type*} [Field L] {E : Type*} [Field E]
    [Algebra L E] {K : IntermediateField L E} {e : L} {w : E}
    (hw : w ^ 2 = algebraMap L E e) (hwK : w ∉ K) :
    ¬ IsSquare (algebraMap L ↥K e) := fun h ↦ by
  obtain ⟨z, hzK, hz⟩ := (isSquare_algebraMap_iff K e).mp h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hw.trans hz.symm) with rfl | rfl
  exacts [hwK hzK, hwK (neg_mem hzK)]

/-- An element of the base field is a square in the bottom intermediate field iff it is a square
in the base field. -/
theorem isSquare_algebraMap_bot_iff {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    (x : L) :
    IsSquare (algebraMap L ↥(⊥ : IntermediateField L E) x) ↔ IsSquare x := by
  rw [← IntermediateField.botEquiv_symm]
  exact ⟨fun h ↦ by simpa using h.map (IntermediateField.botEquiv L E), fun h ↦ h.map _⟩

open IntermediateField Polynomial in
/-- An element of the simple extension `F(y)` with `y² ∈ F` is exactly an `F`-linear combination
`u + v · y`. -/
theorem mem_adjoin_simple_sq {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {y : E}
    {a : F} (hy : y ^ 2 = algebraMap F E a) {z : E} :
    z ∈ F⟮y⟯ ↔ ∃ u v : F, z = algebraMap F E u + algebraMap F E v * y := by
  classical
  have hmonic : (X ^ 2 - C a).Monic := monic_X_pow_sub_C a two_ne_zero
  have hroot : aeval y (X ^ 2 - C a) = 0 := by simp [hy]
  rw [← mem_toSubalgebra,
    adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.isAlgebraic ⟨_, hmonic, hroot⟩),
    ← Subalgebra.mem_toSubmodule, ← Submodule.span_range_natDegree_eq_adjoin hmonic hroot,
    natDegree_X_pow_sub_C, show Finset.image (y ^ ·) (Finset.range 2) = {1, y} by
      simp [show Finset.range 2 = {0, 1} by decide],
    Finset.coe_pair, Submodule.mem_span_pair]
  simp [Algebra.smul_def, eq_comm]

/-- Induction step of `square_descent` when the new radical `y` already lies in `L(s')`: adjoining
`y` changes nothing, so the descent set is unchanged up to `⊆ insert y s'`. -/
private theorem square_descent_insert_of_mem {L : Type*} [Field L] {E : Type*} [Field E]
    [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} {c : E → L}
    (hs : ∀ z ∈ insert y s', z ^ 2 = algebraMap L E (c z)) (hc : ∀ z ∈ insert y s', c z ≠ 0)
    (hyK : y ∈ IntermediateField.adjoin L (s' : Set E))
    (ih : ∀ e : L, (∃ z ∈ IntermediateField.adjoin L (s' : Set E), z ^ 2 = algebraMap L E e)
        ↔ ∃ t ⊆ s', IsSquare (e * ∏ i ∈ t, c i)) (d : L) :
    (∃ z ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin L (s' : Set E))) ({y} : Set E),
        z ^ 2 = algebraMap L E d)
      ↔ ∃ t ⊆ insert y s', IsSquare (d * ∏ i ∈ t, c i) := by
  set K := IntermediateField.adjoin L (s' : Set E) with hK
  have hmem (z : E) : z ∈ IntermediateField.adjoin (↥K) ({y} : Set E) ↔ z ∈ K := by
    have hadj_eq : SetLike.coe (IntermediateField.adjoin (↥K) ({y} : Set E)) = SetLike.coe K := by
      rw [show IntermediateField.adjoin (↥K) ({y} : Set E) = ⊥ from
          IntermediateField.adjoin_simple_eq_bot_iff.mpr
            (IntermediateField.mem_bot.mpr ⟨⟨y, hyK⟩, rfl⟩),
        IntermediateField.coe_bot, hK,
        IntermediateField.adjoin_eq_range_algebraMap_adjoin L (s' : Set E)]
    simpa [SetLike.mem_coe] using
      (show z ∈ (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) ↔ z ∈ (K : Set E)
        by rw [hadj_eq])
  have hgenK : ∀ i ∈ insert y s', i ∈ K := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hyK
    · rw [hK]; exact IntermediateField.subset_adjoin L _ hi'
  simp only [hmem]
  refine ⟨fun hz ↦ (ih d).mp hz |>.imp fun t ⟨ht, hsq⟩ ↦
    ⟨ht.trans (Finset.subset_insert y s'), hsq⟩, ?_⟩
  rintro ⟨t, ht, r, hr⟩
  set P : E := ∏ i ∈ t, i with hP
  have hPK : P ∈ K := Subalgebra.prod_mem K.toSubalgebra fun i hi ↦ hgenK i (ht hi)
  have hPsq : algebraMap L E (∏ i ∈ t, c i) = P ^ 2 := by
    rw [map_prod, hP, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i hi ↦ (hs i (ht hi)).symm
  have hPne : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    exact fun i hi hzero ↦ hc i (ht hi)
      ((map_eq_zero (algebraMap L E)).mp (by rw [← hs i (ht hi), hzero]; ring))
  refine ⟨algebraMap L E r / P, div_mem (IntermediateField.algebraMap_mem K r) hPK, ?_⟩
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hPne)]
  rw [← hPsq, ← map_mul, ← map_pow, hr]; ring_nf

/-- Induction step of `square_descent` when the new radical `y` is genuinely new (`y ∉ L(s')`):
one degree-`2` step via `square_descent_step`, tracking whether `y` enters the descent set. -/
private theorem square_descent_insert_of_notMem {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*}
    [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hy : y ^ 2 = algebraMap L E (c y)) (hyK : y ∉ IntermediateField.adjoin L (s' : Set E))
    (hbridge : ∀ e : L, IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) e)
        ↔ ∃ t ⊆ s', IsSquare (e * ∏ i ∈ t, c i)) (d : L) :
    (∃ z ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin L (s' : Set E))) ({y} : Set E),
        z ^ 2 = algebraMap L E d)
      ↔ ∃ t ⊆ insert y s', IsSquare (d * ∏ i ∈ t, c i) := by
  set K := IntermediateField.adjoin L (s' : Set E) with hK
  have : NeZero (2 : ↥K) := ⟨by
    rw [← map_ofNat (algebraMap L ↥K) 2]
    exact (map_ne_zero_iff _ (algebraMap L ↥K).injective).mpr two_ne_zero⟩
  have hcyK : y ^ 2 = algebraMap (↥K) E (algebraMap L (↥K) (c y)) := by
    rw [hy, ← IsScalarTower.algebraMap_apply L (↥K) E]
  have hynotbot : y ∉ (⊥ : IntermediateField (↥K) E) := by
    rw [IntermediateField.mem_bot]; rintro ⟨w, hw⟩; exact hyK (hw ▸ w.2)
  have hstep := square_descent_step (L := ↥K) (E := E) hcyK hynotbot (algebraMap L (↥K) d)
  have hLbridge : (∃ u v : ↥K, algebraMap (↥K) E (algebraMap L (↥K) d)
        = (algebraMap (↥K) E u + algebraMap (↥K) E v * y) ^ 2)
      ↔ (∃ z ∈ IntermediateField.adjoin (↥K) ({y} : Set E), z ^ 2 = algebraMap L E d) := by
    rw [← IsScalarTower.algebraMap_apply L (↥K) E]
    simp only [mem_adjoin_simple_sq hcyK]
    exact ⟨fun ⟨u, v, huv⟩ ↦ ⟨_, ⟨u, v, rfl⟩, huv.symm⟩,
      fun ⟨_, ⟨u, v, hz⟩, hz2⟩ ↦ ⟨u, v, (hz ▸ hz2).symm⟩⟩
  rw [← hLbridge, hstep, ← map_mul, hbridge d, hbridge (d * c y)]
  constructor
  · rintro (⟨t, ht, hsq⟩ | ⟨t, ht, hsq⟩)
    · exact ⟨t, ht.trans (Finset.subset_insert y s'), hsq⟩
    · refine ⟨insert y t, Finset.insert_subset_insert y ht, ?_⟩
      rw [Finset.prod_insert fun h ↦ hys (ht h)]; simpa [mul_assoc] using hsq
  · rintro ⟨t, ht, hsq⟩
    by_cases hyt : y ∈ t
    · refine .inr ⟨t.erase y, fun a ha ↦ ?_, ?_⟩
      · rcases Finset.mem_insert.mp (ht (Finset.mem_of_mem_erase ha)) with rfl | h
        · exact absurd rfl (Finset.mem_erase.mp ha).1
        · exact h
      · rw [show ∏ i ∈ t, c i = c y * ∏ i ∈ t.erase y, c i from by
          rw [← Finset.prod_insert (Finset.notMem_erase y t), Finset.insert_erase hyt]] at hsq
        simpa [mul_assoc] using hsq
    · refine .inl ⟨t, fun a ha ↦ ?_, hsq⟩
      rcases Finset.mem_insert.mp (ht ha) with rfl | h
      · exact absurd ha hyt
      · exact h

/-- Iterated square descent: some element of `L(s)` squares to `d` iff `d * ∏_{y ∈ t} c y` is a
square in `L` for some subset `t ⊆ s`. -/
theorem square_descent {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E]
    {s : Finset E} {c : E → L} (hs : ∀ y ∈ s, y ^ 2 = algebraMap L E (c y))
    (hc : ∀ y ∈ s, c y ≠ 0) (d : L) :
    (∃ z : E, z ∈ IntermediateField.adjoin L (s : Set E) ∧ z ^ 2 = algebraMap L E d)
      ↔ (∃ t : Finset E, t ⊆ s ∧ IsSquare (d * ∏ y ∈ t, c y)) := by
  classical
  revert hs hc d
  induction s using Finset.induction_on with
  | empty =>
    intro hs hc d
    simp only [Finset.coe_empty, IntermediateField.adjoin_empty]
    constructor
    · rintro ⟨z, hz, hz2⟩
      rw [IntermediateField.mem_bot] at hz
      obtain ⟨w, rfl⟩ := hz
      refine ⟨∅, by simp, w, ?_⟩
      apply (algebraMap L E).injective
      rw [Finset.prod_empty, mul_one, ← hz2]; push_cast; ring
    · rintro ⟨t, ht, hsq⟩
      obtain rfl := Finset.subset_empty.mp ht
      simp only [Finset.prod_empty, mul_one] at hsq
      obtain ⟨w, hw⟩ := hsq
      refine ⟨algebraMap L E w, IntermediateField.algebraMap_mem _ _, ?_⟩
      rw [hw]; push_cast; ring
  | insert y s' hys ih =>
    intro hs hc d
    have hy : y ^ 2 = algebraMap L E (c y) := hs y (Finset.mem_insert_self y s')
    have ih' := ih (fun z hz ↦ hs z (Finset.mem_insert_of_mem hz))
      (fun z hz ↦ hc z (Finset.mem_insert_of_mem hz))
    set K := IntermediateField.adjoin L (s' : Set E) with hK
    have hset : (IntermediateField.adjoin L ((insert y s' : Finset E) : Set E) : Set E)
        = (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) := by
      have h2 : (IntermediateField.adjoin L ((s' : Set E) ∪ ({y} : Set E)) : Set E)
          = (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) := by
        rw [← IntermediateField.adjoin_adjoin_left L (s' : Set E) ({y} : Set E)]; rfl
      rw [← h2]; congr 1; rw [Finset.coe_insert, Set.insert_eq, Set.union_comm]
    have hmemK (z : E) : z ∈ IntermediateField.adjoin L ((insert y s' : Finset E) : Set E)
        ↔ z ∈ IntermediateField.adjoin (↥K) ({y} : Set E) := by
      rw [← SetLike.mem_coe, hset, SetLike.mem_coe]
    simp only [hmemK]
    by_cases hyK : y ∈ K
    · exact square_descent_insert_of_mem hs hc hyK ih' d
    · have hbridge (e : L) : IsSquare (algebraMap L (↥K) e)
          ↔ ∃ t ⊆ s', IsSquare (e * ∏ y ∈ t, c y) :=
        (isSquare_algebraMap_iff K e).trans (ih' e)
      exact square_descent_insert_of_notMem hys hy hyK hbridge d

/-- The relation space of an `ι`-indexed family has `𝔽₂`-dimension at most `|ι|`. -/
theorem rootRelations_finrank_le {ι : Type*} [Fintype ι] {L : Type*} [Field L] [DecidableEq L]
    (r : ι → L) :
    Module.finrank (ZMod 2) (rootRelations r) ≤ Fintype.card ι := by
  simpa [Module.finrank_pi] using Submodule.finrank_le (rootRelations r)

/-- `multiquadraticRelations s c` has the same `𝔽₂`-dimension as the relation space of the
restricted family `c|_s`. -/
theorem multiquadraticRelations_finrank_eq_rootRelations {L : Type*} [Field L] [DecidableEq L]
    {E : Type*} (s : Finset E) (c : E → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s c)
      = Module.finrank (ZMod 2) (rootRelations fun x : ↥s ↦ c x.1) :=
  (Submodule.equivMapOfInjective _
    (Function.ExtendByZero.linearMap_injective _ Subtype.val_injective) _).symm.finrank_eq

/-- `multiquadraticRelations s c` has `𝔽₂`-dimension at most `|s|`. -/
theorem multiquadraticRelations_finrank_le {L : Type*} [Field L] [DecidableEq L] {E : Type*}
    (s : Finset E) (c : E → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s c) ≤ s.card := by
  rw [multiquadraticRelations_finrank_eq_rootRelations, ← Fintype.card_coe s]
  exact rootRelations_finrank_le _

instance {L : Type*} [Field L] [DecidableEq L] {E : Type*} (s : Finset E) (c : E → L) :
    Module.Finite (ZMod 2) (multiquadraticRelations s c) :=
  Module.Finite.equiv (Submodule.equivMapOfInjective _
    (Function.ExtendByZero.linearMap_injective _ Subtype.val_injective) _)

/-- Intersecting `V (insert y s')` with the hyperplane `ε y = 0` recovers `V s'`. -/
theorem multiquadraticRelations_insert_inf_ker_proj {L : Type*} [Field L] [DecidableEq L]
    {E : Type*} [DecidableEq E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hc : ∀ x ∈ insert y s', c x ≠ 0) :
    multiquadraticRelations (insert y s') c ⊓ LinearMap.ker (LinearMap.proj y)
      = multiquadraticRelations s' c := by
  have hc' : ∀ x ∈ s', c x ≠ 0 := fun x hx ↦ hc x (Finset.mem_insert_of_mem hx)
  ext ε
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    mem_multiquadraticRelations hc, mem_multiquadraticRelations hc']
  refine ⟨fun ⟨⟨hsupp, hsq⟩, hy⟩ ↦ ⟨fun x hx ↦ ?_, ?_⟩,
    fun ⟨hsupp, hsq⟩ ↦ ⟨⟨fun x hx ↦ hsupp x (mt Finset.mem_insert_of_mem hx), ?_⟩, hsupp y hys⟩⟩
  · grind
  · simpa [Finset.filter_insert, hy] using hsq
  · simpa [Finset.filter_insert, hsupp y hys] using hsq

/-- Some relation of `V (insert y s')` has `y`-coordinate `1` iff `c y` is a square in
`L(s')`. -/
theorem multiquadraticRelations_ycoord {L : Type*} [Field L] [DecidableEq L] [NeZero (2 : L)]
    {E : Type*} [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} (hys : y ∉ s')
    {c : E → L} (hs : ∀ x ∈ insert y s', x ^ 2 = algebraMap L E (c x))
    (hc : ∀ x ∈ insert y s', c x ≠ 0) :
    (∃ ε : E → ZMod 2, ε ∈ multiquadraticRelations (insert y s') c ∧ ε y = 1)
      ↔ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y)) := by
  rw [isSquare_algebraMap_iff, square_descent (fun x hx ↦ hs x (Finset.mem_insert_of_mem hx))
    (fun x hx ↦ hc x (Finset.mem_insert_of_mem hx))]
  refine ⟨fun ⟨ε, hε, hεy⟩ ↦ ?_, fun ⟨t, hts, hsq⟩ ↦ ?_⟩
  · obtain ⟨-, hsq⟩ := (mem_multiquadraticRelations hc).mp hε
    refine ⟨s'.filter (fun x ↦ ε x = 1), Finset.filter_subset _ _, ?_⟩
    simpa [Finset.filter_insert, hεy,
      Finset.prod_insert fun h ↦ hys (Finset.mem_of_mem_filter y h)] using hsq
  · refine ⟨((insert y t : Finset E) : Set E).indicator 1,
      (indicator_mem_multiquadraticRelations_iff (Finset.insert_subset_insert y hts) hc).mpr ?_,
      by simp⟩
    rwa [Finset.prod_insert fun h ↦ hys (hts h)]

/-- Adjoining `y` raises `dim V` by `1` when `c y` is a square in `L(s')`, and leaves it
unchanged otherwise. -/
theorem multiquadraticRelations_insert_finrank {L : Type*} [Field L] [DecidableEq L]
    [NeZero (2 : L)] {E : Type*} [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E}
    (hys : y ∉ s') {c : E → L} (hs : ∀ x ∈ insert y s', x ^ 2 = algebraMap L E (c x))
    (hc : ∀ x ∈ insert y s', c x ≠ 0)
    [Decidable (IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y)))] :
    Module.finrank (ZMod 2) (multiquadraticRelations (insert y s') c)
      = Module.finrank (ZMod 2) (multiquadraticRelations s' c)
        + (if IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y))
            then 1 else 0) := by
  set W := multiquadraticRelations (insert y s') c
  let evy : W →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj y).comp W.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker evy
  have hker : Module.finrank (ZMod 2) (LinearMap.ker evy)
      = Module.finrank (ZMod 2) (multiquadraticRelations s' c) := by
    rw [← Submodule.finrank_map_subtype_eq W, LinearMap.ker_comp, Submodule.map_comap_subtype,
      multiquadraticRelations_insert_inf_ker_proj hys hc]
  have hone : (1 : ZMod 2) ∈ LinearMap.range evy
      ↔ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y)) := by
    rw [← multiquadraticRelations_ycoord hys hs hc]
    simp [evy, W]
  rcases Ideal.eq_bot_or_top (LinearMap.range evy) with h | h <;> rw [h] at hone hrn <;>
    simp only [finrank_bot, finrank_top, Module.finrank_self, Submodule.mem_bot, Submodule.mem_top,
      one_ne_zero, true_iff, false_iff] at hone hrn <;> grind

/-- Degree of a multiquadratic extension: `[L(s) : L] = 2 ^ (|s| - dim V)`, where `V` is the
`𝔽₂`-space of square relations among the radicands. -/
theorem multiquadratic_degree {L : Type*} [Field L] [DecidableEq L] [NeZero (2 : L)] {E : Type*}
    [Field E] [Algebra L E] {s : Finset E} {c : E → L}
    (hs : ∀ x ∈ s, x ^ 2 = algebraMap L E (c x)) (hc : ∀ x ∈ s, c x ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (s : Set E))
      = 2 ^ (s.card - Module.finrank (ZMod 2) (multiquadraticRelations s c)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert y s' hys ih =>
    have hs' : ∀ x ∈ s', x ^ 2 = algebraMap L E (c x) :=
      fun x hx ↦ hs x (Finset.mem_insert_of_mem hx)
    have hc' : ∀ x ∈ s', c x ≠ 0 := fun x hx ↦ hc x (Finset.mem_insert_of_mem hx)
    have hle := multiquadraticRelations_finrank_le s' c
    rw [Finset.coe_insert, IntermediateField.finrank_adjoin_insert, ih hs' hc',
      finrank_adjoin_sqrt_eq ((hs y (Finset.mem_insert_self y s')).trans
        (IsScalarTower.algebraMap_apply L (IntermediateField.adjoin L (s' : Set E)) E (c y))),
      multiquadraticRelations_insert_finrank hys hs hc, Finset.card_insert_of_notMem hys]
    split_ifs
    · rw [mul_one, Nat.add_sub_add_right]
    · rw [add_zero, ← pow_succ, Nat.sub_add_comm hle]

/-- The dimension of the relation space is invariant under reindexing the family by a
bijection. -/
theorem rootRelations_finrank_reindex {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {L : Type*} [Field L] [DecidableEq L] (r : ι → L) (hr : ∀ i, r i ≠ 0) {r' : κ → L}
    (hr' : ∀ j, r' j ≠ 0) (e : ι ≃ κ) (he : ∀ i, r' (e i) = r i) :
    Module.finrank (ZMod 2) (rootRelations r) = Module.finrank (ZMod 2) (rootRelations r') := by
  classical
  set φ := LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : ι ↦ ZMod 2) e
  have hprod (ε : ι → ZMod 2) : (∏ k ∈ Finset.univ.filter
      (fun k ↦ (φ ε) k = 1), r' k) = ∏ i ∈ Finset.univ.filter (fun i ↦ ε i = 1), r i := by
    refine Finset.prod_equiv e.symm (fun k ↦ ?_) (fun k _ ↦ ?_)
    · simp [Finset.mem_filter, φ, LinearEquiv.piCongrLeft'_apply]
    · rw [← he (e.symm k), Equiv.apply_symm_apply e k]
  have hmap : Submodule.map (φ : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (rootRelations r)
      = rootRelations r' := by
    ext η
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨ε, hε, rfl⟩
      rw [mem_rootRelations hr']
      rw [mem_rootRelations hr] at hε
      simp only [LinearEquiv.coe_coe]
      rwa [hprod ε]
    · intro hη
      refine ⟨φ.symm η, ?_, by simp⟩
      rw [mem_rootRelations hr, ← hprod (φ.symm η)]
      rw [mem_rootRelations hr'] at hη
      simpa using hη
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- Family form of `multiquadratic_degree`: for an injective family `x : ι → E` of square roots
of nonzero radicands `r : ι → L`, the degree of `L(x i : i)` over `L` is
`2 ^ (|ι| - dim rootRelations r)`. -/
theorem multiquadratic_degree_family {ι : Type*} [Fintype ι] {L : Type*} [Field L] [DecidableEq L]
    [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E] {x : ι → E}
    (hxinj : Function.Injective x) {r : ι → L} (hx : ∀ i, x i ^ 2 = algebraMap L E (r i))
    (hr : ∀ i, r i ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (Set.range x))
      = 2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (rootRelations r)) := by
  classical
  set s : Finset E := Finset.univ.image x with hs
  have hrange : (s : Set E) = Set.range x := by rw [hs]; simp [Finset.coe_image]
  have hscard : s.card = Fintype.card ι := by
    rw [hs, Finset.card_image_of_injective _ hxinj, Finset.card_univ]
  set cf : E → L := Function.extend x r 1 with hcf
  have hcf_x (i) : cf (x i) = r i := hxinj.extend_apply _ _ i
  have hs_sq : ∀ y ∈ s, y ^ 2 = algebraMap L E (cf y) := by
    intro y hy; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcf_x]; exact hx i
  have hs_ne : ∀ y ∈ s, cf y ≠ 0 := by
    intro y hy; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcf_x]; exact hr i
  set e : ↥s ≃ ι := (Equiv.setCongr hrange).trans (Equiv.ofInjective x hxinj).symm with he
  have hxe (y : ↥s) : x (e y) = (y : E) :=
    congrArg Subtype.val ((Equiv.ofInjective x hxinj).apply_symm_apply (Equiv.setCongr hrange y))
  have hdim : Module.finrank (ZMod 2) (multiquadraticRelations s cf)
      = Module.finrank (ZMod 2) (rootRelations r) :=
    (multiquadraticRelations_finrank_eq_rootRelations s cf).trans
      (rootRelations_finrank_reindex (fun y : ↥s ↦ cf y.1) (fun y ↦ hs_ne y.1 y.2) hr e
        fun y ↦ by rw [← hcf_x (e y), hxe y])
  rw [← hrange, multiquadratic_degree hs_sq hs_ne, hscard, hdim]

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
