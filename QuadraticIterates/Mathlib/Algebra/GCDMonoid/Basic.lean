/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Normalization under homomorphisms

Normalizing before applying a monoid homomorphism does not change the normalized image
(`normalize_map_normalize`).

Auxiliary material for the formalization of the surjectivity of arboreal Galois representations of
`X² + a`; upstreaming candidates for Mathlib.
-/

@[expose] public section

theorem normalize_map_normalize {α : Type*} [MonoidWithZero α] [NormalizationMonoid α]
    [IsLeftCancelMulZero α] {F : Type*} [FunLike F α α] [MonoidHomClass F α α] (f : F) (x : α) :
    normalize (f (normalize x)) = normalize (f x) :=
  normalize_eq_normalize_iff_associated.mpr ((normalize_associated x).map f)
