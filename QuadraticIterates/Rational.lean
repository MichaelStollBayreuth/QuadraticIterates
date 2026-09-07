/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.Reflection
public import QuadraticIterates.Rational.Residues
public import QuadraticIterates.Rational.Sequence

/-!
# Rational parameters `a = r/s`

The extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some iterated
polynomials* (`QuadraticIterates.ArchMath1992`), to rational parameters: for `a = r/s`, the
rescaled sequence `γ_n = w_n / s^(2^(n-1) - 1)` has integer numerators `w_n`
(`QuadraticIterates.Rational.Sequence`), whose Möbius factors `β_n` are the integers whose
square classes decide `Ω_n ≅ [C₂]ⁿ`; the reflection mechanism shows `β_n` to be a non-square
modulo suitable moduli (`QuadraticIterates.Rational.Reflection`), which exist for every
non-squarefree level in the 2-adic classes (`QuadraticIterates.Rational.Residues`). Work in
progress; the plan is Chapter 6 of the blueprint.
-/
