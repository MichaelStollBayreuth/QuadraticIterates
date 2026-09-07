/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Rational.GammaTwo
public import QuadraticIterates.Rational.Main
public import QuadraticIterates.Rational.Reflection
public import QuadraticIterates.Rational.Residues
public import QuadraticIterates.Rational.Sequence
public import QuadraticIterates.Rational.SquareClasses

/-!
# Rational parameters `a = r/s`

The extension of the Section 3 theorem of M. Stoll, *Galois groups over ℚ of some iterated
polynomials* (`QuadraticIterates.ArchMath1992`), to rational parameters: for `a = r/s`, the
rescaled sequence `γ_n = w_n / s^(2^(n-1) - 1)` has integer numerators `w_n`
(`QuadraticIterates.Rational.Sequence`), whose Möbius factors `β_n` are the integers whose
square classes decide `Ω_n ≅ [C₂]ⁿ`; the reflection mechanism shows `β_n` to be a non-square
modulo suitable moduli (`QuadraticIterates.Rational.Reflection`), which exist for every
non-squarefree level in the 2-adic classes and, under the squarefree-level certificates, for the
squarefree levels (`QuadraticIterates.Rational.Residues`); a second mechanism for the squarefree
levels works modulo divisors of the numerator of `γ_2` (`QuadraticIterates.Rational.GammaTwo`).
The shared-part lemma (`QuadraticIterates.Rational.SquareClasses`) turns the non-squareness of
all `|β_n|`, `n ≥ 2`, into `Ω_n ≅ [C₂]ⁿ` for all `n`, through the Section 1 theorem for a rational
parameter; Theorems R⁺ and R⁻ (`QuadraticIterates.Rational.Main`) assemble these for the positive
world `a > -1` and for Stoll's world `a ≤ -2`. Chapter 6 of the blueprint.
-/
