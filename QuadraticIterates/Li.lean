/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import QuadraticIterates.Li.ArchMath2021
public import QuadraticIterates.Li.Residues

/-!
# Further values of `a` with `Ω_n ≅ [C₂]ⁿ`: the results of Li

Formalization of the results of H.-C. Li, Arch. Math. **114** (2020), 265-269, and Arch. Math.
**117** (2021), 133-140, which extend the Section 3 theorem of M. Stoll, *Galois groups over ℚ of
some iterated polynomials* (`QuadraticIterates.ArchMath1992`) to further values of `a`: the
Galois group `Ω_n` of the `n`-th iterate of `X² + a` is the full wreath power `[C₂]ⁿ` for all `n`
when `a = -(8k+2)(8k+3)` or `a = -((4k+1)(4k+2)+1)`, and, for `a < 0` with `a ≡ 3 mod 4` and `-a`
not a square, if and only if `-a - 1` is not a square.

The proofs follow the pattern of the Section 3 theorem: none of the `|b_n|`, `n ≥ 2` (resp.
`n ≥ 3`), is a square, by the single-index criteria of Chapter 2 with suitable moduli, whose
residues are computed in `QuadraticIterates.Li.Residues`.
-/
