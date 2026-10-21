module

public import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements, with `sorry` proofs, of the main results for verification with
[leanprover/comparator](https://github.com/leanprover/comparator): the results for integer
parameters, which contain the main result of Section 3 of M. Stoll, Arch. Math. 59 (1992) (three
challenges, one per case) and Theorem 3.5 of H.-C. Li, Arch. Math. 114 (2020)
(`forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three`; all in
`QuadraticIterates/Main/Integers`), the integer parameters of the two families of
`QuadraticIterates/Main/Families`, which contain Theorems 3.3 and 3.9 of H.-C. Li, Arch. Math. 117
(2021) (`nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two` and
`nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one`),
the main theorem for rational parameters `a = r/s`
(`nonempty_mulEquiv_of_twoAdicClass_of_criteria` in `QuadraticIterates/Main/Theorem`), and its
three corollaries: level two decides outside the interval `(α, α′]`
(`forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass` in
`QuadraticIterates/Main/LevelTwo`), shorter lists of criteria on the interval `α < a < -1`
(`nonempty_mulEquiv_of_lt_neg_one_of_criteria` in `QuadraticIterates/Main/Interval`), and the
classes of `(r, s)` in which no criterion is needed there
(`nonempty_mulEquiv_of_lt_neg_one_of_emod`, in the same file).

This file imports **only Mathlib**: the non-Mathlib definitions the statements refer to
(`QuadraticIterates.iteratedPoly`, `.GaloisGroup`, `.WreathPower`, and for the main theorem the
criteria `.NegAllCriterion`, `.NegFirstCriterion`, `.NegTailCriterion` and the `2`-adic classes
`.TwoAdicClass`, and for the second corollary `.NegFirstCriterion'` and `.NegTailCriterion'`) are
reproduced here from the library — under their library names, and with the
library's local notation `fℚ[a, n]` spelled out — so the challenge does not depend on the repository
being formalized. The Galois group is defined for a rational parameter, as in the library; the
integer parameters of the challenges are cast to `ℚ`. Comparator compares the full definition
bodies (not just types) between challenge and solution, so a solution that alters any of these
definitions is rejected. The companion `Solution.lean` discharges the `sorry`s with the library
theorems.
-/

@[expose] public section

namespace QuadraticIterates

/-- The iterates `f_n` of `f = X² + a` over a commutative (semi)ring `R`: `f_0 = X`,
`f_{n+1} = f_n² + a`. Over `ℤ` (`R := ℤ`) this is the sequence of the paper. -/
noncomputable def iteratedPoly {R : Type*} [CommSemiring R] (a : R) : ℕ → Polynomial R
  | 0 => Polynomial.X
  | n + 1 => (iteratedPoly a n) ^ 2 + Polynomial.C a

/-- The Galois group `Ω_n = Gal(f_n/ℚ)` of the `n`-th iterate of `X² + a`, `a ∈ ℚ`, via Mathlib's
`Polynomial.Gal`. -/
noncomputable abbrev GaloisGroup (a : ℚ) (n : ℕ) : Type :=
  (iteratedPoly a n).Gal

/-- The `n`-fold iterated regular wreath product `[C_2]^n` of `C_2 = Multiplicative (ZMod 2)`, via
Mathlib's `IteratedWreathProduct`. -/
abbrev WreathPower (n : ℕ) : Type :=
  IteratedWreathProduct (Multiplicative (ZMod 2)) n

/-- Criteria (Z1)–(Z4) for `φ₀` (the pattern `(-1, -1, -1, …)`), for `a = r/s`. -/
inductive NegAllCriterion (r s : ℤ) : Prop
  /-- (Z1) `r ≠ ±□`. -/
  | not_isSquare (h : ¬IsSquare r) (h' : ¬IsSquare (-r))
  /-- (Z2) A prime `p ≡ ±3 (mod 8)` divides `r + 2s`. -/
  | dvd_add_two_mul (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
      (hdvd : (p : ℤ) ∣ r + 2 * s)
  /-- (Z3) An odd prime `p` divides `r² + s²`, and `(-rs / p) = ((r - s)s / p) = -1`. -/
  | dvd_sq_add_sq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ r ^ 2 + s ^ 2)
      (h₁ : jacobiSym (-(r * s)) p = -1) (h₂ : jacobiSym ((r - s) * s) p = -1)
  /-- (Z4) A prime `p ≡ 1 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(m s / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 1) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- (Z4) `r = 2^k m` with `k ≥ 3` and `m s ≡ ±3 (mod 8)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 3 ≤ k) (hr : r = 2 ^ k * m)
      (h : m * s % 8 = 3 ∨ m * s % 8 = 5)

/-- Criteria (O1)–(O5) for `φ₁` (the pattern `(-1, 1, 1, …)`), for `a = r/s` with `s > 0`. -/
inductive NegFirstCriterion (r s : ℤ) : Prop
  /-- (O1) `a > 0`. -/
  | pos (h : 0 < r)
  /-- (O2) `a ≡ 1 mod 4`: `s` is odd and `r ≡ s (mod 4)`. -/
  | modEq_four (hs : Odd s) (h : r ≡ s [ZMOD 4])
  /-- (O3) An odd prime `p` divides `s = p^k m` (`p ∤ m`) with `k` odd or `(-rm / p) = -1`. -/
  | dvd_right (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) (hs : s = p ^ k * m)
      (hm : ¬(p : ℤ) ∣ m) (h : Odd k ∨ jacobiSym (-(r * m)) p = -1)
  /-- (O4) `s = 2^k m` with `m` odd, and `k` is odd, or `k = 2` and `rm ≡ 1 (mod 4)`, or `k ≥ 4`
  is even and `rm ≢ -1 (mod 8)`. -/
  | dvd_right_two (k : ℕ) (m : ℤ) (hs : s = 2 ^ k * m) (hm : Odd m)
      (h : Odd k ∨ (k = 2 ∧ r * m % 4 = 1) ∨ (Even k ∧ 4 ≤ k ∧ r * m % 8 ≠ 7))
  /-- (O5) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = 1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = 1)
  /-- (O5) `r = 2^k m` with `k ≥ 2` and `ms ≡ 1 (mod 4)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 1)

/-- Criteria (T1)–(T4) for `τ` (the pattern `(1, -1, -1, …)`), for `a = r/s` with `s > 0`. -/
inductive NegTailCriterion (r s : ℤ) : Prop
  /-- (T1) `-1 < a < 0`. -/
  | neg_one_lt (h₁ : -s < r) (h₀ : r < 0)
  /-- (T2) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- (T2) `r = 2^k m` with `k ≥ 2` and `ms ≡ 3 (mod 4)`. -/
  | dvd_left_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hr : r = 2 ^ k * m) (h : m * s % 4 = 3)
  /-- (T3) A prime `p ≡ 3 (mod 4)` divides `r + s = p^k m` (`p ∤ m`) with `(sm / p) = 1`. -/
  | dvd_add (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hrs : r + s = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (s * m) p = 1)
  /-- (T3) `r + s = 2^k m` with `k ≥ 2` and `sm ≡ 1 (mod 4)`. -/
  | dvd_add_two (k : ℕ) (m : ℤ) (hk : 2 ≤ k) (hrs : r + s = 2 ^ k * m) (h : s * m % 4 = 1)
  /-- (T3) `r + s ≠ ±□`, and `r + s` is divisible by `4` or by a prime `p ≡ 3 (mod 4)`. -/
  | not_isSquare_add (h : ¬IsSquare (r + s)) (h' : ¬IsSquare (-(r + s)))
      (hdvd : 4 ∣ r + s ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p : ℤ) ∣ r + s)
  /-- (T4) `a < -1`, `c_3 < 0 < c_4` (that is, `r w_3 < 0 < r w_4`), and `r + s ≠ ±□`. -/
  | window (hr : r < -s) (h₃ : (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0)
      (h₄ : 0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) (h : ¬IsSquare (r + s))
      (h' : ¬IsSquare (-(r + s)))

/-- The `2`-adic classes (C1)–(C3) of the main theorem for `a = r/s` with sign `ε`: `s` odd and
`r + 2s ≡ -ε (mod 4)`; `s` odd and `r + s ≡ -ε (mod 4)`; or `s` even and `r ≡ -ε (mod 4)`. -/
def TwoAdicClass (r s ε : ℤ) : Prop :=
  (Odd s ∧ r + 2 * s ≡ -ε [ZMOD 4]) ∨ (Odd s ∧ r + s ≡ -ε [ZMOD 4]) ∨ (Even s ∧ r ≡ -ε [ZMOD 4])

/-- Criteria for `φ₁` (the pattern `(-1, 1, 1, …)`) for `a = r/s` with `α < a < -1`. -/
inductive NegFirstCriterion' (r s : ℤ) : Prop
  /-- `a ≡ 1 mod 4`: `s` is odd and `r ≡ s (mod 4)`. -/
  | modEq_four (hs : Odd s) (h : r ≡ s [ZMOD 4])
  /-- `s` is not a square. -/
  | not_isSquare_right (h : ¬IsSquare s)
  /-- `-r` is not a square modulo an odd prime `p ∣ s`. -/
  | dvd_right (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ s)
      (h : jacobiSym (-r) p = -1)
  /-- `16 ∣ s` and `r ≡ 3 (mod 8)`. -/
  | dvd_right_sixteen (h : 16 ∣ s) (hr : r % 8 = 3)
  /-- (O5) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = 1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = 1)

/-- Criteria for `τ` (the pattern `(1, -1, -1, …)`) for `a = r/s` with `α < a < -1`. -/
inductive NegTailCriterion' (r s : ℤ) : Prop
  /-- (T2) A prime `p ≡ 3 (mod 4)` divides `r = p^k m` (`p ∤ m`) with `(ms / p) = -1`. -/
  | dvd_left (p k : ℕ) (m : ℤ) (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k)
      (hr : r = p ^ k * m) (hm : ¬(p : ℤ) ∣ m) (h : jacobiSym (m * s) p = -1)
  /-- A prime `p ≡ 3 (mod 4)` divides `r + s`. -/
  | dvd_add (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hdvd : (p : ℤ) ∣ r + s)

end QuadraticIterates

open QuadraticIterates

/-- Integer parameters (`nonempty_mulEquiv_of_pos_of_emod_four_eq_one`): if `a > 0` and
`a ≡ 1 mod 4`, then `Ω_n ≅ [C₂]ⁿ` for all `n`; case a) of the main result of Section 3 of
M. Stoll, Arch. Math. 59 (1992). -/
theorem challenge_nonempty_mulEquiv_of_pos_of_emod_four_eq_one (a : ℤ) (ha : 0 < a)
    (ha4 : a % 4 = 1) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Integer parameters (`nonempty_mulEquiv_of_pos_of_emod_four_eq_two`): if `a > 0` and
`a ≡ 2 mod 4`, then `Ω_n ≅ [C₂]ⁿ` for all `n`; case b) of the main result of Section 3 of
M. Stoll, Arch. Math. 59 (1992). -/
theorem challenge_nonempty_mulEquiv_of_pos_of_emod_four_eq_two (a : ℤ) (ha : 0 < a)
    (ha4 : a % 4 = 2) (n : ℕ) : Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Integer parameters (`nonempty_mulEquiv_of_neg_of_emod_four_eq_zero`): if `a < 0`,
`a ≡ 0 mod 4` and `-a` is not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n`; case c) of the main result
of Section 3 of M. Stoll, Arch. Math. 59 (1992). -/
theorem challenge_nonempty_mulEquiv_of_neg_of_emod_four_eq_zero (a : ℤ) (ha : a < 0)
    (ha4 : a % 4 = 0) (hsq : ¬IsSquare (-a)) (n : ℕ) :
    Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Integer parameters of the first family
(`nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two`): for `a = -ℓ(ℓ + 1)` with a
positive integer `ℓ ≡ 2 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`. Theorem 3.3 of H.-C. Li, Arch. Math.
117 (2021), is the case `ℓ = 8k + 2`. -/
theorem challenge_nonempty_mulEquiv_of_eq_neg_mul_add_one_of_emod_four_eq_two (ℓ : ℤ) (hℓ : 0 < ℓ)
    (hℓ4 : ℓ % 4 = 2) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) * (ℓ + 1))) n ≃* WreathPower n) :=
  sorry

/-- Integer parameters of the second family
(`nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one`): for `a = -(ℓ² + ℓ + 1)` with a
positive integer `ℓ ≡ 1 mod 4`, `Ω_n ≅ [C₂]ⁿ` for all `n`. Theorem 3.9 of H.-C. Li, Arch. Math.
117 (2021), is this statement with `ℓ = 4k + 1`. -/
theorem challenge_nonempty_mulEquiv_of_eq_neg_sq_add_add_one_of_emod_four_eq_one (ℓ : ℤ)
    (hℓ : 0 < ℓ) (hℓ4 : ℓ % 4 = 1) (n : ℕ) :
    Nonempty (GaloisGroup (-((ℓ : ℚ) ^ 2 + ℓ + 1)) n ≃* WreathPower n) :=
  sorry

/-- Integer parameters (`forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three`): for `a < 0`
with `a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ` for all `n` if and only if `-a - 1` is
not a square; Theorem 3.5 of H.-C. Li, Arch. Math. 114 (2020). -/
theorem challenge_forall_nonempty_mulEquiv_iff_of_neg_of_emod_four_eq_three (a : ℤ) (ha : a < 0)
    (ha4 : a % 4 = 3) (hsq : ¬IsSquare (-a)) :
    (∀ n, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
  sorry

/-- **The main theorem** for rational parameters (`nonempty_mulEquiv_of_twoAdicClass_of_criteria`):
let `a = r/s` with `r, s` coprime and `s > 0`, and either `a ≤ -2` and `ε = -1`, or
`a³ + 2a² + 2a + 2 > 0` and `ε = 1`. If `(r, s, ε)` lies in one of the `2`-adic classes
`TwoAdicClass r s ε` and two of the three lists of criteria `NegAllCriterion r s`,
`NegFirstCriterion r s`, `NegTailCriterion r s` apply, then `Ω_n ≅ [C₂]ⁿ` for all `n`. -/
theorem challenge_nonempty_mulEquiv_of_twoAdicClass_of_criteria (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (ε : ℤ)
    (hε : (r ≤ -2 * s ∧ ε = -1) ∨ (0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3 ∧ ε = 1))
    (hc : TwoAdicClass r s ε)
    (h : NegAllCriterion r s ∧ NegFirstCriterion r s ∨ NegAllCriterion r s ∧ NegTailCriterion r s ∨
      NegFirstCriterion r s ∧ NegTailCriterion r s) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  sorry

/-- **Level two decides** (`forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`): let
`a = r/s` with `r, s` coprime and `s > 0`, and either `a ≤ -2` and `ε = -1`, or `a > -1` or
`a < -1` with `c₃ < 0 < c₄` (here `r w₃ = (r² + rs)² + rs³` and `r w₄ = (r w₃)² + rs⁷`) and
`ε = 1`. If `(r, s, ε)` lies in one of the `2`-adic classes `TwoAdicClass r s ε`, then `Ω_n ≅ [C₂]ⁿ`
for all `n` if and only if `c₁ = -a` and `c₂ = a² + a` are 2-independent: none of `c₁`, `c₂`,
`c₁ c₂` is a square. -/
theorem challenge_forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass (r s : ℤ)
    (hrs : IsCoprime r s) (hs : 0 < s) (ε : ℤ)
    (hε : r ≤ -2 * s ∧ ε = -1 ∨ (-s < r ∨ r < -s ∧ (r ^ 2 + r * s) ^ 2 + r * s ^ 3 < 0 ∧
      0 < ((r ^ 2 + r * s) ^ 2 + r * s ^ 3) ^ 2 + r * s ^ 7) ∧ ε = 1)
    (hc : TwoAdicClass r s ε) :
    (∀ n, Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n)) ↔
      ¬IsSquare (-(r / s : ℚ)) ∧ ¬IsSquare ((r / s : ℚ) ^ 2 + r / s) ∧
        ¬IsSquare (-(r / s : ℚ) * ((r / s : ℚ) ^ 2 + r / s)) :=
  sorry

/-- **The interval** `α < a < -1` (`nonempty_mulEquiv_of_lt_neg_one_of_criteria`): let `a = r/s`
with `r, s` coprime, `s > 0`, `a < -1` and `a³ + 2a² + 2a + 2 > 0`, in one of the `2`-adic classes
`TwoAdicClass r s 1`, and let `c₁ = -a` and `c₂ = a² + a` be 2-independent. If two of the lists of
criteria `NegAllCriterion r s`, `NegFirstCriterion' r s`, `NegTailCriterion' r s` apply, then
`Ω_n ≅ [C₂]ⁿ` for all `n`. -/
theorem challenge_nonempty_mulEquiv_of_lt_neg_one_of_criteria (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (hr : r < -s) (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (hc : TwoAdicClass r s 1)
    (h2 : ¬IsSquare (-(r / s : ℚ)) ∧ ¬IsSquare ((r / s : ℚ) ^ 2 + r / s) ∧
      ¬IsSquare (-(r / s : ℚ) * ((r / s : ℚ) ^ 2 + r / s)))
    (h : NegAllCriterion r s ∧ NegFirstCriterion' r s ∨ NegAllCriterion r s ∧
      NegTailCriterion' r s ∨ NegFirstCriterion' r s ∧ NegTailCriterion' r s) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  sorry

/-- **Automatic classes on the interval** `α < a < -1` (`nonempty_mulEquiv_of_lt_neg_one_of_emod`):
let `a = r/s` with `r, s` coprime, `s > 0`, `a < -1` and `a³ + 2a² + 2a + 2 > 0`. If
`(r, s) ≡ (1, 1)`, `(1, 3)` or `(3, 2) (mod 4)`; or `(r, s) ≡ (2, 1) (mod 4)` with `r ≡ 2` or
`s ≡ 5 (mod 8)`; or `(r, s) ≡ (0, 3) (mod 4)` with `|r|` not of the form `4^j m`, `m ≡ 1 (mod 8)`
(not a square in `ℚ₂`), or `r + 2s ≡ ±6 (mod 16)`; or `r ≡ 3 (mod 8)`, `s ≡ 0 (mod 4)` and
`s ≢ 4 (mod 32)`, then `Ω_n ≅ [C₂]ⁿ` for all `n`. -/
theorem challenge_nonempty_mulEquiv_of_lt_neg_one_of_emod (r s : ℤ) (hrs : IsCoprime r s)
    (hs : 0 < s) (hr : r < -s) (hα : 0 < r ^ 3 + 2 * r ^ 2 * s + 2 * r * s ^ 2 + 2 * s ^ 3)
    (h : r % 4 = 1 ∧ s % 2 = 1 ∨ r % 4 = 3 ∧ s % 4 = 2 ∨
      r % 4 = 2 ∧ s % 4 = 1 ∧ (r % 8 = 2 ∨ s % 8 = 5) ∨
      r % 4 = 0 ∧ s % 4 = 3 ∧ ((∀ j : ℕ, ∀ m : ℤ, -r = 4 ^ j * m → m % 8 ≠ 1) ∨
        (r + 2 * s) % 16 = 6 ∨ (r + 2 * s) % 16 = 10) ∨
      r % 8 = 3 ∧ s % 4 = 0 ∧ s % 32 ≠ 4) (n : ℕ) :
    Nonempty (GaloisGroup (r / s : ℚ) n ≃* WreathPower n) :=
  sorry
