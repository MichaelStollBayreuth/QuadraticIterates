module

public import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements, with `sorry` proofs, of the main results for verification with
[leanprover/comparator](https://github.com/leanprover/comparator): the three cases of the paper's
Section 3 main result (`section3_main`), one challenge per case, the theorems of Li extending it
(`li2021_theorem_3_9`, `li2020_theorem_3_5` and, in its strengthened form
`nonempty_mulEquiv_of_eq_neg_mul`, Theorem 3.3 of 2021; all in `QuadraticIterates/Main/Integers`),
and the main theorem for rational parameters `a = r/s`
(`nonempty_mulEquiv_of_twoAdicClass_of_criteria` in `QuadraticIterates/Main/Theorem`).

This file imports **only Mathlib**: the non-Mathlib definitions the statements refer to
(`QuadraticIterates.iteratedPoly`, `.GaloisGroup`, `.WreathPower`, and for the main theorem the
criteria `.NegAllCriterion`, `.NegFirstCriterion`, `.NegTailCriterion` and the `2`-adic classes
`.TwoAdicClass`) are reproduced here from the library — under their library names, and with the
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

end QuadraticIterates

open QuadraticIterates

/-- Section 3 main result (`section3_main`), case a): if `a > 0` and `a ≡ 1 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_one (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 1) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case b): if `a > 0` and `a ≡ 2 mod 4`, then
`Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_pos_emod_four_eq_two (a : ℤ) (ha : 0 < a) (ha4 : a % 4 = 2) :
    ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Section 3 main result (`section3_main`), case c): if `a < 0`, `a ≡ 0 mod 4` and `-a` is not a
square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_section3_main_neg_emod_four_eq_zero (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 0)
    (hsq : ¬IsSquare (-a)) : ∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n) :=
  sorry

/-- For `a = -(4k+2)(4k+3)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` (`nonempty_mulEquiv_of_eq_neg_mul`);
Theorem 3.3 of H.-C. Li, Arch. Math. 117 (2021), is the case of even `k`, `a = -(8k+2)(8k+3)`. -/
theorem challenge_nonempty_mulEquiv_of_eq_neg_mul (k : ℕ) :
    ∀ n ≥ 1, Nonempty (GaloisGroup ((-((4 * k + 2) * (4 * k + 3)) : ℤ) : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.9 of H.-C. Li, Arch. Math. 117 (2021) (`li2021_theorem_3_9`): for
`a = -((4k+1)(4k+2)+1)`, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`. -/
theorem challenge_li2021_theorem_3_9 (k : ℕ) :
    ∀ n ≥ 1,
      Nonempty (GaloisGroup ((-((4 * k + 1) * (4 * k + 2) + 1) : ℤ) : ℚ) n ≃* WreathPower n) :=
  sorry

/-- Theorem 3.5 of H.-C. Li, Arch. Math. 114 (2020) (`li2020_theorem_3_5`): for `a < 0` with
`a ≡ 3 mod 4` and `-a` not a square, `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1` if and only if `-a - 1` is not
a square. -/
theorem challenge_li2020_theorem_3_5 (a : ℤ) (ha : a < 0) (ha4 : a % 4 = 3)
    (hsq : ¬IsSquare (-a)) :
    (∀ n ≥ 1, Nonempty (GaloisGroup (a : ℚ) n ≃* WreathPower n)) ↔ ¬IsSquare (-a - 1) :=
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
