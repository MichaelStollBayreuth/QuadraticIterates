#!/usr/bin/env python3
"""Draw the parameters a = r/s covered by the main theorem and by the two families.

Horizontal axis: the denominator s; vertical axis: the numerator r; one mark per coprime pair.

* Circles: a lies in the region and in one of the 2-adic classes (C1)-(C3) of the main theorem
  (`QuadraticIterates.TwoAdicClass`), coloured by the class. Filled when two of the lists (Z), (O),
  (T) hold (`QuadraticIterates.NegAllCriterion`, `QuadraticIterates.NegFirstCriterion`,
  `QuadraticIterates.NegTailCriterion`), so that
  `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria` gives surjectivity; hollow
  otherwise.
* Squares: the families a = -j(j+1) (`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`)
  and a = -(l^2+l+1) (`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`).
* Black hollow circles: not covered, and c_1, ..., c_6 are 2-dependent (some product of them is a
  square), so rho_a is not surjective.
* Grey dots: not covered, and c_1, ..., c_6 are 2-independent.

The script checks, on the plotted box, that outside (alpha, a_*] the hypotheses of the main theorem
hold exactly when c_1, c_2 are 2-independent
(`QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`), and that every
hollow circle has c_1, c_2 2-dependent, so that rho_a is not surjective there; the legend says so.

Usage: python3 plots/coverage.py. Writes coverage.tex, coverage.pdf and coverage.png next to this
script; needs pdflatex (with TikZ) and pdftocairo.
"""

import shutil
import subprocess
import tempfile
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path

S_MAX, R_MIN, R_MAX = 26, -72, 20
LEVELS = 6  # the uncovered parameters are tested for 2-dependence of c_1, ..., c_LEVELS
HERE = Path(__file__).resolve().parent


# Arithmetic

def factor(n):
    """The prime factorization of |n| > 0, as a dict."""
    n, f, p = abs(n), {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


def legendre(x, p):
    x %= p
    return 0 if x == 0 else 1 if pow(x, (p - 1) // 2, p) == 1 else -1


def split(n, p):
    """(k, m) with n = p^k m and p not dividing m."""
    k = 0
    while n % p == 0:
        n, k = n // p, k + 1
    return k, n


def bisect(f, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if (f(lo) < 0) == (f(mid) < 0) else (lo, mid)
    return lo


# alpha: the real root of x^3 + 2x^2 + 2x + 2; a_*: the root of c_4 between alpha and -1
ALPHA = bisect(lambda x: x ** 3 + 2 * x ** 2 + 2 * x + 2, -2, -1)
A_STAR = bisect(lambda x: ((x * x + x) ** 2 + x) ** 2 + x, -1.4, -1.25)


# The hypotheses, as in QuadraticIterates/Main/TwoAdic.lean and QuadraticIterates/Main/Criteria.lean

def two_adic_class(r, s, eps):
    """1, 2 or 3 for (C1), (C2), (C3), and 0 for none."""
    if s % 2 == 1 and (r + 2 * s + eps) % 4 == 0:
        return 1
    if s % 2 == 1 and (r + s + eps) % 4 == 0:
        return 2
    if s % 2 == 0 and (r + eps) % 4 == 0:
        return 3
    return 0


def criterion_z(r, s):
    """(Z1)-(Z4)."""
    if not is_square(r) and not is_square(-r):
        return True
    if r + 2 * s != 0 and any(p % 8 in (3, 5) for p in factor(r + 2 * s)):
        return True
    if any(p != 2 and legendre(-r * s, p) == -1 and legendre((r - s) * s, p) == -1
           for p in factor(r * r + s * s)):
        return True
    if r == 0:
        return False
    if any(p % 4 == 1 and legendre(split(r, p)[1] * s, p) == -1 for p in factor(r)):
        return True
    k, m = split(r, 2)
    return k >= 3 and m * s % 8 in (3, 5)


def criterion_o(r, s):
    """(O1)-(O5)."""
    if r > 0 or (s % 2 == 1 and (r - s) % 4 == 0):
        return True
    for p in factor(s):
        k, m = split(s, p)
        if p != 2 and (k % 2 == 1 or legendre(-r * m, p) == -1):
            return True
    k, m = split(s, 2)
    if k % 2 == 1 or (k == 2 and r * m % 4 == 1) or (k >= 4 and k % 2 == 0 and r * m % 8 != 7):
        return True
    if r == 0:
        return False
    if any(p % 4 == 3 and legendre(split(r, p)[1] * s, p) == 1 for p in factor(r)):
        return True
    k, m = split(r, 2)
    return k >= 2 and m * s % 4 == 1


def criterion_t(r, s):
    """(T1)-(T4)."""
    t = r + s
    if -s < r < 0:
        return True
    if r != 0:
        if any(p % 4 == 3 and legendre(split(r, p)[1] * s, p) == -1 for p in factor(r)):
            return True
        k, m = split(r, 2)
        if k >= 2 and m * s % 4 == 3:
            return True
    if t == 0:
        return False
    if any(p % 4 == 3 and legendre(s * split(t, p)[1], p) == 1 for p in factor(t)):
        return True
    k, m = split(t, 2)
    if k >= 2 and s * m % 4 == 1:
        return True
    not_sq = not is_square(t) and not is_square(-t)
    if not_sq and (t % 4 == 0 or any(p % 4 == 3 for p in factor(t))):
        return True
    rw3 = (r * r + r * s) ** 2 + r * s ** 3
    return r < -s and rw3 < 0 < rw3 ** 2 + r * s ** 7 and not_sq


def main_class(r, s):
    """The class (C1)-(C3) if a = r/s lies in the region of the main theorem, else 0."""
    if r <= -2 * s:
        return two_adic_class(r, s, -1)
    if r ** 3 + 2 * r * r * s + 2 * r * s * s + 2 * s ** 3 > 0:
        return two_adic_class(r, s, 1)
    return 0


def main_criteria(r, s):
    """Two of (Z), (O), (T)."""
    return criterion_z(r, s) + criterion_o(r, s) + criterion_t(r, s) >= 2


def level_two_independent(r, s):
    """c_1 ~ -rs, c_2 ~ r(r+s) and c_1 c_2 ~ -s(r+s) are not squares."""
    return not (is_square(-r * s) or is_square(r * (r + s)) or is_square(-s * (r + s)))


def coprime_base(nums):
    """Pairwise coprime integers > 1 such that every element of nums is a product of powers."""
    base = {n for n in nums if n > 1}
    while True:
        pair = next(((a, b) for a in base for b in base if a < b and gcd(a, b) > 1), None)
        if pair is None:
            return base
        a, b = pair
        g = gcd(a, b)
        base -= {a, b}
        base |= {x for x in (a // g, b // g, g) if x > 1}


def two_dependent(r, s, levels):
    """Some product of some of c_1, ..., c_levels is a square in Q.

    Modulo squares, c_n is its numerator times its denominator. Over a coprime base, a product of
    such integers is a square iff it is positive and every base element that is not a square occurs
    to an even power; so this is linear dependence over F_2 of the vectors of the sign and these
    parities, decided without factoring.
    """
    a = Fraction(r, s)
    c, vals = -a, []
    for _ in range(levels):
        vals.append(c.numerator * c.denominator)
        c = c * c + a
    if 0 in vals:
        return True
    base = [b for b in coprime_base(abs(v) for v in vals) if not is_square(b)]
    pivots = {}
    for v in vals:
        vec = int(v < 0)
        for i, b in enumerate(base):
            vec |= split(abs(v), b)[0] % 2 << (i + 1)
        while vec and vec.bit_length() in pivots:
            vec ^= pivots[vec.bit_length()]
        if not vec:
            return True
        pivots[vec.bit_length()] = vec
    return False


def family(r, s):
    """'A' for a = -j(j+1), 'Li' for a = -(l^2+l+1), with j, l = u/v as in the two theorems."""
    v = isqrt(s)
    if v * v != s or v % 2 == 0:
        return None
    for u in range(1, isqrt(abs(r)) + 2):
        if gcd(u, v) != 1:
            continue
        if r == -u * (u + v) and u > v and (u % 4, v % 4) in ((2, 1), (3, 3)):
            return 'A'
        if (r == -(u * u + u * v + v * v) and v * v <= u * (u + v)
                and (u % 4, v % 4) in ((1, 1), (2, 3))):
            return 'Li'
    return None


def classify(r, s):
    """The mark for (r, s): ('fam', 'A' | 'Li'), ('main', class, filled), 'dep' or None."""
    f = family(r, s)
    c = main_class(r, s)
    assert not (f and c), (r, s)
    if f:
        return ('fam', f)
    if not c:
        return 'dep' if two_dependent(r, s, LEVELS) else None
    assert level_two_independent(r, s) != two_dependent(r, s, 2), (r, s)
    filled = main_criteria(r, s)
    if not ALPHA < r / s <= A_STAR:
        assert filled == level_two_independent(r, s), (r, s)
    if not filled:
        assert not level_two_independent(r, s), (r, s)
    return ('main', c, filled)


# The picture

PREAMBLE = r"""\documentclass[border=4mm]{standalone}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath}
\usepackage{array}
\usepackage{tikz}
\definecolor{cone}{HTML}{0072B2}
\definecolor{ctwo}{HTML}{009E73}
\definecolor{cthree}{HTML}{E69F00}
\definecolor{famA}{HTML}{8E3B9E}
\definecolor{famLi}{HTML}{D55E00}
\definecolor{dot}{HTML}{A8A8A8}
\definecolor{excl}{HTML}{E4E4E4}
\definecolor{intv}{HTML}{FBF0D4}
\definecolor{ink}{HTML}{303030}
\newcommand{\markF}[3]{\fill[#1] (#2,#3) circle[radius=0.85mm];}
\newcommand{\markH}[3]{\draw[#1, line width=0.6pt, fill=white] (#2,#3) circle[radius=0.62mm];}
\tikzset{sq/.style={draw=ink, line width=0.3pt}}
\newcommand{\markQ}[3]{\filldraw[sq, fill=#1] (#2,#3)
  ++(-0.95mm,-0.95mm) rectangle ++(1.9mm,1.9mm);}
\newcommand{\markD}[2]{\fill[dot] (#1,#2) circle[radius=0.3mm];}
\newcommand{\mk}[1]{\tikz[baseline=-0.6ex]{#1}}
\begin{document}
"""

CLASS_COLOR = {1: 'cone', 2: 'ctwo', 3: 'cthree'}
FAMILY_COLOR = {'A': 'famA', 'Li': 'famLi'}


def legend():
    """The legend, a tabular to the right of the plot."""
    def row(marker, text):
        return rf"\mk{{{marker}}} & {text} \\[0.5ex]"
    filled = lambda c, x=0: rf"\fill[{c}] ({x}mm,0) circle[radius=0.85mm];"
    hollow = lambda c, x=0: rf"\draw[{c}, line width=0.6pt] ({x}mm,0) circle[radius=0.62mm];"
    trio = lambda f: "".join(f(c, x) for c, x in (('cone', -2.1), ('ctwo', 0), ('cthree', 2.1)))
    square = lambda c: rf"\filldraw[sq, fill={c}] (-0.95mm,-0.95mm) rectangle (0.95mm,0.95mm);"
    swatch = lambda c: rf"\fill[{c}] (-1.4mm,-1.1mm) rectangle (1.4mm,1.1mm);"
    lines = [
        r"\begin{tabular}{@{}c@{\hspace{0.7em}}>{\raggedright\arraybackslash}p{6.2cm}@{}}",
        r"\multicolumn{2}{@{}l}{\large\bfseries Arboreal representations of $x^2 + a$} \\",
        r"\multicolumn{2}{@{}l}{coprime $r, s$ with $s \ge 1$, $a = r/s$} \\[1.5ex]",
        r"\multicolumn{2}{@{}l}{\bfseries Main theorem: circles, by $2$-adic class} \\[0.3ex]",
        r"& $(r, s) \bmod 4$ for $a \le -2$; for $a > \alpha$ \\[0.3ex]",
        row(filled('cone'), r"(C1): $(3,1)$, $(3,3)$; $(1,1)$, $(1,3)$"),
        row(filled('ctwo'), r"(C2): $(0,1)$, $(2,3)$; $(2,1)$, $(0,3)$"),
        row(filled('cthree'), r"(C3): $(1,0)$, $(1,2)$; $(3,0)$, $(3,2)$"),
        row(trio(filled), r"two of (Z), (O), (T) hold, so $\rho_a$ is surjective"),
        row(trio(hollow), r"$c_1, c_2$ are $2$-dependent, so $\rho_a$ is not surjective"),
        r"\multicolumn{2}{@{}l}{} \\[0.5ex]",
        r"\multicolumn{2}{@{}l}{\bfseries The two families: squares} \\[0.3ex]",
        row(square('famA'), r"$a = -j(j + 1)$, $j = u/v > 1$, "
            r"$(u, v) \equiv (2,1), (3,3) \bmod 4$"),
        row(square('famLi'), r"$a = -(\ell^2 + \ell + 1) \le -2$, $\ell = u/v$, "
            r"$(u, v) \equiv (1,1), (2,3) \bmod 4$"),
        r"\multicolumn{2}{@{}l}{} \\[0.5ex]",
        r"\multicolumn{2}{@{}l}{\bfseries Not covered} \\[0.3ex]",
        row(hollow('ink'), r"$c_1, \dots, c_6$ are $2$-dependent, so $\rho_a$ is not surjective"),
        row(r"\fill[dot] (0,0) circle[radius=0.3mm];", r"$c_1, \dots, c_6$ are $2$-independent"),
        row("", r"no mark: $\gcd(r, s) > 1$; $a$ appears at its reduced fraction, "
            r"whose residues mod $4$ may differ"),
        r"\multicolumn{2}{@{}l}{} \\[0.5ex]",
        r"\multicolumn{2}{@{}l}{\bfseries Regions} \\[0.3ex]",
        row(swatch('excl'), r"$-2 < a \le \alpha$: not covered"),
        row(swatch('intv'), r"$\alpha < a \le a_*$; outside it, in the classes, $\rho_a$ is "
            r"surjective iff $c_1, c_2$ are $2$-independent"),
        r"\end{tabular}",
    ]
    return "\n".join(lines)


def picture():
    x0, x1, y0, y1 = 0.3, S_MAX + 0.7, R_MIN - 1.5, R_MAX + 1.5
    out = [PREAMBLE, r"\begin{tikzpicture}[x=0.42cm, y=0.21cm, font=\footnotesize]"]
    # regions and lines through the origin, clipped to the frame
    out.append(rf"\begin{{scope}}\clip ({x0},{y0}) rectangle ({x1},{y1});")
    out.append(rf"\fill[excl] (0,0) -- ({x1},{-2 * x1:.3f}) -- ({x1},{ALPHA * x1:.3f}) -- cycle;")
    out.append(rf"\fill[intv] (0,0) -- ({x1},{ALPHA * x1:.3f}) -- "
               rf"({x1},{A_STAR * x1:.3f}) -- cycle;")
    for a in (-2, ALPHA, A_STAR, -1, 0):
        out.append(rf"\draw[ink!55, line width=0.4pt] (0,0) -- ({x1},{a * x1:.3f});")
    out.append(r"\end{scope}")
    # the marks
    for s in range(1, S_MAX + 1):
        for r in range(R_MIN, R_MAX + 1):
            if gcd(r, s) != 1:
                continue
            m = classify(r, s)
            if m is None:
                out.append(rf"\markD{{{s}}}{{{r}}}")
            elif m == 'dep':
                out.append(rf"\markH{{ink}}{{{s}}}{{{r}}}")
            elif m[0] == 'fam':
                out.append(rf"\markQ{{{FAMILY_COLOR[m[1]]}}}{{{s}}}{{{r}}}")
            else:
                out.append(rf"\mark{'F' if m[2] else 'H'}{{{CLASS_COLOR[m[1]]}}}{{{s}}}{{{r}}}")
    # frame, ticks, labels
    out.append(rf"\draw[ink, line width=0.5pt] ({x0},{y0}) rectangle ({x1},{y1});")
    for s in (1, 5, 10, 15, 20, 25):
        out.append(rf"\draw[ink] ({s},{y0}) -- +(0,-0.8) node[below] {{${s}$}};")
    for r in range(-70, R_MAX + 1, 10):
        out.append(rf"\draw[ink] ({x0},{r}) -- +(-0.25,0) node[left] {{${r}$}};")
    out.append(rf"\node[below=5mm] at ({(x0 + x1) / 2},{y0}) {{denominator $s$}};")
    out.append(rf"\node[left=9mm, rotate=90, anchor=south] at ({x0},{(y0 + y1) / 2}) "
               r"{numerator $r$};")
    labels = [(-2, r"a = -2"), (ALPHA, rf"a = \alpha \approx {ALPHA:.3f}"),
              (A_STAR, rf"a = a_* \approx {A_STAR:.3f}"), (-1, r"a = -1"), (0, r"a = 0")]
    for a, text in labels:
        out.append(rf"\node[right, ink] at ({x1},{a * x1:.3f}) {{${text}$}};")
    out.append(rf"\node[anchor=north west] at ({x1 + 6.2},{y1}) {{{legend()}}};")
    out.append(r"\end{tikzpicture}")
    out.append(r"\end{document}")
    return "\n".join(out) + "\n"


def main():
    tex = HERE / "coverage.tex"
    tex.write_text(picture())
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                        "-output-directory", tmp, str(tex)], check=True,
                       stdout=subprocess.DEVNULL)
        shutil.copy(Path(tmp) / "coverage.pdf", HERE / "coverage.pdf")
    subprocess.run(["pdftocairo", "-png", "-r", "200", "-singlefile",
                    str(HERE / "coverage.pdf"), str(HERE / "coverage")], check=True)


if __name__ == "__main__":
    main()
