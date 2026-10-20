#!/usr/bin/env python3
"""Draw the parameters a = r/s covered by the main theorem and by the two families.

One mark per coprime pair (r, s), in two layouts: coverage.pdf has the denominator s across and the
numerator r up, with a full legend, drawn at its final size for a page with text width 16 cm (so
that its text keeps its nominal size); coverage-slide.pdf, for a 16:9 slide, has r across and s up,
a sans-serif font and a compact legend.

* Circles: a lies in the region and in one of the 2-adic classes (C1)-(C3) of the main theorem
  (`QuadraticIterates.TwoAdicClass`), coloured by the class. Filled when two of the lists (Z), (O),
  (T) hold (`QuadraticIterates.NegAllCriterion`, `QuadraticIterates.NegFirstCriterion`,
  `QuadraticIterates.NegTailCriterion`), so that
  `QuadraticIterates.nonempty_mulEquiv_of_twoAdicClass_of_criteria` gives surjectivity; hollow
  otherwise.
* Squares: the families a = -l(l+1) (`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_mul_add_one`)
  and a = -(l^2+l+1) (`QuadraticIterates.nonempty_mulEquiv_of_eq_neg_sq_add_add_one`).
* Black hollow circles: not covered, and c_1, ..., c_6 are 2-dependent (some product of them is a
  square), so rho_a is not surjective.
* Grey dots: not covered, and c_1, ..., c_6 are 2-independent.

The script checks, on the plotted box, that outside (alpha, alpha'] the hypotheses of the main
theorem hold exactly when c_1, c_2 are 2-independent
(`QuadraticIterates.forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`), and that every
hollow coloured circle has c_1, c_2 2-dependent, so that rho_a is not surjective there; the legends
say so.

Usage: python3 plots/coverage.py. Writes coverage.{tex,pdf,png} and coverage-slide.{tex,pdf,png}
next to this script; needs pdflatex (with TikZ and sansmath) and pdftocairo.
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


# alpha: the real root of x^3 + 2x^2 + 2x + 2; alpha': the root of c_4 between alpha and -1
ALPHA = bisect(lambda x: x ** 3 + 2 * x ** 2 + 2 * x + 2, -2, -1)
ALPHA_PRIME = bisect(lambda x: ((x * x + x) ** 2 + x) ** 2 + x, -1.4, -1.25)


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
    """'A' for a = -l(l+1), 'Li' for a = -(l^2+l+1), with l = u/v as in the two theorems."""
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
    if not ALPHA < r / s <= ALPHA_PRIME:
        assert filled == level_two_independent(r, s), (r, s)
    if not filled:
        assert not level_two_independent(r, s), (r, s)
    return ('main', c, filled)


# The pictures

CLASS_COLOR = {1: 'cone', 2: 'ctwo', 3: 'cthree'}
FAMILY_COLOR = {'A': 'famA', 'Li': 'famLi'}

# Radii in mm of filled circles (f), hollow circles (h) and dots (d), half the side of a square (q),
# and the line width in pt of hollow circles (lw)
PORTRAIT = dict(f=0.6, h=0.44, q=0.68, d=0.21, lw=0.45)
SLIDE = dict(f=0.64, h=0.47, q=0.72, d=0.22, lw=0.5)

PREAMBLE = r"""\documentclass[border=@border@mm]{standalone}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath}
\usepackage{array}
\usepackage{tikz}
@FONTS@
\definecolor{cone}{HTML}{0072B2}
\definecolor{ctwo}{HTML}{009E73}
\definecolor{cthree}{HTML}{E69F00}
\definecolor{famA}{HTML}{8E3B9E}
\definecolor{famLi}{HTML}{D55E00}
\definecolor{dot}{HTML}{A8A8A8}
\definecolor{excl}{HTML}{E4E4E4}
\definecolor{intv}{HTML}{FBF0D4}
\definecolor{ink}{HTML}{303030}
\newcommand{\markF}[3]{\fill[#1] (#2,#3) circle[radius=@f@mm];}
\newcommand{\markH}[3]{\draw[#1, line width=@lw@pt, fill=white] (#2,#3) circle[radius=@h@mm];}
\tikzset{sq/.style={draw=ink, line width=0.3pt}}
\newcommand{\markQ}[3]{\filldraw[sq, fill=#1] (#2,#3) +(-@q@mm,-@q@mm) rectangle +(@q@mm,@q@mm);}
\newcommand{\markD}[2]{\fill[dot] (#1,#2) circle[radius=@d@mm];}
\newcommand{\mk}[1]{\tikz[baseline=-0.6ex]{#1}}
\begin{document}
@BEGIN@"""


def preamble(sans, sizes, border):
    """The document preamble: the marks of the given sizes, a sans-serif font if sans, and a border
    of the given width in mm."""
    t = PREAMBLE.replace('@FONTS@', r"\usepackage{sansmath}" "\n"
                         r"\renewcommand{\familydefault}{\sfdefault}" if sans else "")
    t = t.replace('@BEGIN@', r"\sansmath" if sans else "").replace('@border@', str(border))
    for k, v in sizes.items():
        t = t.replace(f'@{k}@', str(v))
    return t


def mark_tex(m, x, y):
    """The TeX command drawing the mark m of classify at (x, y)."""
    if m is None:
        return rf"\markD{{{x}}}{{{y}}}"
    if m == 'dep':
        return rf"\markH{{ink}}{{{x}}}{{{y}}}"
    if m[0] == 'fam':
        return rf"\markQ{{{FAMILY_COLOR[m[1]]}}}{{{x}}}{{{y}}}"
    return rf"\mark{'F' if m[2] else 'H'}{{{CLASS_COLOR[m[1]]}}}{{{x}}}{{{y}}}"


def sample(*marks, step=0.0):
    """A legend sample: the marks (macro, colour), side by side at distance step (in mm)."""
    x0 = -step * (len(marks) - 1) / 2
    body = "".join(
        rf"\markD{{{x0 + i * step:.2f}mm}}{{0mm}}" if m == 'markD' else
        rf"\{m}{{{c}}}{{{x0 + i * step:.2f}mm}}{{0mm}}" for i, (m, c) in enumerate(marks))
    return rf"\mk{{{body}}}"


def swatch(c):
    return rf"\mk{{\fill[{c}] (-1.4mm,-1.1mm) rectangle (1.4mm,1.1mm);}}"


def regions(x1, y1, along):
    """The two wedges and the five lines a = -2, alpha, alpha', -1, 0 from the origin to the edge
    x1 (along = 's') or y1 (along = 'r') of the frame."""
    pt = (lambda a: f"({x1},{a * x1:.3f})") if along == 's' else (lambda a: f"({a * y1:.3f},{y1})")
    out = [rf"\fill[excl] (0,0) -- {pt(-2)} -- {pt(ALPHA)} -- cycle;",
           rf"\fill[intv] (0,0) -- {pt(ALPHA)} -- {pt(ALPHA_PRIME)} -- cycle;"]
    out += [rf"\draw[ink!55, line width=0.4pt] (0,0) -- {pt(a)};"
            for a in (-2, ALPHA, ALPHA_PRIME, -1, 0)]
    return out


def legend_portrait():
    """The legend of the portrait picture, a tabular to the right of the plot."""
    def head(text, skip=True):
        space = r"\noalign{\vskip 1.4ex}" if skip else ""
        return rf"{space}\multicolumn{{2}}{{@{{}}l}}{{\bfseries {text}}} \\[0.3ex]"

    def row(marker, text):
        return rf"{marker} & {text} \\[0.4ex]"
    trio = lambda m: sample((m, 'cone'), (m, 'ctwo'), (m, 'cthree'), step=2.5 * PORTRAIT['f'])
    lines = [
        r"\begin{tabular}{@{}c@{\hspace{0.6em}}>{\raggedright\arraybackslash}p{5.35cm}@{}}",
        r"\multicolumn{2}{@{}l}{coprime $r, s$ with $s \ge 1$, $a = r/s$} \\[0.3ex]",
        head(r"Main theorem: circles"),
        r"& $(r, s) \bmod 4$ for $a \le -2$; for $a > \alpha$ \\[0.4ex]",
        row(sample(('markF', 'cone')), r"(C1): $(3,1)$, $(3,3)$; $(1,1)$, $(1,3)$"),
        row(sample(('markF', 'ctwo')), r"(C2): $(0,1)$, $(2,3)$; $(2,1)$, $(0,3)$"),
        row(sample(('markF', 'cthree')), r"(C3): $(1,0)$, $(1,2)$; $(3,0)$, $(3,2)$"),
        row(trio('markF'), r"two of (Z), (O), (T) hold, so $\rho_a$ is surjective"),
        row(trio('markH'), r"$c_1, c_2$ are $2$-dependent, so $\rho_a$ is not surjective"),
        head(r"The two families: squares"),
        row(sample(('markQ', 'famA')), r"$a = -\ell(\ell + 1) \le -2$, $\ell = j/k$, "
            r"$(j, k) \equiv (2,1), (3,3) \bmod 4$"),
        row(sample(('markQ', 'famLi')), r"$a = -(\ell^2 + \ell + 1) \le -2$, $\ell = j/k$, "
            r"$(j, k) \equiv (1,1), (2,3) \bmod 4$"),
        head(r"Not covered"),
        row(sample(('markH', 'ink')),
            r"$c_1, \dots, c_6$ are $2$-dependent, so $\rho_a$ is not surjective"),
        row(sample(('markD', None)), r"$c_1, \dots, c_6$ are $2$-independent"),
        row("", r"no mark: $\gcd(r, s) > 1$; $a$ appears at its reduced fraction, "
            r"whose residues mod $4$ may differ"),
        head(r"Regions"),
        rf"& $\alpha \approx {ALPHA:.3f}$, $\alpha' \approx {ALPHA_PRIME:.3f}$ \\[0.4ex]",
        row(swatch('excl'), r"$-2 < a \le \alpha$: not covered"),
        row(swatch('intv'), r"$\alpha < a \le \alpha'$; outside it, in the classes, $\rho_a$ is "
            r"surjective iff $c_1, c_2$ are $2$-independent"),
        r"\end{tabular}",
    ]
    return "\n".join(lines)


def picture_portrait(marks):
    """The denominator s across, the numerator r up, with a full legend on the right, at its final
    size: the width is that of a text block of 16 cm."""
    x0, x1, y0, y1 = 0.3, S_MAX + 0.7, R_MIN - 1.5, R_MAX + 1.5
    out = [preamble(False, PORTRAIT, 1),
           r"\begin{tikzpicture}[x=2.6mm, y=1.55mm]",
           rf"\begin{{scope}}\clip ({x0},{y0}) rectangle ({x1},{y1});",
           *regions(x1, y1, 's'), r"\end{scope}"]
    out += [mark_tex(m, s, r) for r, s, m in marks]
    out.append(rf"\draw[ink, line width=0.5pt] ({x0},{y0}) rectangle ({x1},{y1});")
    for s in (1, 5, 10, 15, 20, 25):
        out.append(rf"\draw[ink] ({s},{y0}) -- +(0,-1mm) node[below] {{${s}$}};")
    for r in range(-70, R_MAX + 1, 10):
        out.append(rf"\draw[ink] ({x0},{r}) -- +(-1mm,0) node[left] {{${r}$}};")
    out.append(rf"\node[below=5.5mm] at ({(x0 + x1) / 2},{y0}) {{denominator $s$}};")
    out.append(rf"\node[left=9.5mm, rotate=90, anchor=south] at ({x0},{(y0 + y1) / 2}) "
               r"{numerator $r$};")
    labels = [(-2, r"a = -2"), (ALPHA, r"a = \alpha"), (ALPHA_PRIME, r"a = \alpha'"),
              (-1, r"a = -1"), (0, r"a = 0")]
    for a, text in labels:
        out.append(rf"\node[right, ink] at ({x1},{a * x1:.3f}) {{${text}$}};")
    out.append(rf"\node[anchor=north west, inner sep=0pt, xshift=15.5mm] at ({x1},{y1}) "
               rf"{{{legend_portrait()}}};")
    out += [r"\end{tikzpicture}", r"\end{document}"]
    return "\n".join(out) + "\n"


def legend_slide():
    """The legend of the slide picture: four groups side by side, the headings over the texts."""
    step = 2.5 * SLIDE['f']
    groups = [
        [r"\bfseries Main theorem",
         ("", r"$(r, s) \bmod 4$ for $a \le -2 \mid a > \alpha$"),
         (sample(('markF', 'cone')), r"(C1)\enspace $(3,1), (3,3) \mid (1,1), (1,3)$"),
         (sample(('markF', 'ctwo')), r"(C2)\enspace $(0,1), (2,3) \mid (2,1), (0,3)$"),
         (sample(('markF', 'cthree')), r"(C3)\enspace $(1,0), (1,2) \mid (3,0), (3,2)$")],
        [r"\bfseries Families",
         (sample(('markQ', 'famA')), r"$a = -\ell(\ell + 1)$"),
         (sample(('markQ', 'famLi')), r"$a = -(\ell^2 + \ell + 1)$")],
        [r"\bfseries Marks",
         (sample(('markF', 'cone'), ('markQ', 'famA'), step=step), r"$\rho_a$ surjective"),
         (sample(('markH', 'cone'), ('markH', 'ink'), step=step), r"$\rho_a$ not surjective"),
         (sample(('markD', None)), r"not covered")],
        [r"\bfseries Regions",
         (swatch('excl'), r"$-2 < a \le \alpha$"),
         (swatch('intv'), r"$\alpha < a \le \alpha'$")],
    ]
    height = max(len(g) for g in groups)
    cells = [[("", g[0])] + g[1:] + [("", "")] * (height - len(g)) for g in groups]
    spec = r"@{\hspace{2.2em}}".join([r"c@{\hspace{0.5em}}l"] * len(groups))
    lines = [rf"\begin{{tabular}}{{@{{}}{spec}@{{}}}}"]
    for i in range(height):
        lines.append(" & ".join(f"{m} & {t}" for m, t in (c[i] for c in cells)) + r" \\")
    lines.append(r"\end{tabular}")
    return "\n".join(lines)


def picture_slide(marks):
    """The numerator r across, the denominator s up, with a compact legend below: for a slide."""
    x0, x1, y0, y1 = R_MIN - 1.2, R_MAX + 1.2, 0.3, S_MAX + 0.7
    out = [preamble(True, SLIDE, 1),
           r"\begin{tikzpicture}[x=1.6mm, y=2.15mm, font=\small]",
           rf"\begin{{scope}}\clip ({x0},{y0}) rectangle ({x1},{y1});",
           *regions(x1, y1, 'r'), r"\end{scope}"]
    out += [mark_tex(m, r, s) for r, s, m in marks]
    out.append(rf"\draw[ink, line width=0.5pt] ({x0},{y0}) rectangle ({x1},{y1});")
    for r in range(-70, R_MAX + 1, 10):
        out.append(rf"\draw[ink] ({r},{y0}) -- +(0,-1mm) node[below] {{${r}$}};")
    for s in (1, 5, 10, 15, 20, 25):
        out.append(rf"\draw[ink] ({x0},{s}) -- +(-1mm,0) node[left] {{${s}$}};")
    out.append(rf"\node[below=5.5mm] at ({(x0 + x1) / 2},{y0}) {{numerator $r$}};")
    out.append(rf"\node[left=7mm, rotate=90, anchor=south] at ({x0},{(y0 + y1) / 2}) "
               r"{denominator $s$};")
    labels = [(-2, r"a = -2"), (ALPHA, r"\alpha"), (ALPHA_PRIME, r"\alpha'"), (-1, r"-1"),
              (0, r"0")]
    for a, text in labels:
        out.append(rf"\node[above, ink] at ({a * y1:.3f},{y1}) {{${text}$}};")
    out.append(rf"\node[anchor=north, font=\footnotesize] at ({(x0 + x1) / 2},{y0}) "
               rf"[yshift=-12mm] {{{legend_slide()}}};")
    out += [r"\end{tikzpicture}", r"\end{document}"]
    return "\n".join(out) + "\n"


def render(name, tex, dpi):
    """Write name.tex next to this script and compile it to name.pdf and name.png."""
    (HERE / f"{name}.tex").write_text(tex)
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                        "-output-directory", tmp, str(HERE / f"{name}.tex")], check=True,
                       stdout=subprocess.DEVNULL)
        shutil.copy(Path(tmp) / f"{name}.pdf", HERE / f"{name}.pdf")
    subprocess.run(["pdftocairo", "-png", "-r", str(dpi), "-singlefile",
                    str(HERE / f"{name}.pdf"), str(HERE / name)], check=True)


def main():
    marks = [(r, s, classify(r, s)) for s in range(1, S_MAX + 1)
             for r in range(R_MIN, R_MAX + 1) if gcd(r, s) == 1]
    render("coverage", picture_portrait(marks), 300)
    render("coverage-slide", picture_slide(marks), 300)


if __name__ == "__main__":
    main()
