# QuadraticIterates

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of a criterion for the arboreal
Galois representation of `f = X² + a`, `a ∈ ℚ`, to be surjective, and of the known results for
integer `a`, which follow from it — once along new, simpler proofs that extend them to rational
parameters, and once along the proofs of the original papers.

Let `f_n` be the `n`-th iterate of `f`, let `K_n` be the splitting field of `f_n` over `ℚ`, and let
`Ω_n = Gal(K_n/ℚ)`, which always embeds into the `n`-fold iterated wreath product `[C₂]ⁿ`. By the
criterion of

> M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
> Arch. Math. **59** (1992), 239–244
> ([DOI: 10.1007/BF01197321](https://doi.org/10.1007/BF01197321)),

`Ω_n ≅ [C₂]ⁿ` exactly when `c_1, …, c_n` are 2-independent in `ℚ*/(ℚ*)²`, where `c_1 = −a` and
`c_{k+1} = c_k² + a`. This criterion is formalized for every rational `a`, together with Odoni's
embedding theorem, and without the paper's assumption that the iterates are irreducible:
maximality of `Ω_n` forces `f_1, …, f_n` to be irreducible.

The first formalization (Part I of the [blueprint](#blueprint)) does not reproduce the proofs of
the paper and its successors, but gives different, simpler proofs of their main results and
extends them to further cases and to rational parameters. Instead of passing from the `c_n` to their Möbius quotients `b_n`, as those proofs do,
the formalization works with quadratic characters: every level is maximal if and only if, for
every `n ≥ 1`, some character `χ : ℚ* → {±1}` has `χ(c_n) = −1` and `χ(c_m) = 1` for all `m > n`.
Such characters (the sign, the parities of `p`-adic valuations, and characters induced by Dirichlet
characters) are found by short computations modulo a single prime power, and they give:

- a **criterion for rational parameters** `a = r/s`
  (`nonempty_mulEquiv_of_twoAdicClass_of_criteria`): if `a ≤ −2` or `a³ + 2a² + 2a + 2 > 0`, the
  pair `(r, s)` lies in one of three explicit 2-adic classes, and two of three explicit lists of
  conditions on `r` and `s` hold, then `Ω_n ≅ [C₂]ⁿ` for all `n`. Outside the interval
  `α < a ≤ α′ ≈ −1.31` this is sharp: in these classes every level is maximal as soon as the
  second one is (`forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`), that is, as soon
  as none of `−a`, `a(a + 1)` and `−a²(a + 1)` is a square. On `α < a < −1`, congruences of `r`
  and `s` modulo 32 (and, in one class, `|r|` not being a square in `ℚ₂`) give `Ω_n ≅ [C₂]ⁿ` with
  no further condition, for the proportion 245/576 ≈ 0.43 of the parameters there
  (`nonempty_mulEquiv_of_lt_neg_one_of_emod`);
- **two families** of rational parameters, `a = −ℓ(ℓ + 1)` and `a = −(ℓ² + ℓ + 1)` with `ℓ` in
  certain classes of fractions, outside the reach of the criterion;
- the **results for integer `a`**, as the case `s = 1`: the main result of Section 3 of the
  paper (`a > 0` with `a ≡ 1` or `2 mod 4`, or `a < 0` with `a ≡ 0 mod 4` and `−a` not a square),
  and the theorems of H.-C. Li
  (Arch. Math. **114** (2020), 265–269, [DOI: 10.1007/s00013-019-01390-x](https://doi.org/10.1007/s00013-019-01390-x);
  Arch. Math. **117** (2021), 133–140, [DOI: 10.1007/s00013-021-01609-w](https://doi.org/10.1007/s00013-021-01609-w)):
  every level is maximal when `a = −(4k+2)(4k+3)` (Li's family `a = −(8k+2)(8k+3)` is the case of
  even `k`) or `a = −((4k+1)(4k+2)+1)`, and, for `a < 0` with `a ≡ 3 mod 4` and `−a` not a square,
  exactly when `−a − 1` is not a square.

For integer `a`, these three papers are everything that is unconditionally known: apart from the
values `a = −(4k+2)(4k+3)` with odd `k`, no further value of `a` has been settled since 2021.
[Maximality for `x² + a`](https://michaelstollbayreuth.github.io/QuadraticIterates/literature.html)
(source: [`website/literature.html`](website/literature.html)) surveys the literature — it maps
the eight sign-and-residue classes of `a` against what is proved in each, links every box to the
declaration that formalizes it, and collects the neighbouring work that moves the basepoint off
the critical point, bounds finitely many levels, or assumes *abc* or Vojta.

The plot [`plots/coverage.pdf`](plots/coverage.pdf) shows, for `1 ≤ s ≤ 26` and `−72 ≤ r ≤ 20`,
which `a = r/s` the criterion and the two families cover, coloured by 2-adic class and family, and
marks the uncovered `a` with `c_1, …, c_6` 2-dependent; [`plots/coverage.py`](plots/coverage.py)
generates it.

The second formalization (Part II of the blueprint) follows the paper and the two papers of Li
along their own proofs, through the Möbius quotients `b_n` of the sequence `c_n`: for an integer
`a` such that `−a` is not a square, the `b_n` are pairwise coprime integers with
`c_n = ∏_{d ∣ n} b_d`, so `Ω_n ≅ [C₂]ⁿ` for every `n` as soon as none of `|b_2|, |b_3|, …` is a
square (`section1_of_not_isSquare_abs_bSeq`); the paper and Li show this for the values of `a`
above by congruences for the `b_n` (`section3_main`, `nonempty_mulEquiv_of_eq_neg_mul`,
`li2021_theorem_3_9`, `li2020_theorem_3_5`). The two formalizations share the Galois-theoretic
foundation: the iterates, Odoni's embedding, the degree criterion and the criterion itself.

There is no `sorry`, and no axiom beyond the three of Mathlib.

## Contents

The Lean sources are in [`QuadraticIterates`](QuadraticIterates):

- [`Galois`](QuadraticIterates/Galois): the iterates `f_n`, the fields `K_n` and the groups `Ω_n`,
  Odoni's embedding, the degree criterion and the criterion of the paper
  (`nonempty_mulEquiv_iff_twoIndependent`);
- [`Characters`](QuadraticIterates/Characters): patterns of characters along a sequence, and the
  criterion in terms of characters (`tfae_forall_nonempty_mulEquiv`);
- [`Sequence`](QuadraticIterates/Sequence): the sequence `c_n` for `a = r/s`, its integer
  numerators, signs and orbits modulo `N`, its rigid divisibility and its `p`-adic valuations;
- [`Patterns`](QuadraticIterates/Patterns): the values of characters along `c_n`, at the sign, at
  the primes of `r`, `s`, `r + s`, `r + 2s`, `r² + s²` and `w_3`, and at `2`, with the reflection
  and period-two mechanisms;
- [`Main`](QuadraticIterates/Main): the three lists of criteria, the 2-adic condition, the main
  theorem, its corollaries, further criteria from the primes of `v_2`, `v_3` and `w_3`, the two
  families and the integer parameters;
- [`EvenPoly.lean`](QuadraticIterates/EvenPoly.lean): even polynomials and their iteration
  sequences, of which `c_n` is one;
- [`ArchMath1992`](QuadraticIterates/ArchMath1992) (with
  [`ArchMath1992.lean`](QuadraticIterates/ArchMath1992.lean)): the paper along its own proofs —
  `Sequences` (the iteration sequences of even polynomials and their Möbius quotients `β_n`, over
  general rings and over `ℤ`), `Iterates` (the sequence `c_n` for integer `a`, the irreducibility
  of the iterates, the rescaled polynomial) and `Main` (the integers `b_n`, the theorem of
  Section 1 and the main result of Section 3);
- [`Li`](QuadraticIterates/Li) (with [`Li.lean`](QuadraticIterates/Li.lean)): the results of Li
  along his proofs — `Residues` (the residues of the rescaled sequence for `a < 0`),
  `ArchMath2021` and `ArchMath2020` (the theorems of the two papers);
- [`QuadraticIterates/Mathlib`](QuadraticIterates/Mathlib): auxiliary declarations missing from
  the current version of Mathlib, stated in their natural generality and following Mathlib's
  directory structure; these are candidates for upstreaming.

[`formalization.yaml`](formalization.yaml) is the project's self-report in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) format; it
includes a table aligning each result of the three papers with the declarations that formalize
it, along both routes.
[`comparator/`](comparator) holds a [comparator](https://github.com/leanprover/comparator)
harness for the main result of Section 3 (one challenge per case), for the theorems of Li (the
first one in its strengthened form), and for the criterion for rational parameters and its three
corollaries, whose challenges reproduce the definitions of the 2-adic classes and lists of
conditions. A second configuration proves the six challenges about integer `a` along the proofs
of the original papers.

## Blueprint

[`blueprint/`](blueprint) contains a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint in two parts that develops the mathematics, with statements and proofs, and links each
item to the declarations that formalize it. In Part I, chapters 1–7 are the sections of the paper
M. Stoll, *When do all iterates of x² + a have maximal Galois group?* (preprint,
[`paper/arboreal-surjective.pdf`](paper/arboreal-surjective.pdf)), with the paper's numbering of
the statements: the introduction with the criterion of the 1992 paper, quadratic characters, sign
information, the characters `φ_n` for `n ≥ 2`, the Klein four-group of characters with the three
lists of criteria, the main result with its integer corollary, and the two quadratic families.
Each chapter opens with the supporting statements that the formalization needs beyond the
paper's, numbered with letters. Appendix A proves the criterion of the 1992 paper, appendix B
collects further formalized results (further criteria, refinements of the main theorem), and
appendix C the auxiliary theory. Part II reproduces the 1992 paper and the results of Li: its
chapters II.1–II.3 are the three sections of the paper, with the paper's numbering behind the
prefix II (Facts II.1.0, Lemma II.1.1, …, Lemma II.2.2), chapter II.4 collects the further
auxiliary theory and chapter II.5 the results of Li; the Galois-theoretic statements of the
paper's Section 1 are quoted from appendix A. Every definition and theorem is formalized, so the
dependency graph, which covers both parts, is entirely green.

To build it, install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and a TeX
distribution, then run in the root directory of this repository

```bash
leanblueprint pdf                       # blueprint/print/print.pdf
leanblueprint web                       # blueprint/web/index.html
lake env lean blueprint/checkdecls.lean # every \lean{...} name exists
```

The last step replaces `leanblueprint checkdecls`, which cannot be used here (see the comment in
[`blueprint/checkdecls.lean`](blueprint/checkdecls.lean)); it reads `blueprint/lean_decls`, which
`leanblueprint web` writes, so run it after that.

## API documentation

```bash
lake build QuadraticIterates:docs   # .lake/build/doc/index.html
```

generates the documentation with [doc-gen4](https://github.com/leanprover/doc-gen4), which is
required by `lakefile.toml` for this purpose only (a plain `lake build` does not build it; keep
its `rev` in sync with `lean-toolchain`). Note that the documentation covers everything the
project imports, that is, all of Mathlib: doc-gen4 walks the import closure by construction, so
this cannot be narrowed to the project's own modules. On CI it takes more than an hour, and the
generated HTML is around 0.5 GB.

The [Pages workflow](.github/workflows/deploy-pages.yml) builds the blueprint and the
documentation and publishes them alongside the project website — the sources of which are in
[`website/`](website), the literature survey among them — under `/blueprint` and `/docs`,
at <https://michaelstollbayreuth.github.io/QuadraticIterates/>. It runs on every push to `main`,
and can also be triggered by hand.

## Building

Ensure that you have a functioning Lean 4 installation (see the
[Lean installation guide](https://leanprover-community.github.io/get_started.html)), then run

```bash
lake exe cache get
lake build
```

in the root directory of this repository.
