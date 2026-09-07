# QuadraticIterates

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A complete formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of

> M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
> Arch. Math. **59** (1992), 239–244
> ([DOI: 10.1007/BF01197321](https://doi.org/10.1007/BF01197321)).

For an integer `a` such that `-a` is not a square, let `f_n` be the `n`-th iterate of
`f = X² + a`, let `K_n` be the splitting field of `f_n` over `ℚ`, and let `Ω_n = Gal(K_n/ℚ)`,
which always embeds into the `n`-fold iterated wreath product `[C₂]ⁿ`. The paper determines when
that embedding is an isomorphism: for a given `n` this happens exactly when the integers
`b_1, …, b_n` of a certain multiplicative decomposition of the iteration sequence are
2-independent in `ℚ*/(ℚ*)²`; and it happens for every `n` when `a > 0` with `a ≡ 1` or `2 mod 4`,
or `a < 0` with `a ≡ 0 mod 4` and `-a` not a square. All results of the paper are formalized,
with no `sorry` and no axioms beyond the three of Mathlib.

Also formalized are the extensions of the last result by H.-C. Li
(Arch. Math. **114** (2020), 265–269, [DOI: 10.1007/s00013-019-01390-x](https://doi.org/10.1007/s00013-019-01390-x);
Arch. Math. **117** (2021), 133–140, [DOI: 10.1007/s00013-021-01609-w](https://doi.org/10.1007/s00013-021-01609-w)):
the embedding is an isomorphism for every `n` when `a = -(4k+2)(4k+3)` or
`a = -((4k+1)(4k+2)+1)`, and, for `a < 0` with `a ≡ 3 mod 4` and `-a` not a square, exactly when
`-a - 1` is not a square. Li's first family is `a = -(8k+2)(8k+3)`, the case of even `k`; the odd
case is proved here by his argument, with a residue of the rescaled sequence modulo 8 in place of
one modulo 4.

Beyond the papers, the last result is extended to rational parameters `a = r/s`
([`QuadraticIterates/Rational`](QuadraticIterates/Rational)): for `a > −1` and for `a ≤ −2`, when
`(r, s)` lies in one of a few explicit residue classes modulo 8 and a *squarefree-level
certificate* holds (a modulus modulo which `r`, `−s` or `±s` is not a square, or a residue
condition modulo 8), the embedding is an isomorphism for every `n`. The rescaled iteration
sequence of `a` has integer numerators whose Möbius factors take the place of the `b_n`, and the
reflection mechanism of the paper works for them with a twist by a power of `s`; Chapter 6 of the
blueprint records the statements and the proofs.

For integer `a`, these three papers are everything that is unconditionally known: apart from that
half-family, no further value of `a` has been settled since 2021.
[Maximality for `x² + a`](https://michaelstollbayreuth.github.io/QuadraticIterates/literature.html)
(source: [`website/literature.html`](website/literature.html)) surveys the literature — it maps
the eight sign-and-residue classes of `a` against what is proved in each, links every box to the
declaration that formalizes it, and collects the neighbouring work that moves the basepoint off
the critical point, bounds finitely many levels, or assumes *abc* or Vojta.

## Contents

The Lean sources are in [`QuadraticIterates`](QuadraticIterates):

- [`ArchMath1992.lean`](QuadraticIterates/ArchMath1992.lean) and the folder
  [`QuadraticIterates/ArchMath1992`](QuadraticIterates/ArchMath1992): the paper itself, in five
  files — `Sequences` (the γ- and β-sequences over general rings and over `ℤ`), `Iterates` (the
  polynomials `f_n`, the fields `K_n`, the groups `Ω_n`), `Irreducibility`, `DegreeCriterion`
  and `Main` (the three main theorems);
- [`Li.lean`](QuadraticIterates/Li.lean) and the folder [`QuadraticIterates/Li`](QuadraticIterates/Li):
  the results of Li — `Residues` (the residues of the rescaled sequence for `a < 0`),
  `ArchMath2021` and `ArchMath2020` (the theorems of the two papers);
- [`QuadraticIterates/Mathlib`](QuadraticIterates/Mathlib): auxiliary declarations missing from
  the current version of Mathlib, stated in their natural generality and following Mathlib's
  directory structure; these are candidates for upstreaming.

[`formalization.yaml`](formalization.yaml) is the project's self-report in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) format; it
includes a table aligning each result of the paper with the declaration that formalizes it.
[`comparator/`](comparator) holds a [comparator](https://github.com/leanprover/comparator)
harness for the main result of Section 3, for the theorems of Li (the first one in its
strengthened form) and for the two rational-parameter theorems, one challenge per case.

## Blueprint

[`blueprint/`](blueprint) contains a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint that reproduces the paper — its definitions, statements and proofs — and links each
item to the declarations that formalize it. Its chapters 1–3 are the three sections of the
paper, with the numbering of the printed results preserved (Facts 1.0, Lemma 1.1, …, Lemma 2.2);
chapter 0 collects the definitions of the introduction, chapter 4 the general-purpose theory
developed under `QuadraticIterates/Mathlib`, and chapter 5 the results of Li. Every item is fully
formalized, so the dependency graph is entirely green.

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
this cannot be narrowed to the project's own modules. On CI it takes about 80 minutes and the
generated HTML is around 1.3 GB.

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
