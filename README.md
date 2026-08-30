# QuadraticIterates

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

## Contents

The Lean sources are in [`QuadraticIterates`](QuadraticIterates):

- [`ArchMath1992.lean`](QuadraticIterates/ArchMath1992.lean) and the folder
  [`QuadraticIterates/ArchMath1992`](QuadraticIterates/ArchMath1992): the paper itself, in five
  files — `Sequences` (the γ- and β-sequences over general rings and over `ℤ`), `Iterates` (the
  polynomials `f_n`, the fields `K_n`, the groups `Ω_n`), `Irreducibility`, `DegreeCriterion`
  and `Main` (the three main theorems);
- [`QuadraticIterates/Mathlib`](QuadraticIterates/Mathlib): auxiliary declarations missing from
  the current version of Mathlib, stated in their natural generality and following Mathlib's
  directory structure; these are candidates for upstreaming.

[`formalization.yaml`](formalization.yaml) is the project's self-report in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) format; it
includes a table aligning each result of the paper with the declaration that formalizes it.
[`comparator/`](comparator) holds a [comparator](https://github.com/leanprover/comparator)
harness for the main result of Section 3.

## Blueprint

[`blueprint/`](blueprint) contains a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint that reproduces the paper — its definitions, statements and proofs — and links each
item to the declarations that formalize it. Its chapters 1–3 are the three sections of the
paper, with the numbering of the printed results preserved (Facts 1.0, Lemma 1.1, …, Lemma 2.2);
chapter 0 collects the definitions of the introduction and chapter 4 the general-purpose theory
developed under `QuadraticIterates/Mathlib`. Every item is fully formalized, so the dependency
graph is entirely green.

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
project imports, that is, all of Mathlib, so the first run takes a long time and produces several
gigabytes.

The [Pages workflow](.github/workflows/deploy-pages.yml) builds the blueprint and the
documentation and publishes them alongside the project website, under `/blueprint` and `/docs`.
It has to be triggered manually while the repository is private.

## Building

Ensure that you have a functioning Lean 4 installation (see the
[Lean installation guide](https://leanprover-community.github.io/get_started.html)), then run

```bash
lake exe cache get
lake build
```

in the root directory of this repository.
