# QuadraticIterates

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/QuadraticIterates/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/QuadraticIterates/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of a criterion for the arboreal
Galois representation of `f = X² + a`, `a ∈ ℚ`, to be surjective, and of the known results for
integer `a`, which follow from it.

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

The aim of this branch is not to reproduce the proofs of the paper and its successors, but to give
different, simpler proofs of their main results and to extend them to further cases and to rational
parameters. Instead of passing from the `c_n` to their Möbius quotients `b_n`, as those proofs do,
the formalization works with quadratic characters: every level is maximal if and only if, for
every `n ≥ 1`, some character `χ : ℚ* → {±1}` has `χ(c_n) = −1` and `χ(c_m) = 1` for all `m > n`.
Such characters (the sign, the parities of `p`-adic valuations, and characters induced by Dirichlet
characters) are found by short computations modulo a single prime power, and they give:

- a **criterion for rational parameters** `a = r/s`
  (`nonempty_mulEquiv_of_twoAdicClass_of_criteria`): if `a ≤ −2` or `a³ + 2a² + 2a + 2 > 0`, the
  pair `(r, s)` lies in one of three explicit 2-adic classes, and two of three explicit lists of
  conditions on `r` and `s` hold, then `Ω_n ≅ [C₂]ⁿ` for all `n`. Outside the interval
  `α < a ≤ a_* ≈ −1.31` this is sharp: in these classes every level is maximal as soon as the
  second one is (`forall_nonempty_mulEquiv_iff_twoIndependent_of_twoAdicClass`), that is, as soon
  as none of `−a`, `a(a + 1)` and `−a²(a + 1)` is a square. On `α < a < −1`, congruences of `r`
  and `s` modulo 32 (and, in one class, `|r|` not being a square in `ℚ₂`) give `Ω_n ≅ [C₂]ⁿ` with
  no further condition, for the proportion 245/576 ≈ 0.43 of the parameters there
  (`nonempty_mulEquiv_of_lt_neg_one_of_emod`);
- **two families** of rational parameters, `a = −j(j + 1)` and `a = −(ℓ² + ℓ + 1)` with `j`, `ℓ`
  in certain classes of fractions, outside the reach of the criterion;
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

There is no `sorry`, and no axiom beyond the three of Mathlib. The paper's own proofs, through
the `b_n` (part 2 of its Section 1 theorem, Lemmas 1.1, 2.1 and 2.2), and those of Li are
formalized on the `main` branch of this repository.

## Contents

The Lean sources are in [`QuadraticIterates`](QuadraticIterates):

- [`Galois`](QuadraticIterates/Galois): the iterates `f_n`, the fields `K_n` and the groups `Ω_n`,
  Odoni's embedding, the degree criterion and the criterion of the paper
  (`nonempty_mulEquiv_iff_twoIndependent`);
- [`Characters`](QuadraticIterates/Characters): patterns of characters along a sequence, and the
  criterion in terms of characters (`tfae_forall_nonempty_mulEquiv`);
- [`Sequence`](QuadraticIterates/Sequence): the sequence `c_n` for `a = r/s`, its integer
  numerators, signs and orbits modulo `N`;
- [`Patterns`](QuadraticIterates/Patterns): the values of characters along `c_n`, at the sign, at
  the primes of `r`, `s`, `r + s`, `r + 2s` and `r² + s²`, and at `2`, with the reflection and
  period-two mechanisms;
- [`Main`](QuadraticIterates/Main): the three lists of criteria, the 2-adic condition, the main
  theorem, the two families and the integer parameters;
- [`EvenPoly.lean`](QuadraticIterates/EvenPoly.lean): even polynomials and their iteration
  sequences, of which `c_n` is one;
- [`QuadraticIterates/Mathlib`](QuadraticIterates/Mathlib): auxiliary declarations missing from
  the current version of Mathlib, stated in their natural generality and following Mathlib's
  directory structure; these are candidates for upstreaming.

[`formalization.yaml`](formalization.yaml) is the project's self-report in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) format; it
includes a table aligning each result of the three papers with the declaration that formalizes
it, or recording that it is not formalized on this branch.
[`comparator/`](comparator) holds a [comparator](https://github.com/leanprover/comparator)
harness for the main result of Section 3 (one challenge per case), for the theorems of Li (the
first one in its strengthened form), and for the criterion for rational parameters and its three
corollaries, whose challenges reproduce the definitions of the 2-adic classes and lists of
conditions.

## Blueprint

[`blueprint/`](blueprint) contains a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint that develops the mathematics of this branch, with statements and proofs, and links each
item to the declarations that formalize it: chapter 1 the Galois-theoretic criterion, chapter 2
quadratic characters, chapter 3 the sequence `c_n`, chapter 4 the patterns of characters along it,
chapter 5 the lists of criteria and the main theorem, chapter 6 the two families, chapter 7 the
integer parameters, and chapter 8 the auxiliary theory. Every definition and theorem is
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
