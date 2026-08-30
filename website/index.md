---
layout: default
title: QuadraticIterates
---

<header class="page-header">
  <h1>{{ site.title }}</h1>
</header>

A complete formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of

> [Michael Stoll](https://www.mathe2.uni-bayreuth.de/stoll/),
> *Galois groups over ℚ of some iterated polynomials*,
> Arch. Math. **59** (1992), 239–244
> ([DOI: 10.1007/BF01197321](https://doi.org/10.1007/BF01197321)).

For an integer `a` such that `-a` is not a square, the paper determines when the Galois group
over ℚ of the `n`-th iterate of `X² + a` is the full iterated wreath power `[C₂]ⁿ`.

- [Blueprint]({{ site.baseurl }}/blueprint/) — the paper, with each definition and statement
  linked to the declaration that formalizes it
  ([PDF version]({{ site.baseurl }}/blueprint.pdf))
- [API documentation]({{ site.baseurl }}/docs/) — generated from the Lean sources
- [Source code](https://github.com/MichaelStollBayreuth/QuadraticIterates) on GitHub

<!-- To re-enable the upstreaming dashboard, restore the paragraph and
     `{% raw %}{% include _upstreaming_dashboard/dashboard.md %}{% endraw %}` from the git
     history and uncomment the dashboard step in .github/workflows/deploy-pages.yml. -->
