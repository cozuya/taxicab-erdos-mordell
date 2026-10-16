# Prior art

Maja Petrović, Branko Malešević, and Bojan Banjac,
*On the Erdős–Mordell inequality for triangles in taxicab geometry*,
Journal of Mathematical Inequalities **14** (2020), 1299–1319,
DOI [10.7153/jmi-2020-14-84](https://doi.org/10.7153/jmi-2020-14-84),
formulated the result proved here as **Conjecture 1**, printed page 1318 /
PDF page 20. [Paper](https://files.ele-math.com/articles/jmi-14-84.pdf#page=20) ·
[arXiv:1901.08758](https://arxiv.org/abs/1901.08758).

Their Theorem 2 establishes the coefficient $3/2$ for the restricted coordinate
positions analyzed in the paper: $A=(0,r)$, $B=(p,0)$, $C=(q,0)$, with the stated
sign and ordering cases and coordinate reflections. Conjecture 1 asks for every
triangle orientation. An arbitrary rotation cannot remove this distinction,
because it need not preserve taxicab distance.

The contribution of this package is a complete proof of that universal,
arbitrary-orientation inequality, with a Lean formalization and sharpness
verification. The proposed constant $3/2$ and the sharpness obstruction were
already present in the original literature. Coordinate-median minimization and
piecewise linear methods are established ingredients; they are not claimed as
new discoveries here.

A bounded AI-assisted literature search located no earlier resolution of this
exact conjecture in the sources searched. This is negative evidence within that
search's scope, not established worldwide priority or independent human
confirmation.

An access limitation remains: the full text of M. Ghandehari and H. Martini,
*On the Erdős–Mordell inequality for normed planes and spaces*, Studia Scientiarum
Mathematicarum Hungarica **55** (2018), 174–189,
DOI [10.1556/012.2018.55.2.1392](https://doi.org/10.1556/012.2018.55.2.1392),
was not accessed in that review. Its full scope has therefore not been checked.
No claim about resolving a differently scoped survey conjecture is made.

The Lean checks establish the mathematical statements in this repository.
Historical priority remains a separate scholarly question.
