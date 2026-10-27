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

## Earlier proof found after the review (October 27, 2026)

A later search-engine and GitHub check found an earlier proof that the review
missed. Principia Math in Progress, *The sharp taxicab Erdős–Mordell
inequality*, MathDB 341671, is a write-up dated 12 September 2026 by its authors
and originally hosted on principia-math.com
([LaTeX source](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/site-backup/mathdb-341671/mathdb-341671-solution.tex)). It presents a proof that, for a strictly interior point of
any nondegenerate triangle in every real normed plane, the sum of distances to the
vertices is at least 3/2 times the sum of distances to the side lines, and also
to the side segments. It states that 3/2 is optimal in the taxicab plane. A Lean
formalization of the inequality, not of the sharpness example, was committed to
PrincipiaMathOrg/math-solutions on 26 October 2026
([Problem341671.lean](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/mathdb/Principia/MathDB/Problem341671.lean)).

The write-up date is author-entered and has not been independently confirmed.
Neither document has been reviewed here. On that record, Conjecture 1 had a
proof before this repository's work; this package is a separate proof with its
own Lean verification.

The Lean checks establish the mathematical statements in this repository.
Historical priority remains a separate scholarly question.
