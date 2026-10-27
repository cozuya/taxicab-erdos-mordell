# Taxicab Erdős–Mordell Conjecture 1 — proof available

**Result:** A proof is available for **Conjecture 1** of Maja Petrović,
Branko Malešević, and Bojan Banjac's paper, *On the Erdős–Mordell
inequality for triangles in taxicab geometry* (2020; arXiv:1901.08758),
including arbitrary triangle orientations and the sharp coefficient 3/2.
The precise inequality and its sharpness are formally checked in Lean
4.35.0 with Mathlib v4.35.0.

**Historical status:** An earlier proof appears to exist: a
[Principia Math in Progress write-up](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/site-backup/mathdb-341671/mathdb-341671-solution.tex) for MathDB 341671, dated
12 September 2026, presents a proof of Conjecture 1 in a stronger form,
with a [Lean formalization](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/mathdb/Principia/MathDB/Problem341671.lean) published on 26 October 2026. The
bounded, AI-assisted literature search for this repository missed it; it
was found on 27 October 2026. **No novelty, first-discovery,
historical-priority, or official problem-list closure claim is made.** This page exists so
that other people considering work on the conjecture can find and
evaluate the proof.

**Exact statement:** For any nondegenerate triangle A, B, C in the
taxicab plane and any strictly interior point P, the sum of the
taxicab distances from P to the vertices is at least 3/2 times
the sum of the taxicab distances from P to the supporting lines
of the opposite sides. This holds without an orientation restriction,
and 3/2 is sharp. The "Exact statement" section of [README.md](README.md)
gives the exact barycentric and coordinate statement, including the
definition of distance to the infinite supporting lines.

**Original source:** [Petrović–Malešević–Banjac, Conjecture 1, printed
page 1318 / PDF page 20](https://files.ele-math.com/articles/jmi-14-84.pdf#page=20)
and [arXiv:1901.08758](https://arxiv.org/abs/1901.08758).

**Check this result:** [Readable proof](PROOF.md) ·
[Lean main theorem](Taxicab/Main.lean) ·
[Exact statement check](Verification.lean) ·
[Verification report](VERIFICATION_REPORT.md) ·
[GitHub Actions verification](https://github.com/cozuya/taxicab-erdos-mordell/actions/workflows/verify.yml) ·
[Prior-art review](PRIOR_ART.md) ·
[Provenance](PROVENANCE.md).

**Search names:** taxicab Erdos Mordell inequality; Conjecture 1
Petrovic Malesevic Banjac; Erdős–Mordell taxicab geometry conjecture
arbitrary orientations; coefficient 3/2 proof; Lean proof.

Repository: https://github.com/cozuya/taxicab-erdos-mordell

Overview page: https://cozuya.github.io/proofs/taxicab-erdos-mordell/
