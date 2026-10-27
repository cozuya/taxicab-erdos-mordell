# Taxicab Erdős–Mordell Inequality: Proof of Conjecture 1

**By Chris Ozols, with AI-assisted proof development and formalization.**

> **Proof available; no novelty claim; an earlier proof appears to exist.**
> A [Principia Math in Progress write-up](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/site-backup/mathdb-341671/mathdb-341671-solution.tex) for MathDB 341671, dated
> 12 September 2026, presents a proof of Conjecture 1 in a stronger form
> (every real normed plane), and a [Lean formalization](https://github.com/PrincipiaMathOrg/math-solutions/blob/main/mathdb/Principia/MathDB/Problem341671.lean) of it was
> published on 26 October 2026. The bounded search for this repository missed
> it; it was found on 27 October 2026. I do not claim this is a first or novel
> proof, or that an external problem listing has been officially closed.
> This repository provides a checkable proof and Lean verification for
> anyone investigating the same statement. See [prior art](PRIOR_ART.md).

This repository proves **Conjecture 1 of Maja Petrović, Branko Malešević, and
Bojan Banjac**: the taxicab Erdős–Mordell inequality holds for every nondegenerate
triangle, in every orientation, and every strictly interior point. The coefficient
**3/2 is sharp**. The proof and sharpness statement are verified with
**Lean 4.35.0 and Mathlib v4.35.0**.

The conjecture appears on printed page 1318 / PDF page 20 of
[*On the Erdős–Mordell inequality for triangles in taxicab geometry*](https://files.ele-math.com/articles/jmi-14-84.pdf#page=20)
([arXiv:1901.08758](https://arxiv.org/abs/1901.08758)).

[Readable proof](PROOF.md) · [Lean proof](Taxicab/Main.lean) ·
[Exact-statement check](Verification.lean) ·
[Verification runs](https://github.com/cozuya/taxicab-erdos-mordell/actions/workflows/verify.yml) ·
[Verification report](VERIFICATION_REPORT.md) · [Provenance](PROVENANCE.md) ·
[Discovery summary](DISCOVERY.md) · [Prior art](PRIOR_ART.md) · [Citation](CITATION.cff) ·
[Overview page](https://cozuya.github.io/proofs/taxicab-erdos-mordell/)

## Exact statement

Use fixed coordinates on $\mathbb R^2$. For points $U,V$, set

```math
d(U,V)=|U_x-V_x|+|U_y-V_y|.
```

For distinct $U,V$, the distance from $P$ to their infinite supporting line is

```math
h(P;U,V)=
\frac{|(V_x-U_x)(P_y-U_y)-(V_y-U_y)(P_x-U_x)|}
{\max(|V_x-U_x|,|V_y-U_y|)}.
```

Let $A,B,C$ satisfy
$\det(B-A,C-A)\ne0$. For any positive real $\alpha,\beta,\gamma$ with
$\alpha+\beta+\gamma=1$, put $P=\alpha A+\beta B+\gamma C$. Then

```math
2\bigl(d(P,A)+d(P,B)+d(P,C)\bigr)
\ge 3\bigl(h(P;B,C)+h(P;C,A)+h(P;A,B)\bigr).
```

There is no orientation restriction. All three line-distance denominators are
proved positive. The distances are to the supporting lines, not to side segments;
arbitrary rotations are not symmetries of this metric.

For every real $k>3/2$, there is a nondegenerate triangle and a strictly interior
point with $\sum d<k\sum h$. The example
$A=(-1,0)$, $B=(1,0)$, $C=(0,1)$, $P=(0,\varepsilon)$ has
$\sum d=3+\varepsilon$ and $\sum h=2-\varepsilon$ for $0<\varepsilon<1$.

## Proof overview

Each side-line distance is at most the distance to either endpoint. This proves
the inequality on the boundary. The coordinatewise median of the three vertices
lies in the closed triangle, including coordinate ties. Within the triangle, the
sum of vertex distances equals its value at that median plus the distance to the
median, while the sum of line distances is affine.

Interpolation between the median and the boundary therefore reduces the problem
to the median. Coordinate reflections and an interchange of the axes put that
case into a form handled by a piecewise affine estimate and an exact polynomial
identity. [PROOF.md](PROOF.md) gives the full argument and the sharpness example.

## Reproduce the verification

On Linux x86_64, install Bash, Git, Python 3, curl, tar, zstd, and the usual
coreutils. For example, on Ubuntu:

```sh
sudo apt-get update
sudo apt-get install --yes git python3 curl tar zstd coreutils
git clone https://github.com/cozuya/taxicab-erdos-mordell.git
cd taxicab-erdos-mordell
bash scripts/install-lean.sh
export PATH="$PWD/.tools/lean-4.35.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh
./verify.sh
python3 scripts/check-package.py
```

If the exact Lean
toolchain is already installed, omit the installer and put its `bin` directory on
`PATH`, or set `LEAN_BIN_DIR` when running the fetch and verification scripts.
Other platforms can install the version in [lean-toolchain](lean-toolchain) and
run the same fetch and verification commands in Bash.

| Component | Pinned version or revision |
| --- | --- |
| Lean | 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | `5.0.0-src+eb6cafb` |
| Mathlib | v4.35.0, `56a005855ea17e0b0958f73ec801ae140b0a1679` |

[TOOLCHAIN.json](TOOLCHAIN.json) pins the Linux compiler archive by SHA-256.
[lake-manifest.json](lake-manifest.json) pins every dependency. The fetch script
checks that the lockfile is unchanged; reproduction does not require `lake update`.

`./verify.sh` cleans and rebuilds all nine project modules, then runs
`lake env lean --trust=0 Verification.lean`. It prints the theorem types and
audits the actual axiom reports for:

| Declaration | Checked result |
| --- | --- |
| `Taxicab.taxicab_erdos_mordell_strict` | The universal strict-interior inequality |
| `TaxicabVerification.exact_statement` | The same inequality in raw coordinates |
| `TaxicabVerification.exact_denominators_positive` | All three denominators are positive |
| `Taxicab.sharpness` | Every coefficient greater than 3/2 fails |
| `Taxicab.sharpness_distances` | The exact sums in the example above |

The only axiom dependencies of each audited declaration are `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axiom, or
`native_decide` is used. Reports in `.build/` retain commands, exit codes, theorem
types, axiom dependencies, tool versions, and source hashes. The committed
[local evidence](evidence/verification.json) identifies its sources by hash.

GitHub Actions repeats the checks on pushes, pull requests, manual runs, and a
change to public visibility. Its artifact identifies the checked commit and run;
it is separate from the committed local evidence.

Formal verification establishes the stated results within Lean's kernel and the
listed foundations. It does not establish historical priority. See
[PRIOR_ART.md](PRIOR_ART.md) for the bounded literature review and its access
limitation.

## License

Copyright 2026 Chris Ozols. The Lean proofs, scripts, and documentation in this
repository are licensed under the [Apache License, Version 2.0](LICENSE).
Third-party dependencies retain their respective licenses.
