# Verification and statement correspondence

The reproducible entry point is `./verify.sh`. Its complete output is retained in
[evidence/verification.log](evidence/verification.log), with machine-readable
metadata in [evidence/verification.json](evidence/verification.json) and exact
theorem types and axiom reports in
[evidence/kernel-check.log](evidence/kernel-check.log).

## What is checked

Points are explicitly `ℝ × ℝ`. In [Taxicab/Basic.lean](Taxicab/Basic.lean),
`d` is the sum of absolute coordinate differences, and `h` is the absolute
two-dimensional determinant divided by the maximum absolute side-coordinate
difference. It measures distance to the infinite supporting line.

`Taxicab.taxicab_erdos_mordell_strict` quantifies over arbitrary points `A B C`
and real weights `α β γ`. The only geometric hypothesis is the nonzero
determinant `det A B C ≠ 0`; the weights are strictly positive and sum to one.
For a noncollinear triangle these are exactly the barycentric conditions for a
strictly interior point. The theorem uses the point with coordinates
`(α*A.1 + β*B.1 + γ*C.1, α*A.2 + β*B.2 + γ*C.2)` and proves
`2*(d P A+d P B+d P C) ≥ 3*(h P B C+h P C A+h P A B)`, exactly the displayed
inequality in the README.

[Verification.lean](Verification.lean) imports the proof and independently
restates the target in raw coordinates. Its `exact_statement` contains the
determinant hypothesis, both absolute coordinate differences in every vertex
distance, and all three determinant-over-maximum line distances explicitly.
There is no axis-parallel-side hypothesis, rotation assumption, or median-inside
assumption. `exact_denominators_positive` separately proves that each denominator
is positive, so totalized division by zero is not used for a degenerate side.

In [Taxicab/Sharpness.lean](Taxicab/Sharpness.lean), `sharpness_distances` evaluates
the family $(-1,0),(1,0),(0,1),(0,\varepsilon)$ exactly. `sharpness` gives, for
every real $k>3/2$, a noncollinear triangle and strictly positive barycentric
weights witnessing failure of the stronger coefficient $k$.

## Commands and evidence

After installing the pinned compiler and fetching the locked dependencies:

```sh
./verify.sh
python3 scripts/check-package.py
```

The verification script records each command and exit code, including:

```sh
lean --version
lean --githash
lake --version
python3 scripts/audit.py pins
python3 scripts/audit.py sources
sha256sum --check SOURCE_SHA256SUMS
lake clean taxicab_erdos_mordell
lake build
lake env lean --trust=0 Verification.lean
python3 scripts/audit.py axioms .build/kernel-check.log
```

Cleaning removes this project's compiled modules before rebuilding all nine
sources. Pinned dependency caches are retained. The separate `--trust=0` run
checks the verification file with Lean's kernel checking enabled for imported
declarations as well. Mathlib is required; its complete dependency revisions are
in [lake-manifest.json](lake-manifest.json).

The five audited declarations are:

| Declaration | Scope |
| --- | --- |
| `Taxicab.taxicab_erdos_mordell_strict` | Main strict-interior theorem |
| `TaxicabVerification.exact_statement` | Raw-coordinate target |
| `TaxicabVerification.exact_denominators_positive` | Positive side denominators |
| `Taxicab.sharpness` | Quantified sharpness |
| `Taxicab.sharpness_distances` | Exact example distances |

Each actual `#print axioms` report must contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. These are standard Lean foundations.
The audit rejects missing reports and any different dependency set, including
`sorryAx` and project-specific axioms. Source checks also reject `sorry`, `admit`,
custom axiom declarations, and `native_decide`. Arithmetic certificates are
checked by Lean; external calculations are not a substitute for proof.

[SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) covers the proof, documentation, pins, and
verification scripts. It excludes itself and generated evidence to avoid a
self-referential manifest. The local report records those source hashes; hosted
reports additionally identify their actual commit and run. Reports from separate
runs have their own timestamps and are not interchangeable.

[GitHub Actions](https://github.com/cozuya/taxicab-erdos-mordell/actions/workflows/verify.yml)
repeats the complete checks and uploads only `verification.log`,
`kernel-check.log`, and `verification.json`, with 90-day artifact retention.
The workflow uses read-only repository permissions and pinned action revisions.
