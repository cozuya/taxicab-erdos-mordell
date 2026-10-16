# Provenance

**Chris Ozols, with AI-assisted proof development and formalization.** Chris
directed the work and verification. OpenAI assistants contributed to the proof,
Lean formalization, and preparation of this package. No exact model identity is
asserted here.

Private proof development and initial Lean verification took place on
**October 16, 2026 UTC**, as supported by privately retained working records.
This is a private development date. No public release date is recorded, and
[CITATION.cff](CITATION.cff) deliberately omits one.

## Verification evidence

The package uses Lean **4.35.0** at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Mathlib **v4.35.0** at
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
[TOOLCHAIN.json](TOOLCHAIN.json) and [lake-manifest.json](lake-manifest.json)
record the complete pins. [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) identifies the
source files, documentation, and verification configuration.

The [local verification report](evidence/verification.json),
[complete transcript](evidence/verification.log), and
[theorem and axiom output](evidence/kernel-check.log) are fresh checks of the
sources in this package. Their commands can be repeated with `./verify.sh`.
All five audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

[Hosted verification runs](https://github.com/cozuya/taxicab-erdos-mordell/actions/workflows/verify.yml)
produce their own reports. Each report records the actual commit, source hashes,
compiler and dependency pins, run URL, event, and repository visibility. Hosted
evidence is attached to the run that produced it, rather than inserted into the
earlier commit it verifies. Actions artifacts have finite retention; offline
copies are retained separately.

Hashes and commit IDs identify content and reveal changes relative to retained
copies. Hosted records establish that the identified package existed and passed
those checks by the run time. Commit dates are author-controlled. These records
do not establish first discovery, absence of earlier edits, sole unaided human
authorship, or guaranteed worldwide priority. Formal correctness and historical
assessment are separate questions.
