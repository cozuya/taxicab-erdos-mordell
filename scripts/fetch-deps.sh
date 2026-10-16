#!/usr/bin/env bash
# Lake materializes the existing lockfile; do not update dependency revisions.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
command -v lake >/dev/null || { printf 'Put the pinned Lean bin directory on PATH.\n' >&2; exit 2; }
before=$(sha256sum lake-manifest.json)
lake exe cache get \
  Mathlib.Basic.Real.Basic \
  Mathlib.Tactic.Convert \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Positivity \
  Mathlib.Tactic.Ring
[[ $(sha256sum lake-manifest.json) == "$before" ]]
python3 scripts/audit.py pins
