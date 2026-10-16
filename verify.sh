#!/usr/bin/env bash
# Rebuild the project and retain all output, theorem types, axioms, and exit codes.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
for program in lean lake python3 sha256sum; do
  command -v "$program" >/dev/null || { printf 'Missing prerequisite: %s\n' "$program" >&2; exit 2; }
done
mkdir -p .build
log=.build/verification.log
started=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run() {
  printf '\n$'
  printf ' %q' "$@"
  printf '\n'
  "$@"
  local code=$?
  printf 'EXIT_CODE=%s\n' "$code"
  return "$code"
}
run_capture() {
  local capture=$1
  shift
  printf '\n$'
  printf ' %q' "$@"
  printf '  # output also saved to %s\n' "$capture"
  "$@" 2>&1 | tee "$capture"
  local codes=("${PIPESTATUS[@]}")
  local code=${codes[0]}
  if (( codes[1] != 0 )); then code=${codes[1]}; fi
  printf 'EXIT_CODE=%s\n' "$code"
  return "$code"
}
verify_main() {
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  run lean --version || return $?
  run lean --githash || return $?
  run lake --version || return $?
  run cat lean-toolchain || return $?
  run git -C .lake/packages/mathlib rev-parse HEAD || return $?
  run python3 scripts/audit.py pins || return $?
  run python3 scripts/audit.py sources || return $?
  run python3 scripts/check-package.py --sources-only || return $?
  run sha256sum --check SOURCE_SHA256SUMS || return $?
  run python3 scripts/audit.py hashes || return $?
  # Clean this package only; a bare `lake clean` would remove dependency caches.
  run lake clean taxicab_erdos_mordell || return $?
  run lake build || return $?
  run_capture .build/kernel-check.log lake env lean --trust=0 Verification.lean || return $?
  run python3 scripts/audit.py axioms .build/kernel-check.log || return $?
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  printf '\nMAIN_INEQUALITY=PASS\nEXACT_STATEMENT=PASS\nPOSITIVE_DENOMINATORS=PASS\nSHARPNESS=PASS\nSHARPNESS_DISTANCES=PASS\nAXIOM_AUDIT=PASS\n'
}
verify_main 2>&1 | tee "$log"
codes=("${PIPESTATUS[@]}")
code=${codes[0]}
if (( codes[1] != 0 )); then code=${codes[1]}; fi
finished=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run python3 scripts/audit.py record "$code" "$started" "$finished" 2>&1 | tee -a "$log"
record_codes=("${PIPESTATUS[@]}")
if (( record_codes[0] != 0 )); then code=${record_codes[0]}; fi
if (( record_codes[1] != 0 )); then code=${record_codes[1]}; fi
printf '\nVERIFY_EXIT_CODE=%s\n' "$code" | tee -a "$log"
exit "$code"
