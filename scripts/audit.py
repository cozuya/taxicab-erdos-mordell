#!/usr/bin/env python3
"""Audit build metadata and printed axiom dependencies, not mathematical truth."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
TARGETS = {
    'Taxicab.taxicab_erdos_mordell_strict',
    'TaxicabVerification.exact_statement',
    'Taxicab.sharpness',
    'Taxicab.sharpness_distances',
    'TaxicabVerification.exact_denominators_positive',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def manifest_hashes():
    entries = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed source digest')
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), 'Source path escapes project')
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, 'Source digest mismatch: ' + name)
        require(name not in entries, 'Duplicate source digest: ' + name)
        entries[name] = actual
    return entries


def axiom_reports(transcript):
    require(not re.search(r'\b(?:warning|error):', transcript),
            'Compiler warning or error in exact-statement check')
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", transcript)
    found = {}
    for name, axioms in records:
        require(name in TARGETS, 'Unexpected axiom report: ' + name)
        require(name not in found, 'Duplicate axiom report: ' + name)
        deps = {a.strip() for a in axioms.split(',') if a.strip()}
        require(deps == ALLOWED, 'Unexpected axiom dependencies: ' + name)
        found[name] = sorted(deps)
    require(set(found) == TARGETS, 'Missing axiom reports')
    return found


mode = sys.argv[1]
if mode == 'pins':
    pin = json.loads((ROOT / 'TOOLCHAIN.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() ==
            'leanprover/lean4:v' + pin['lean_version'], 'Toolchain file')
    require(output('lean', '--short-version') == pin['lean_version'], 'Lean version')
    require(output('lean', '--githash') == pin['lean_commit'], 'Lean commit')
    require(output('lake', '--version').startswith('Lake version ' + pin['lake_version']),
            'Lake version')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    require(mathlib['rev'] == pin['mathlib_commit'], 'mathlib revision')
    require(mathlib['inputRev'] == pin['mathlib_tag'], 'mathlib tag')
    for package in manifest['packages']:
        require(package['type'] == 'git' and
                re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                'Unpinned dependency: ' + package['name'])
        require(output('git', '-C', '.lake/packages/' + package['name'],
                       'rev-parse', 'HEAD') == package['rev'],
                'Dependency checkout: ' + package['name'])
    print('PASS: Lean, Lake, toolchain file, mathlib, and every locked dependency agree.')
elif mode == 'sources':
    paths = sorted([*ROOT.glob('*.lean'), *ROOT.glob('Taxicab/**/*.lean')])
    require(len(paths) == 9, 'Expected nine project Lean modules')
    forbidden = re.compile(r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by)\b')
    for path in paths:
        match = forbidden.search(path.read_text())
        require(match is None, 'Forbidden mechanism in ' + str(path.relative_to(ROOT)))
    print('PASS: all nine project Lean sources passed the forbidden-mechanism scan.')
elif mode == 'axioms':
    transcript = Path(sys.argv[2]).read_text()
    found = axiom_reports(transcript)
    for name in sorted(found):
        print('PASS:', name, 'uses exactly', ', '.join(sorted(found[name])))
    print('PASS: no sorryAx or project-specific axiom in any audited theorem.')
elif mode == 'hashes':
    for name, digest in manifest_hashes().items():
        print(digest, name)
elif mode == 'record':
    exit_code = int(sys.argv[2])
    commit = None
    try:
        git_root = Path(subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'], cwd=ROOT, text=True,
            stderr=subprocess.DEVNULL).strip()).resolve()
        if git_root == ROOT:
            commit = output('git', 'rev-parse', 'HEAD')
    except subprocess.CalledProcessError:
        pass
    dirty = output('git', 'status', '--porcelain', '--untracked-files=no') != '' if commit else None
    repository = os.environ.get('GITHUB_REPOSITORY')
    run_id = os.environ.get('GITHUB_RUN_ID')
    run_url = f'https://github.com/{repository}/actions/runs/{run_id}' if repository and run_id else None
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        require(commit == os.environ.get('GITHUB_SHA'), 'Commit differs from workflow SHA')
        require(dirty is False, 'Tracked sources changed during verification')
    actual_axioms = axiom_reports((ROOT / '.build/kernel-check.log').read_text()) if exit_code == 0 else None
    data = {
        'verification_exit_code': exit_code,
        'status': 'PASS' if exit_code == 0 else 'FAIL',
        'started_utc': sys.argv[3],
        'finished_utc': sys.argv[4],
        'repository_commit_at_run': commit,
        'tracked_worktree_dirty': dirty,
        'github_run_url': run_url,
        'github_event': os.environ.get('GITHUB_EVENT_NAME'),
        'repository_visibility': os.environ.get('REPOSITORY_VISIBILITY', 'local'),
        'identity_note': 'Precommit verification is identified by source hashes; timestamps do not establish priority.',
        'toolchain': json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
        'source_sha256': manifest_hashes(),
        'audited_theorems': sorted(TARGETS),
        'allowed_axioms': sorted(ALLOWED),
        'axiom_dependencies': actual_axioms,
        'transcript': 'verification.log',
        'theorem_types_and_axioms': 'kernel-check.log',
    }
    (ROOT / '.build/verification.json').write_text(json.dumps(data, indent=2) + '\n')
    print('Wrote .build/verification.json')
else:
    raise SystemExit('Unknown audit mode: ' + mode)
