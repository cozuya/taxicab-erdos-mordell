#!/usr/bin/env python3
"""Check the package inventory, manifest, evidence, and local documentation links."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
SOURCES = {
    'README.md', 'PROOF.md', 'PROVENANCE.md', 'PRIOR_ART.md', 'CITATION.cff',
    'VERIFICATION_REPORT.md', 'Taxicab.lean', 'Verification.lean',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'TOOLCHAIN.json',
    'verify.sh', '.gitignore', '.github/workflows/verify.yml',
    'scripts/install-lean.sh', 'scripts/fetch-deps.sh', 'scripts/audit.py',
    'scripts/check-package.py',
    *('Taxicab/' + n + '.lean' for n in
      ('Imports', 'Basic', 'Algebra', 'Median', 'Radial', 'Main', 'Sharpness')),
}
EVIDENCE = {'evidence/' + n for n in
            ('verification.log', 'kernel-check.log', 'verification.json')}
GENERATED = {'.git', '.lake', '.tools', '.build', '__pycache__'}


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def main():
    require(sys.argv[1:] in ([], ['--sources-only']), 'Unexpected arguments')
    sources_only = sys.argv[1:] == ['--sources-only']
    expected = SOURCES | EVIDENCE | {'SOURCE_SHA256SUMS'}
    required = SOURCES | {'SOURCE_SHA256SUMS'} | (set() if sources_only else EVIDENCE)
    present = set()
    for parent, dirs, files in os.walk(ROOT):
        dirs[:] = [n for n in dirs if n not in GENERATED]
        for name in files:
            path = Path(parent) / name
            require(not path.is_symlink(), 'Package must contain regular files')
            present.add(path.relative_to(ROOT).as_posix())
    require(not (present - expected), 'Unexpected package files')
    require(required <= present, 'Missing required package files')

    hashes = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(name in SOURCES and name not in hashes, 'Invalid manifest inventory')
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed digest')
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
                'Source hash mismatch: ' + name)
        hashes[name] = digest
    require(set(hashes) == SOURCES, 'Incomplete source manifest')

    links = 0
    for doc in sorted(ROOT.glob('*.md')):
        text = re.sub(r'```.*?```', '', doc.read_text(), flags=re.S)
        for match in re.finditer(r'\[[^\]\n]+\]\(([^)]+)\)', text):
            target = match.group(1).strip().strip('<>')
            url = urlsplit(target)
            if url.scheme or url.netloc:
                continue
            path = (doc.parent / unquote(url.path)).resolve() if url.path else doc
            relative = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else None
            require(relative in expected, 'Documentation link outside package')
            require(path.exists() or (sources_only and relative in EVIDENCE),
                    'Broken documentation link: ' + target)
            require(not url.fragment, 'Local anchor requires an explicit check')
            links += 1

    if not sources_only:
        report = json.loads((ROOT / 'evidence/verification.json').read_text())
        require(report['verification_exit_code'] == 0 and report['status'] == 'PASS',
                'Local verification did not pass')
        require(report['source_sha256'] == hashes, 'Evidence covers different sources')
        require(report['toolchain'] == json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
                'Evidence uses different pins')
        require('VERIFY_EXIT_CODE=0' in (ROOT / 'evidence/verification.log').read_text(),
                'Missing successful verification transcript')
    print(f'PASS: package inventory, {len(hashes)} source hashes, and {links} local links.')


if __name__ == '__main__':
    main()
