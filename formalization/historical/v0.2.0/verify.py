"""Compile the artifact and audit the axioms of every advertised result.

Run after installing the pinned dependencies: python3 verify.py
Only Python's standard library is required in addition to Lean/Lake.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
(OUT/'report.json').unlink(missing_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED = set(json.loads((ROOT / 'audit_targets.json').read_text()))
if not EXPECTED:
    raise SystemExit('The audit manifest is empty.')


def run(command, filename):
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / filename).write_text(result.stdout)
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(f'Failed with exit code {result.returncode}: {command}')
    if re.search(r'\bwarning:', result.stdout, re.IGNORECASE):
        raise SystemExit('Warnings require review; verification not certified.')
    return result.stdout


version = run(['lake', 'env', 'lean', '--version'], 'lean-version.txt').strip()
if 'version 4.24.0,' not in version:
    raise SystemExit('Unexpected Lean version.')
commit = run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
             'mathlib-commit.txt').strip()
if commit != 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7':
    raise SystemExit('Unexpected mathlib revision.')
run(['lake', '--wfail', '--no-cache', 'build'], 'build.log')
audit = run(['lake', 'env', 'lean', '--trust=0', 'Audit.lean'], 'axioms.log')
(OUT/'kernel-recheck.log').write_text(audit)
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit)
axioms = {name: [x.strip() for x in values.split(',') if x.strip()]
          for name, values in rows}
if set(axioms) != EXPECTED:
    raise SystemExit('The axiom report does not contain exactly the expected theorems.')
for name, dependencies in axioms.items():
    extra = set(dependencies) - ALLOWED
    if extra:
        raise SystemExit(f'Unexpected axioms for {name}: {sorted(extra)}')

files = [ROOT/'Analog.lean', ROOT/'Audit.lean', ROOT/'lakefile.toml',
         ROOT/'lake-manifest.json', ROOT/'lean-toolchain', ROOT/'verify.py',
         ROOT/'audit_targets.json', ROOT/'update_audit.py',
         *sorted((ROOT/'Analog').glob('*.lean'))]
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in files}
report = {
    'status': 'passed', 'lean_version': version,
    'mathlib_commit': 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7',
    'theorem_axioms': axioms, 'source_sha256': hashes,
    'kernel_recheck': 'lake env lean --trust=0 Audit.lean',
    'scope': 'Selected manuscript results. Complete coefficient-class operational score, '
             'SDP attainment and reconstruction, general sharp decoder and circular-Gaussian '
             'small-noise trace with clipping, continuous attained Gram frontier, enclosing-ellipse '
             'equivalence, explicit quadratic frontier, C2 grid certification and O(h^2) scaling, '
             'and criterion transfer. Unified extension: actual attainable-pair constraints, '
             'common-completion collisions, positive definiteness from identification, compactness '
             'and positive operational maximum over all coefficient curves. Continuous recovery, '
             'automatic smoothing, dense-chart propagation and endpoint integration are checked; '
             'the charts still require an unformalized planar topological argument. Approximate '
             'stability is proved for the actual compact encoder class conditional on exact-class '
             'identification. Unrestricted continuous rigidity, analytic identification and '
             'general endpoint-gradient specializations, and additional coverage-inventory '
             'obligations remain incomplete.',
}
(OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
print('PASS: compilation and theorem dependency audit completed.')

