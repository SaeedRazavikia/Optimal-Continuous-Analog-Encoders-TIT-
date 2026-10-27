"""Build every proof and audit public theorems against the current manuscript.

Install pinned Lean/mathlib dependencies, then run: python3 verify.py
A passed report certifies the Lean statements, not every manuscript theorem.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB = 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7'
REPORT = OUT / 'report.json'


def hashes():
    files = [ROOT / name for name in [
        'Analog.lean', 'Audit.lean', 'lakefile.toml', 'lake-manifest.json',
        'lean-toolchain', 'verify.py', 'audit_targets.json', 'update_audit.py',
        'check_manuscript.py', 'manuscript_targets.json',
    ]] + sorted((ROOT / 'Analog').glob('*.lean'))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files if p.exists()}


def save(report):
    tmp = REPORT.with_suffix('.tmp')
    tmp.write_text(json.dumps(report, indent=2) + '\n')
    tmp.replace(REPORT)


def run(command, filename):
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / filename).write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-16000:], end='')
        raise RuntimeError(f'Exit {result.returncode}: {command}; see verification/{filename}')
    if re.search(r'\bwarning:', result.stdout, re.IGNORECASE):
        raise RuntimeError(f'Warnings require review: verification/{filename}')
    print(f'PASS: {filename}', flush=True)
    return result.stdout


def main():
    report = {
        'status': 'running',
        'started_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_sha256': hashes(),
        'scope': 'Kernel audit of the explicit Lean declarations only. '
                 'Current manuscript coverage and remaining obligations are in COVERAGE.md; '
                 'a passing build does not certify all ten manuscript statements.',
    }
    save(report)
    try:
        run([sys.executable, 'check_manuscript.py'], 'manuscript-check.log')
        run([sys.executable, 'update_audit.py', '--check'], 'inventory-check.log')
        targets = json.loads((ROOT / 'audit_targets.json').read_text())
        expected = set(targets)
        if not expected or len(expected) != len(targets):
            raise RuntimeError('Empty or duplicate audit inventory.')
        version = run(['lake', 'env', 'lean', '--version'], 'lean-version.txt').strip()
        if 'version 4.24.0,' not in version:
            raise RuntimeError('Unexpected Lean version.')
        commit = run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
                     'mathlib-commit.txt').strip()
        if commit != MATHLIB:
            raise RuntimeError('Unexpected mathlib revision.')
        run(['lake', '--wfail', '--no-cache', 'build'], 'build.log')
        audit = run(['lake', 'env', 'lean', '--trust=0', 'Audit.lean'], 'axioms.log')
        (OUT / 'kernel-recheck.log').write_text(audit)
        rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit)
        axioms = {name: [x.strip() for x in values.split(',') if x.strip()]
                  for name, values in rows}
        if set(axioms) != expected or len(rows) != len(expected):
            raise RuntimeError('Axiom output does not match the explicit declaration inventory.')
        for name, dependencies in axioms.items():
            extra = set(dependencies) - ALLOWED
            if extra:
                raise RuntimeError(f'Unexpected axioms for {name}: {sorted(extra)}')
        if hashes() != report['source_sha256']:
            raise RuntimeError('Sources changed while verification was running; rerun.')
        manuscript = json.loads((ROOT / 'manuscript_targets.json').read_text())
        run([sys.executable, 'check_manuscript.py'], 'manuscript-check.log')
        report.update(status='passed', lean_version=version, mathlib_commit=commit,
                      theorem_axioms=axioms, declaration_count=len(axioms),
                      module_count=len(list((ROOT / 'Analog').glob('*.lean'))),
                      manuscript_sha256=manuscript['manuscript_sha256'],
                      manuscript_statement_count=manuscript['statement_count'],
                      kernel_recheck='lake env lean --trust=0 Audit.lean')
    except (OSError, ValueError, RuntimeError) as exc:
        report.update(status='failed', error=str(exc))
        print(f'FAIL: {exc}', file=sys.stderr)
    report['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
    save(report)
    if report['status'] != 'passed':
        return 1
    print(f'PASS: {report["declaration_count"]} declarations; compilation and kernel audit complete.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
