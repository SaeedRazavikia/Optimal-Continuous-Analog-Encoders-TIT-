"""Bind the formalization inventory to the accompanying current Main.tex.

Run with --update after reviewing a manuscript revision; the default is a
read-only check. This records statements, not a claim that they are proved.
Only numbered theorem/proposition/lemma/corollary environments are inventoried.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
MANUSCRIPT = ROOT.parent / 'Main.tex'
TARGET = ROOT / 'manuscript_targets.json'


def inventory():
    raw = MANUSCRIPT.read_bytes()
    text = raw.decode('utf-8')
    # Preserve line numbers while excluding unescaped TeX comments.
    active = re.sub(r'(?<!\\)%[^\n]*', '', text)
    pattern = re.compile(
        r'\\begin\{(theorem|proposition|lemma|corollary)\}'
        r'(?:\[[^\]]*\])?.*?\\end\{\1\}', re.S)
    statements = []
    for match in pattern.finditer(active):
        statement = match.group()
        labels = re.findall(r'\\label\{([^}]+)\}', statement)
        result_labels = [label for label in labels
                         if label.startswith(('thm:', 'prop:', 'lem:', 'cor:'))]
        if not result_labels:
            raise SystemExit('A numbered result has no stable result label.')
        statements.append({
            'label': result_labels[0], 'aliases': result_labels[1:],
            'environment': match[1],
            'line': active[:match.start()].count('\n') + 1,
            'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
            'statement_latex': statement,
        })
    labels = [s['label'] for s in statements]
    if not labels or len(labels) != len(set(labels)):
        raise SystemExit('Missing or duplicate manuscript result labels.')
    return {'manuscript': '../Main.tex',
            'manuscript_sha256': hashlib.sha256(raw).hexdigest(),
            'statement_count': len(statements), 'statements': statements,
            'meaning': 'Source correspondence only; see COVERAGE.md for proof status.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--update', action='store_true')
    args = parser.parse_args()
    current = inventory()
    if args.update:
        TARGET.write_text(json.dumps(current, indent=2, ensure_ascii=False) + '\n')
        print(f'Recorded {current["statement_count"]} current manuscript statements.')
    else:
        if not TARGET.exists() or json.loads(TARGET.read_text()) != current:
            raise SystemExit('Manuscript inventory is stale. Review the changed proofs and '
                             'COVERAGE.md, then run python3 check_manuscript.py --update.')
        print(f'Manuscript correspondence is current: {current["statement_count"]} statements.')


if __name__ == '__main__':
    main()
