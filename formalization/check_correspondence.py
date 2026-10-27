"""Check the local paper-to-Lean correspondence catalog without paper source files.

This checks recorded excerpts, guide anchors, and audited Lean declaration links.
It does not download arXiv or prove that a Lean theorem is equivalent to prose.
Use --update only after reviewing changes to the excerpts or the reading guide.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
TARGET = 'paper_targets.json'
GUIDE = '../docs/STATEMENTS.md'
SHA256 = re.compile(r'[0-9a-f]{64}')
RESULT_LABEL = re.compile(r'(?:thm|prop|lem|cor):[a-z0-9-]+')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def declaration_sources(root):
    """Index the same public named declarations used by update_audit.py."""
    found = {}
    for path in sorted((root / 'Analog').glob('*.lean')):
        source = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
        scopes = []
        for line in source.splitlines():
            if match := re.match(r'^(namespace|section)\s+(\S+)\s*$', line):
                scopes.append((match[1], match[2]))
            elif re.match(r'^section\s*$', line):
                scopes.append(('section', ''))
            elif match := re.match(r'^end(?:\s+(\S+))?\s*$', line):
                require(bool(scopes), f'Unmatched scope end in {path.name}.')
                _, name = scopes.pop()
                require(not match[1] or match[1] == name,
                        f'Unexpected scope end in {path.name}.')
            elif match := re.match(
                    r'^(?:@\[[^]]+\]\s*)*(theorem|lemma)\s+([^\s(:]+)', line):
                prefix = '.'.join(name for kind, name in scopes if kind == 'namespace')
                name = prefix + '.' + match[2] if prefix else match[2]
                require(name not in found, f'Duplicate Lean declaration: {name}.')
                found[name] = path.relative_to(root).as_posix()
        require(not scopes, f'Unclosed scope in {path.name}.')
    return found


def validate(root=ROOT, update=False):
    root = Path(root)
    target = root / TARGET
    catalog = json.loads(target.read_text())
    require(isinstance(catalog, dict), 'Catalog must be a JSON object.')
    require(catalog.get('schema_version') == 1, 'Unsupported catalog schema.')
    paper = catalog.get('paper')
    require(isinstance(paper, dict), 'Missing paper metadata.')
    require(isinstance(paper.get('title'), str) and bool(paper['title'].strip()),
            'Missing paper title.')
    arxiv_id, version = paper.get('arxiv_id'), paper.get('version')
    require(isinstance(arxiv_id, str) and re.fullmatch(r'\d{4}\.\d{4,5}', arxiv_id),
            'Invalid arXiv identifier.')
    require(isinstance(version, str) and re.fullmatch(r'v[1-9]\d*', version),
            'An explicit arXiv version is required.')
    suffix = arxiv_id + version
    abstract_url = 'https://arxiv.org/abs/' + suffix
    html_url = 'https://arxiv.org/html/' + suffix
    require(paper.get('url') == abstract_url and paper.get('html_url') == html_url,
            'Paper URLs must match the recorded arXiv identifier and version.')
    require(isinstance(catalog.get('source_snapshot_sha256'), str)
            and SHA256.fullmatch(catalog['source_snapshot_sha256']),
            'Missing historical source-snapshot fingerprint.')
    require(catalog.get('guide') == GUIDE, 'Unexpected reading-guide path.')
    guide_bytes = (root / GUIDE).read_bytes()
    guide = guide_bytes.decode('utf-8')
    guide_hash = digest(guide_bytes)
    if not update:
        require(catalog.get('guide_sha256') == guide_hash,
                'Reading guide changed; review it, then run check_correspondence.py --update.')
    anchors = re.findall(r'<a\s+id=[\"\']([^\"\']+)[\"\']\s*>', guide)
    links = re.findall(r'\[[^\]]*\]\(([^)]+)\)', guide)
    inventory = json.loads((root / 'audit_targets.json').read_text())
    require(isinstance(inventory, list) and bool(inventory)
            and all(isinstance(name, str) for name in inventory)
            and len(inventory) == len(set(inventory)), 'Invalid Lean audit inventory.')
    inventory = set(inventory)
    sources = declaration_sources(root)
    statements = catalog.get('statements')
    require(isinstance(statements, list) and bool(statements), 'Missing paper statements.')
    require(type(catalog.get('statement_count')) is int
            and catalog['statement_count'] == len(statements), 'Statement count mismatch.')
    labels, numbers = set(), set()
    for item in statements:
        require(isinstance(item, dict), 'Every statement must be an object.')
        label = item.get('label')
        require(isinstance(label, str) and RESULT_LABEL.fullmatch(label),
                'Invalid statement label.')
        aliases = item.get('aliases')
        require(isinstance(aliases, list)
                and all(isinstance(a, str) and RESULT_LABEL.fullmatch(a) for a in aliases),
                f'Invalid aliases for {label}.')
        for name in [label] + aliases:
            require(name not in labels, f'Duplicate statement label or alias: {name}.')
            labels.add(name)
        environment = item.get('environment')
        require(environment in {'theorem', 'proposition', 'lemma', 'corollary'},
                f'Invalid statement environment for {label}.')
        number = item.get('paper_number')
        require(isinstance(number, str)
                and re.fullmatch(environment.capitalize() + r' [1-9]\d*', number),
                f'Invalid paper result number for {label}.')
        require(number not in numbers, f'Duplicate paper result number: {number}.')
        numbers.add(number)
        excerpt = item.get('statement_latex')
        require(isinstance(excerpt, str) and bool(excerpt.strip()),
                f'Missing statement excerpt for {label}.')
        require('\\begin{' + environment + '}' in excerpt
                and '\\end{' + environment + '}' in excerpt
                and '\\label{' + label + '}' in excerpt,
                f'Excerpt environment or label mismatch for {label}.')
        excerpt_hash = digest(excerpt.encode('utf-8'))
        if not update:
            require(item.get('statement_sha256') == excerpt_hash,
                    f'Statement excerpt hash mismatch for {label}.')
        for key in ['paper_statement_url', 'paper_proof_url']:
            url = item.get(key)
            require(isinstance(url, str) and url.startswith(html_url + '#')
                    and bool(re.fullmatch(r'[A-Za-z0-9_.:-]+', url[len(html_url) + 1:])),
                    f'{key} must point into the recorded arXiv version for {label}.')
            require(url in links, f'Reading guide does not link {key} for {label}.')
        anchor = item.get('guide_anchor')
        require(anchor == label.replace(':', '-'), f'Invalid guide anchor for {label}.')
        require(anchors.count(anchor) == 1, f'Missing or duplicate guide anchor: {anchor}.')
        require(item.get('coverage') in {'complete', 'partial'},
                f'Invalid coverage status for {label}.')
        declarations = item.get('lean_declarations')
        require(isinstance(declarations, list) and bool(declarations)
                and all(isinstance(name, str) for name in declarations)
                and len(declarations) == len(set(declarations)),
                f'Invalid Lean declaration list for {label}.')
        for name in declarations:
            require(name in inventory, f'Lean declaration is not audited: {name}.')
            require(name in sources, f'Lean declaration source is missing: {name}.')
            require(name in guide, f'Reading guide does not name Lean declaration: {name}.')
        expected_sources = sorted({sources[name] for name in declarations})
        require(item.get('lean_sources') == expected_sources,
                f'Lean source paths do not match declarations for {label}.')
        for source in expected_sources:
            require(any(link.split('#')[0] == '../formalization/' + source for link in links),
                    f'Reading guide does not link Lean source: {source}.')
        if update:
            item['statement_sha256'] = excerpt_hash
    if update:
        catalog['guide_sha256'] = guide_hash
        target.write_text(json.dumps(catalog, indent=2, ensure_ascii=False) + '\n')
    return catalog


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--update', action='store_true',
                        help='Refresh excerpt and guide hashes after manual correspondence review.')
    args = parser.parse_args()
    try:
        catalog = validate(update=args.update)
    except (OSError, ValueError, TypeError) as exc:
        parser.exit(1, f'FAIL: {exc}\n')
    action = 'Updated' if args.update else 'Checked'
    print(f'{action} local correspondence catalog: {catalog["statement_count"]} statements; '
          f'arXiv:{catalog["paper"]["arxiv_id"]}{catalog["paper"]["version"]}.')
    print('This checks recorded correspondence and source links, not mathematical equivalence to the paper.')


if __name__ == '__main__':
    main()
