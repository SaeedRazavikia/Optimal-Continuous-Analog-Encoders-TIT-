"""Build both shared-source manuscript formats with local TeX runtime files.

Usage: python3 build.py [--format both|paper|submission]
"""
from pathlib import Path
import argparse
import hashlib
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build_runtime'
BUILD.mkdir(exist_ok=True)
ENV = os.environ.copy()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--format', choices=['both', 'paper', 'submission'], default='both')
FORMAT = parser.parse_args().format


def run(args, name, cwd=ROOT):
    path = BUILD / (name+'.log')
    with path.open('w') as out:
        p = subprocess.run(args, cwd=cwd, env=ENV, stdout=out,
                           stderr=subprocess.STDOUT)
    if p.returncode:
        print('\n'.join(path.read_text(errors='replace').splitlines()[-50:]))
        raise SystemExit(f'{name} failed')
    print(name+': completed')


for tool in ['pdftex','pdflatex','kpsewhich']:
    if shutil.which(tool) is None:
        raise SystemExit('Missing TeX dependency: '+tool)
fmt = subprocess.run(['kpsewhich','pdflatex.fmt'],capture_output=True,text=True)
if not fmt.stdout.strip():
    tree = Path('/usr/share/texlive/texmf-dist')
    ENV['TEXMF'] = str(tree)
    ENV['TEXMFVAR'] = str(BUILD/'texmf-var')
    ENV['TEXMFCONFIG'] = str(BUILD/'texmf-config')
    ENV['TEXFORMATS'] = str(BUILD)+os.pathsep
    if not (BUILD/'pdflatex.fmt').exists():
        run(['pdftex','-ini','-etex','-jobname=pdflatex','-progname=pdflatex',
             '-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],
            'format',BUILD)
    maproot = tree/'fonts/map/dvips'
    parts=['amsfonts/cm.map','amsfonts/cmextra.map','amsfonts/symbols.map',
           'amsfonts/latxfont.map','rsfs/rsfs.map','tetex/ps2pk35.map']
    (BUILD/'pdftex.map').write_text('\n'.join((maproot/p).read_text() for p in parts))
    ENV['TEXFONTMAPS'] = str(BUILD)+os.pathsep
targets = {
    'paper': ('manuscript', 'TIT_Paper_Revised.pdf'),
    'submission': ('manuscript_submission', 'TIT_Paper_Submission.pdf'),
}
for kind, (stem, output_name) in targets.items():
    if FORMAT != 'both' and FORMAT != kind:
        continue
    for n in range(3):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
             stem+'.tex'],f'{kind}_latex_pass_{n+1}')
    raw=(ROOT/(stem+'.pdf')).read_bytes()
    assert raw.rstrip().endswith(b'%%EOF'), 'PDF export is incomplete'
    (ROOT/output_name).write_bytes(raw)
    print(ROOT/output_name)
    print('Verified PDF bytes:',len(raw),'SHA256:',hashlib.sha256(raw).hexdigest())
