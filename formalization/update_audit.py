"""Regenerate the explicit audit manifest after editing this proof project.

The proof files use ordinary named namespace/section blocks. Public theorem
and lemma declarations are audited individually; private helpers are covered
through the dependency chains of their public callers. This script does not
verify proofs; run verify.py after reviewing its generated manifest.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent
modules = sorted((ROOT / 'Analog').glob('*.lean'))
names = []
for path in modules:
    source = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    scopes = []
    for line in source.splitlines():
        if m := re.match(r'^(namespace|section)\s+(\S+)\s*$', line):
            scopes.append((m[1], m[2]))
        elif re.match(r'^section\s*$', line):
            scopes.append(('section', ''))
        elif m := re.match(r'^end(?:\s+(\S+))?\s*$', line):
            if not scopes:
                raise SystemExit(f'Unmatched scope end in {path.name}: {line}')
            kind, name = scopes.pop()
            if m[1] and m[1] != name:
                raise SystemExit(f'Unexpected scope end in {path.name}: {line}, expected {name}')
        elif m := re.match(r'^(?:@\[[^]]+\]\s*)*(theorem|lemma)\s+([^\s(:]+)', line):
            prefix = '.'.join(name for kind, name in scopes if kind == 'namespace')
            names.append(prefix + '.' + m[2] if prefix else m[2])
    if scopes:
        raise SystemExit(f'Unclosed scope in {path.name}: {scopes}')

if len(names) != len(set(names)):
    raise SystemExit('Duplicate names in generated audit manifest')
names.sort()
(ROOT / 'audit_targets.json').write_text(json.dumps(names, indent=2) + '\n')
(ROOT / 'Analog.lean').write_text(''.join(f'import Analog.{p.stem}\n' for p in modules))
checks = [
    'Analog.quadratic_variance_operational_optimal',
    'Analog.GeneralCollision.triple_collision_preserves_moments',
    'Analog.Quartic.quartic_optimal_all_power',
    'Analog.Decoder.sharp_uniform_decoder',
    'Analog.Decoder.zero_score_no_finite_uniform_decoder',
    'Analog.GramSynthesis.positive_sdp_synthesis',
    'Analog.DifferentialRigidity.planar_differential_rigidity',
    'Analog.GeneralScore.general_operational_score',
    'Analog.GeneralScore.general_score_small_distance_sharpness',
    'Analog.GeneralDesign.positive_sdp_operational_synthesis',
    'Analog.RigidityAnalysis.rigid_representation_of_local_fibers',
    'Analog.SmallNoise.leading_mse_power_exact',
    'Analog.SmallNoise.variance_leading_mse',
    'Analog.FrontierAttainment.frontier_attained_on_maximal_interval',
    'Analog.SynthesisAttainment.operational_maximum_attained',
]
text = 'import Analog\n\n'
text += '\n'.join('#print axioms ' + name for name in names) + '\n\n'
text += '\n'.join('#check ' + name for name in checks) + '\n'
text += '#print Analog.ArbitraryEncoder.varianceScore\n'
text += '#print Analog.Operational.Quotients\n'
text += '#print Analog.Curve.PeakFeasibleAt\n'
(ROOT / 'Audit.lean').write_text(text)
print(f'Generated audit of {len(names)} public declarations in {len(modules)} proof modules.')
