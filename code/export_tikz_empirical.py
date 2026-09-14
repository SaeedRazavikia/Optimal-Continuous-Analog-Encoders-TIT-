#!/usr/bin/env python3
"""Export archived experiments and analytic frontiers for native PGFPlots.

Run from any working directory. This script uses only the Python standard
library, does not draw new random samples, and does not modify result files.
The analytic formulas match code/pareto_frontier.py. Every saved design point
and each plateau transition is checked before its plot table is written.
"""
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures' / 'data'
B_ROBUST = 2.0 / math.sqrt(3.0)
LAMBDA_STAR = 4.0 / (9.0 + 6.0 * math.sqrt(3.0))


def write_table(name, columns, rows):
    path = OUT / name
    with path.open('w', encoding='ascii', newline='\n') as stream:
        stream.write(' '.join(columns) + '\n')
        for row in rows:
            stream.write(' '.join(format(float(x), '.16g') for x in row) + '\n')


def score(b):
    return b * b * (2.0 - b) / (3.0 * b + 2.0)


def loss(b, mu):
    return 4.0 * mu / (b * (2.0 - b)) + 1.0 / (b * b)


def prior_b(mu):
    t = math.sqrt(mu)
    return 2.0 / (1.0 + 2.0 * t / (math.sqrt(t * t + 2.0) + t))


def selected_b(eta, mu):
    b0 = prior_b(mu)
    if eta <= score(b0) / LAMBDA_STAR:
        return b0
    if eta == 1.0:
        return B_ROBUST
    lo, hi = B_ROBUST, b0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if score(mid) >= eta * LAMBDA_STAR:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def gain(eta, mu):
    return 100.0 * (1.0 - loss(selected_b(eta, mu), mu)
                    / loss(B_ROBUST, mu))


def export_finite_noise():
    payload = json.loads((ROOT / 'results' / 'finite_noise.json').read_text())
    count = 0
    for target in ('variance', 'quartic_gap'):
        for prior in ('uniform', 'endpoint_beta'):
            for K in (4, 16):
                group = sorted((r for r in payload['rows']
                                if r['target'] == target
                                and r['prior'] == prior and r['K'] == K),
                               key=lambda r: r['snr_db'])
                assert len(group) == 9
                for r in group:
                    assert abs(r['gain_ci95_hi'] - r['gain_percent']
                               - 1.96*r['paired_se_gain_percent']) < 1e-12
                    assert abs(r['gain_percent'] - r['gain_ci95_lo']
                               - 1.96*r['paired_se_gain_percent']) < 1e-12
                write_table(f'finite_noise_{target}_{prior}_K{K}.dat',
                            ('snr', 'robust', 'robusterr', 'prior', 'priorerr'),
                            ((r['snr_db'], r['gain_percent'],
                              1.96*r['paired_se_gain_percent'],
                              r['tuned_gain_percent_vs_baseline'],
                              1.96*r['paired_se_tuned_gain_percent'])
                             for r in group))
                count += len(group)
    assert count == len(payload['rows']) == 72
    return count


def export_pareto():
    payload = json.loads((ROOT / 'results' / 'pareto_frontier.json').read_text())
    max_error = 0.0
    for row in payload['rows']:
        b = selected_b(row['required_retention'], row['mean_square'])
        error = abs(b - row['b'])
        max_error = max(max_error, error)
        assert error < 1e-12
        assert abs(loss(b, row['mean_square'])
                   - row['loss_coefficient_J']) < 1e-12
    for scenario in payload['scenarios']:
        prior, K = scenario['prior'], scenario['K']
        mu = scenario['mean_square']
        threshold = score(prior_b(mu)) / LAMBDA_STAR
        assert abs(threshold - scenario['unconstrained_retention']) < 1e-12
        # Include the exact transition and resolve the square-root endpoint.
        eta = sorted({0.5 + 0.5*j/300 for j in range(301)}
                     | {1.0 - 0.5*(j/200)**2 for j in range(201)}
                     | {threshold})
        write_table(f'pareto_{prior}_K{K}.dat', ('eta', 'gain'),
                    ((x, gain(x, mu)) for x in eta))
        write_table(f'pareto_transition_{prior}_K{K}.dat', ('eta', 'gain'),
                    [(threshold, gain(threshold, mu))])
    mu = 1.0 / 48.0  # iid Uniform[-1,1], K=16
    for name, b in (('robust', B_ROBUST),
                    ('retention90', selected_b(0.9, mu)),
                    ('prior', prior_b(mu))):
        a = math.sqrt(b * (2.0 - b))
        write_table(f'pareto_ellipse_{name}.dat', ('x', 'y'),
                    ((math.cos(2.0*math.pi*j/500)/a,
                      (1.0 + math.sin(2.0*math.pi*j/500))/b)
                     for j in range(501)))
    write_table('pareto_feature_curve.dat', ('x', 'y'),
                ((-1.0 + 2.0*j/250, (-1.0 + 2.0*j/250)**2)
                 for j in range(251)))
    write_table('pareto_contact_points.dat', ('x', 'y'),
                [(-1.0, 1.0), (0.0, 0.0), (1.0, 1.0)])
    return max_error


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    cells = export_finite_noise()
    error = export_pareto()
    print(json.dumps({'finite_noise_cells_exported': cells,
                      'pareto_saved_designs_checked': 32,
                      'maximum_coefficient_discrepancy': error,
                      'new_random_samples': 0,
                      'output_directory': str(OUT)}, indent=2))


if __name__ == '__main__':
    main()
