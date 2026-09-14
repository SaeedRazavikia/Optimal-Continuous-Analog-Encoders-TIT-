#!/usr/bin/env python3
"""Second implementation of selected certificates and numerical cross-checks.

This script does not import certified_synthesis.py, finite_noise.py, or either
existing verification script. The certificate uses degree-48 positive Taylor
tails, reciprocation at negative arguments, and every principal minor.
This is independent implementation in the same environment, not external review.
Run from any directory: python /path/to/paper/code/independent_reproduce.py
Use --certificate-only with python -S for a standard-library-only certificate.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from itertools import combinations, permutations
from math import comb, factorial, sqrt
import argparse
import hashlib
import json
import platform

ROOT = Path(__file__).resolve().parents[1]


class Box:
    """Closed exact-rational interval, implemented separately from first verifier."""
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Box) else Box(x)

    def __add__(self, other):
        b = self.coerce(other)
        return Box(self.lo+b.lo, self.hi+b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        b = self.coerce(other)
        v = [self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi]
        return Box(min(v), max(v))

    __rmul__ = __mul__


def exp_box(x):
    """At 0<=x<=1, positive-series tail <= next_term/(1-x/50).

    After term 48, each successive term ratio is at most x/50. For x<0
    reciprocate the enclosure at -x. No floating arithmetic enters bounds.
    """
    x = F(x)
    assert abs(x) <= 1
    if x < 0:
        r = exp_box(-x)
        return Box(1/r.hi, 1/r.lo)
    term = F(1)
    total = term
    for j in range(1, 49):
        term *= x/j
        total += term
    first_omitted = term*x/49
    return Box(total, total + first_omitted/(1-x/50))


def determinant(a):
    n = len(a)
    ans = Box(0)
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        prod = Box(-1 if inversions % 2 else 1)
        for i in range(n):
            prod *= a[i][p[i]]
        ans += prod
    return ans


def positive_principal_minors(a):
    out = []
    for n in range(1, len(a)+1):
        for idx in combinations(range(len(a)), n):
            v = determinant([[a[i][j] for j in idx] for i in idx])
            assert v.lo > 0, (idx, float(v.lo))
            out.append({'indices': list(idx), 'verified_positive': True,
                        'lower_display': float(v.lo)})
    return out


def bilinear(a, x, y):
    return sum((x[i]*a[i][j]*y[j] for i in range(len(x))
                for j in range(len(y))), Box(0))


def certificate():
    path = ROOT/'results/certified_synthesis.json'
    p = json.loads(path.read_text())
    h = [[F(v) for v in row] for row in p['primal_witness']['H']]
    lam = F(p['primal_witness']['lambda'])
    g = [row[1:] for row in h[1:]]
    hm = positive_principal_minors(h)
    ws = [[-exp_box(s), Box(1)] for s in (-1, 1)]
    gm = []
    for w in ws:
        gm.append(positive_principal_minors(
            [[Box(g[i][j])-lam*w[i]*w[j] for j in range(2)] for i in range(2)]))

    verification = p['primal_witness']['verification']
    claimed_grid = F(verification['grid_peak_upper'])
    highest = F(0)
    n = int(verification['grid_points'])
    for k in range(n):
        s = F(2*k, n-1)-1
        z = [Box(1), Box(s), exp_box(s)]
        highest = max(highest, bilinear(h, z, z).hi)
    assert highest <= claimed_grid

    # q''=2H11 + 2H02 e^s + 2H12(s+2)e^s + 4H22 e^(2s).
    eu = exp_box(1).hi
    derivative_bound = (2*abs(h[1][1])+2*abs(h[0][2])*eu+
                        6*abs(h[1][2])*eu+4*abs(h[2][2])*eu*eu)
    assert derivative_bound <= 117
    spacing = F(2, n-1)
    before_scaling = claimed_grid + F(117)*spacing**2/8
    lower = lam/before_scaling
    assert before_scaling == F(verification['continuum_peak_upper_before_scaling'])
    assert lower == F(p['certified_bounds']['lower'])

    # Independently enforce the exact rank-two Schur reduction.
    gd = g[0][0]*g[1][1]-g[0][1]**2
    gi = [[g[1][1]/gd, -g[0][1]/gd], [-g[0][1]/gd, g[0][0]/gd]]
    ell = h[0][1:]
    reduced00 = sum(ell[i]*gi[i][j]*ell[j] for i in range(2) for j in range(2))
    assert 0 < reduced00 < h[0][0]
    reduced = [[v/before_scaling for v in row] for row in h]
    reduced[0][0] = reduced00/before_scaling
    zero = determinant(reduced)
    assert zero.lo == zero.hi == 0

    dual = p['dual_witness']
    weights = [F(v) for v in dual['weights']]
    assert all(v >= 0 for v in weights)
    ds = [[[F(v) for v in row] for row in dual[name]]
          for name in ('B_minus', 'B_plus')]
    dm = [positive_principal_minors(d) for d in ds]
    q = [[Box(0) for _ in range(3)] for _ in range(3)]
    for t, alpha in zip(dual['points'], weights):
        z = [Box(1), Box(t), exp_box(F(t))]
        for i in range(3):
            for j in range(3):
                q[i][j] += alpha*z[i]*z[j]
    for i in range(2):
        for j in range(2):
            q[i+1][j+1] -= ds[0][i][j]+ds[1][i][j]
    qm = positive_principal_minors(q)
    normal = sum((bilinear(d, w, w) for d, w in zip(ds, ws)), Box(0))
    assert normal.lo >= 1
    upper = sum(weights)
    assert upper == F(p['certified_bounds']['upper'])
    gap = (upper-lower)/upper
    assert 0 <= gap < F(6, 100000)
    return {
        'status': 'passed', 'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'method': 'Exact Fraction intervals; degree-48 positive Taylor tail and reciprocal bounds; all principal minors',
        'primal_minors': hm, 'score_minors': gm, 'dual_multiplier_minors': dm,
        'dual_residual_minors': qm, 'normalization_lower_display': float(normal.lo),
        'grid_points': n, 'independent_grid_peak_upper_display': float(highest),
        'derived_second_derivative_bound_display': float(derivative_bound),
        'claimed_derivative_bound_verified': 117,
        'rank_reduced_determinant_exact': '0',
        'schur_peak_reduction_display': float(h[0][0]-reduced00),
        'lower': str(lower), 'upper': str(upper),
        'lower_display': float(lower), 'upper_display': float(upper),
        'relative_gap_percent': float(gap*100),
        'scope': 'This certifies the recorded mathematical optimization witnesses; it does not certify all manuscript theorems or historical novelty.'}


def source_moments(prior, order):
    alpha = F(1) if prior == 'uniform' else F(3, 10)
    mu = [F(0)]*(order+1)
    mu[0] = F(1)
    for j in range(2, order+1, 2):
        mu[j] = mu[j-2]*F(j-1)/(2*alpha+j-1)
    return mu


def mean_moments(prior, k, order):
    # Raise the truncated source MGF to power K by polynomial convolution.
    # Coefficient n, multiplied by n!/K^n, is E[m^n].
    mu = source_moments(prior, order)
    factor = [mu[j]/factorial(j) for j in range(order+1)]
    poly = [F(1)]+[F(0)]*order
    for _ in range(k):
        poly = [sum(poly[j]*factor[n-j] for j in range(n+1))
                for n in range(order+1)]
    return [poly[j]*factorial(j)/k**j for j in range(order+1)]


def decimal(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def bisect(func, lo, hi):
    assert func(lo) < 0 < func(hi)
    for _ in range(240):
        mid = (lo+hi)/2
        if func(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2


def coefficients(p, m_squared):
    m2 = decimal(m_squared)
    if p == 2:
        # Solve the first-order equation, not the original radical formula.
        b = bisect(lambda b: m2*b*(b-1)-(2-b)**2, D(1), D(2))
        return ((b*(2-b)).sqrt(), b, D(-1)), None
    r = bisect(lambda r: 8*r*r*(1+r)*(1+3*r)-m2*(1-3*r), D(0), D(1)/3)
    d = 1+2*r+9*r*r
    return ((8*r/d).sqrt(), 2/((1+r)*d.sqrt()),
            -(1+2*r+3*r*r)/((1+r)*d.sqrt())), r


def polynomial_product(a, b):
    out = [D(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def raw_gaussian_mse_ratio(p, k, mm, a, b, noise):
    """Exact Gaussian polynomial moments for the *unclipped* readout.

    This auxiliary calculation is not substituted for the implemented decoder.
    It isolates the finite-polynomial correction to its small-noise limit.
    """
    n0 = decimal(noise)
    variance = n0/(2*k*k*a*a)
    answer = n0/(2*k*k*b*b)
    for j in range(1, p+1):
        for ell in range(1, p+1):
            degree = j+ell
            if degree % 2:
                continue
            double_factorial = 1
            for v in range(1, degree, 2):
                double_factorial *= v
            noise_moment = double_factorial*variance**(degree//2)
            answer += comb(p, j)*comb(p, ell)*decimal(mm[2*p-degree])*noise_moment
    return answer/n0


def analytical_checks():
    data = json.loads((ROOT/'results/finite_noise.json').read_text())
    crows = data['coefficients_and_scores']
    checks = []
    convergence = []
    with localcontext() as ctx:
        ctx.prec = 75
        for p in (2, 4):
            for prior in ('uniform', 'endpoint_beta'):
                for k in (4, 16):
                    mu = source_moments(prior, 6)
                    mm = mean_moments(prior, k, 6)
                    tmean = mu[p]-mm[p]
                    eff2 = p*p*mm[2*p-2]
                    for name, m2 in [('optimal', F(p*p)), ('prior_tuned', eff2)]:
                        abc, r = coefficients(p, m2)
                        a, b, c = abc
                        row = next(x for x in crows if (x['p'], x['prior'], x['K'], x['design']) == (p, prior, k, name))
                        err = max(abs(float(v)-w) for v, w in zip(abc, row['coefficients_a_b_c']))
                        assert err < 2e-12
                        score = 1/(D(p*p)/(a*a)+1/(b*b))
                        assert abs(float(score)-row['normalized_worst_case_squared_score']) < 2e-12
                        assert abs(float(mm[2*p-2])-row['mean_power_2p_minus_2']) < 1e-15
                        if p == 2:
                            peak_residual = abs(a*a-b*(2-b))
                        else:
                            rhs = polynomial_product([D(1), -D(1)], [r*r, -2*r, D(1)])
                            rhs = polynomial_product(rhs, [1+2*r, D(1)])
                            lhs = [1-c*c, -a*a, -2*b*c, D(0), -b*b]
                            peak_residual = max(abs(x-b*b*y) for x, y in zip(lhs, rhs))
                        assert peak_residual < D('1e-68')
                        limit = (1/(b*b)+decimal(eff2)/(a*a))/(2*k*k)
                        checks.append({'p': p, 'prior': prior, 'K': k, 'design': name,
                            'coefficient_max_difference': err,
                            'peak_polynomial_identity_residual': float(peak_residual),
                            'mean_power_exact': str(mm[2*p-2]),
                            'high_snr_mse_over_N0': float(limit),
                            'score': float(score)})
                        for snr in (20, 30):
                            empirical = next(x for x in data['rows'] if (x['p'], x['prior'], x['K'], x['snr_db']) == (p, prior, k, snr))
                            reported_limit = empirical['high_snr_mse_over_N0_'+name]
                            assert abs(float(limit)-reported_limit) < 2e-12
                            assert abs(float(tmean)-empirical['prior_mean']) < 1e-14
                            value = empirical['mse_'+name]/empirical['N0']
                            se = empirical['se_'+name]/empirical['N0']
                            raw_ratio = raw_gaussian_mse_ratio(p, k, mm, a, b,
                                                               F(str(empirical['N0'])))
                            convergence.append({'p': p, 'prior': prior, 'K': k,
                                'design': name, 'snr_db': snr,
                                'analytic_limit': float(limit), 'observed_mse_over_N0': value,
                                'standard_error_of_observed_ratio': se,
                                'unclipped_polynomial_exact_mse_over_N0': float(raw_ratio),
                                'relative_difference_percent': 100*(value/float(limit)-1),
                                'difference_in_reported_mc_standard_errors': (value-float(limit))/se})
    return {'status': 'passed', 'coefficient_and_moment_cells': len(checks),
        'method': '75-digit Decimal bisection of stationary equations; exact source-MGF polynomial convolution; coefficientwise peak identities',
        'checks': checks, 'finite_snr_comparisons': convergence,
        'comparison_scope': 'Finite-SNR outputs need not equal the small-noise limit. Differences include clipping and nonlinear terms plus Monte Carlo error. No universal agreement-within-confidence-interval assertion is made.'}


def pareto_spot_checks():
    path = ROOT/'results/pareto_frontier.json'
    if not path.exists():
        return {'status': 'not_run', 'reason': 'Optional Pareto data file absent'}
    data = json.loads(path.read_text())
    checks = []
    with localcontext() as ctx:
        ctx.prec = 75
        robust_b = 2/D(3).sqrt()
        robust_a2 = robust_b*(2-robust_b)
        star = 1/(4/robust_a2+1/(robust_b*robust_b))
        required = D(9)/10*star
        # Direct boundary polynomial, solved without the Pareto implementation.
        boundary = bisect(lambda b: b**3-2*b*b+3*required*b+2*required,
                          robust_b, D(2))
        for k in (4, 16):
            mm = mean_moments('uniform', k, 2)[2]
            (a0, b0, _), _ = coefficients(2, 4*mm)
            b = min(b0, boundary)
            a2 = b*(2-b)
            score = 1/(4/a2+1/(b*b))
            loss = decimal(4*mm)/a2+1/(b*b)
            robust_loss = decimal(4*mm)/robust_a2+1/(robust_b*robust_b)
            gain = 100*(1-loss/robust_loss)
            row = next(x for x in data['rows'] if x['prior']=='uniform' and
                       x['K']==k and x['required_retention']==.9)
            assert abs(float(b)-row['b']) < 2e-12
            assert abs(float(loss)-row['loss_coefficient_J']) < 2e-12
            assert abs(float(score)-row['normalized_separation']) < 2e-12
            assert abs(float(gain)-row['asymptotic_gain_percent_vs_robust']) < 2e-10
            assert abs(score-required) < D('1e-68')
            assert b0 > boundary and row['constraint_active']
            checks.append({'prior': 'uniform', 'K': k, 'required_retention': .9,
                'b': float(b), 'a': float(a2.sqrt()), 'c': -1,
                'loss_J': float(loss), 'normalized_separation': float(score),
                'active_score_constraint_residual': float(abs(score-required)),
                'asymptotic_gain_percent_vs_robust': float(gain),
                'peak_identity': '|E(s)|^2 = 1-b^2 s^2(1-s^2) <= 1',
                'status': 'passed'})
    return {'status': 'passed', 'cells': checks,
            'scope': 'Independent 75-digit reproduction of two analytic frontier points; no new finite-noise simulation or independent theorem proof.'}


def decoder_checks():
    # Compare the reusable routine against a received-plane halfspace projection,
    # not a second copy of its feature-coordinate correction formula.
    import random
    import numpy as np
    from decoders import strip_coordinates, decode_gap
    rng = random.Random(70139062)
    b = [[.6, .17], [-.13, .45]]
    c = [.1, -.2]
    det = b[0][0]*b[1][1]-b[0][1]*b[1][0]
    inverse = [[b[1][1]/det, -b[0][1]/det], [-b[1][0]/det, b[0][0]/det]]
    normal = inverse[0]
    norm2 = sum(v*v for v in normal)
    k = 7
    discrepancies = []
    for _ in range(128):
        y = [rng.uniform(-30, 30), rng.uniform(-30, 30)]
        shifted = [y[i]-k*c[i] for i in range(2)]
        height = sum(normal[i]*shifted[i] for i in range(2))
        excess = height-max(-k, min(k, height))
        projected = [shifted[i]-excess*normal[i]/norm2 for i in range(2)]
        reference = [sum(inverse[i][j]*projected[j] for j in range(2))/k for i in range(2)]
        actual = strip_coordinates(np.array(y), np.array(c), np.array(b), k)
        discrepancies.append(max(abs(actual[i]-reference[i]) for i in range(2)))
        value = float(decode_gap(np.array(y), np.array(c), np.array(b), k, lambda x: x*x))
        discrepancies.append(abs(value-(reference[1]-reference[0]*reference[0])))
    assert max(discrepancies) < 3e-13
    return {'status': 'passed', 'observations': 128, 'comparisons': len(discrepancies),
            'max_absolute_difference': max(discrepancies),
            'method': 'Independent Euclidean halfspace projection in received coordinates compared with reusable strip decoder',
            'numpy': np.__version__}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate-only', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT/'results/independent_reproduction.json')
    args = parser.parse_args()
    report = {'status': 'passed', 'review_type': 'Independent implementation in the same computational environment; no external human or different-machine review',
              'python': platform.python_version(), 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certificate': certificate()}
    if not args.certificate_only:
        report['analytic_numerical_claims'] = analytical_checks()
        report['decoder'] = decoder_checks()
        report['pareto_spot_checks'] = pareto_spot_checks()
    args.output.parent.mkdir(exist_ok=True, parents=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'passed', 'certificate_gap_percent': report['certificate']['relative_gap_percent'],
        'analytic_cells': report.get('analytic_numerical_claims', {}).get('coefficient_and_moment_cells', 0),
        'decoder_comparisons': report.get('decoder', {}).get('comparisons', 0),
        'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
