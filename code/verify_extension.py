"""Reproducible numerical checks for the encoder research addendum.

These checks validate formulas and sharp-pair constructions. They do not
verify the topological proof or certify historical novelty.
Run from this file's directory: python verify_extension.py
"""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import brentq, minimize

ROOT = Path(__file__).resolve().parents[1] / 'results'
RNG = np.random.default_rng(20260913)
records = []


def check(name, error, tolerance, **details):
    records.append(dict(name=name, error=float(error), tolerance=float(tolerance),
                        passed=bool(error <= tolerance), **details))


def parabola(M):
    t = M / 2
    # Rationalized denominator avoids cancellation at large t.
    b = 2 / (1 + 2 * t / (np.sqrt(t*t+2) + t))
    a = np.sqrt(b*(2-b))
    return a, b, -1.


def quartic(M):
    rho = brentq(lambda r: 8*r*r*(1+r)*(1+3*r)-M*M*(1-3*r),
                 0., 1/3, xtol=5e-15)
    d = 1+2*rho+9*rho*rho
    a = np.sqrt(8*rho/d)
    b = 2/((1+rho)*np.sqrt(d))
    c = -(1+2*rho+3*rho*rho)/((1+rho)*np.sqrt(d))
    return rho, a, b, c


grid = np.linspace(-1, 1, 10001)
for M in [.2, .5, 1., 2., 4., 8., 20.]:
    a, b, c = parabola(M)
    lam = 1/(M*M/(a*a)+1/(b*b))
    check(f'parabola stationary M={M}',
          abs(M*M*b*(b-1)-(2-b)**2), 2e-12)
    check(f'parabola peak identity M={M}',
          np.max(np.abs(a*a*grid**2+(b*grid**2-1)**2
                        -(1-b*b*grid**2*(1-grid**2)))), 2e-14)
    check(f'parabola optimum identity M={M}',
          abs(lam-b*b*(b-1)), 2e-14)

quartic_records = []
for M in [.2, .5, 1., 2., 4., 8., 20.]:
    r, a, b, c = quartic(M)
    A, B = a*a, b*b
    lam = 1/(M*M/A+1/B)
    eta = 2/(B*B*(1+r)**3*(1-r))
    zeta = eta*(1+r)/(1-3*r)
    residuals = np.array([
        -M*M/A**2+eta*r+zeta,
        -2/b**3+2*eta*(b*r*r+c)*r*r+2*zeta*(b+c),
        2*eta*(b*r*r+c)+2*zeta*(b+c),
    ])
    check(f'quartic KKT M={M}',
          np.max(np.abs(residuals))/(1+eta+zeta), 2e-12)
    t = grid**2
    check(f'quartic continuum factor M={M}',
          np.max(np.abs(1-(A*t+(b*t*t+c)**2)
                        -B*(1-t)*(t-r)**2*(t+1+2*r))), 3e-14)
    check(f'quartic multipliers M={M}', max(0., -eta, -zeta), 0.)
    quartic_records.append(dict(M=M, rho=r, a=a, b=b, c=c,
                                lambda_over_K2P=lam, eta=eta, zeta=zeta))

# All-pair lower bounds, including nonsymmetric mean slopes and sheared maps.
for K in [4, 5, 8, 17]:
    for p in [2, 4]:
        for target in ['jensen', 'shifted_mean', 'exponential_mean']:
            X = RNG.uniform(-1, 1, (12000, K))
            Y = RNG.uniform(-1, 1, (12000, K))
            S, T = X.sum(axis=1), (X**p).sum(axis=1)
            U, W = Y.sum(axis=1), (Y**p).sum(axis=1)
            if target == 'jensen':
                psi = lambda m: m**p
                slopes = np.array([-p, p])
            elif target == 'shifted_mean':
                psi = lambda m: (m+.3)**2
                slopes = np.array([-1.4, 2.6])
            else:
                psi = np.exp
                slopes = np.exp(np.array([-1., 1.]))
            E = np.array([[1.2, .3], [-.2, .8]])
            G = E.T@E
            w = np.column_stack((-slopes, np.ones(2)))
            L2 = max(v@np.linalg.solve(G,v) for v in w)
            df = (T-W)/K-psi(S/K)+psi(U/K)
            dm = np.column_stack((S-U,T-W))
            d2 = np.einsum('ni,ij,nj->n',dm,G,dm)
            check(f'all pairs K={K}, p={p}, {target}',
                  max(0., np.max((K*K/L2)*df*df-d2)), 1e-10,
                  pair_count=len(X))

# Realized shrinking source pairs: two locally independent input entries
# implement the desired direction in the two-moment plane.
sharp_records = []
for K in [4, 7, 12]:
    for p in [2, 4]:
        for e in [.08, .04, .02]:
            x = np.full(K, 1-e)
            x[0] -= e/4
            x[1] += e/4
            if p == 2:
                a,b,c = parabola(2)
            else:
                _,a,b,c = quartic(4)
            G = np.diag([a*a,b*b])
            m = x.mean()
            w = np.array([-p*m**(p-1),1.])
            direction = np.linalg.solve(G,w)
            J = np.array([[1.,1.], [p*x[0]**(p-1),p*x[1]**(p-1)]])
            dx = np.linalg.solve(J,direction)
            dx *= 1e-5/np.max(np.abs(dx))
            y=x.copy()
            y[:2] += dx
            dm=np.array([y.sum()-x.sum(),np.sum(y**p)-np.sum(x**p)])
            df=np.mean(y**p)-y.mean()**p-np.mean(x**p)+x.mean()**p
            quotient=(dm@G@dm)/(df*df)
            local=K*K/(w@np.linalg.solve(G,w))
            check(f'realized local sharp pair K={K}, p={p}, eps={e}',
                  abs(quotient/local-1), .004)
            sharp_records.append(dict(K=K,p=p,epsilon=e,
                                      quotient_over_K2=quotient/(K*K),
                                      local_limit_over_K2=local/(K*K),
                                      global_limit_over_K2=1/(p*p/(a*a)+1/(b*b))))

# Gram rank reduction: discard a translation perpendicular to the feature plane.
for j in range(25):
    V=RNG.normal(size=(3,3))
    H=V.T@V
    G=H[1:,1:]
    h=H[1:,0]
    reduced=H.copy()
    reduced[0,0]=h@np.linalg.solve(G,h)
    features=np.column_stack((np.ones_like(grid),grid,np.exp(grid)))
    old=np.einsum('ni,ij,nj->n',features,H,features)
    new=np.einsum('ni,ij,nj->n',features,reduced,features)
    check(f'Gram projection dominance {j}',max(0.,np.max(new-old)),1e-10)
    check(f'Gram reduced determinant {j}',abs(np.linalg.det(reduced)),1e-8)

# Independent finite-constraint solver sanity check for the quartic KKT optimum.
r,a,b,c=quartic(4)
A=a*a
tg=np.linspace(0,1,1501)
def objective(v):
    return 16/v[0]+1/v[1]**2
def feasible(v):
    return 1-v[0]*tg-(v[1]*tg*tg+v[2])**2
finite=minimize(objective, [A*.85,b*.85,c*.85], method='SLSQP',
                bounds=[(1e-6,2),(1e-6,4),(-3,3)],
                constraints=[dict(type='ineq',fun=feasible)],
                options=dict(ftol=1e-12,maxiter=500))
check('finite solver matches quartic analytic objective',
      abs(finite.fun/objective([A,b,c])-1), 3e-7)

report=dict(seed=20260913,checks=len(records),
            passing=sum(r['passed'] for r in records),
            status='passed' if all(r['passed'] for r in records) else 'failed',
            notes=[
                'Numerical checks are not a proof of the topological rigidity theorem.',
                'The finite solver is a sanity check; the analytic KKT and peak factor give the continuum certificate.',
                'No Gaussian-MSE experiment or exhaustive novelty review was performed.'
            ],
            quartic_examples=quartic_records,sharp_pairs=sharp_records,
            finite_solver=dict(success=bool(finite.success),message=finite.message,
                               x=finite.x.tolist(),objective=float(finite.fun)),
            results=records)
(ROOT/'extension_rerun.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],checks=report['checks'],
                      passing=report['passing'],
                      failed=[x for x in records if not x['passed']],
                      quartic_M4=quartic_records[4]),indent=2))
if not all(r['passed'] for r in records):
    raise SystemExit(1)
