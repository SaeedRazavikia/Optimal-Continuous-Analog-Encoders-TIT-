#!/usr/bin/env python3
"""Variance robustness/small-noise-MSE frontier, with reproducible evidence.

The analytic theorem supplies global optimality over continuous exact encoders.
The independent three-variable convex comparison below is a numerical check,
not an additional certificate or a claim of finite-noise MSE optimality.
Run from any directory: python code/pareto_frontier.py --trials 200000
"""
from pathlib import Path
import argparse
import csv
import json
import platform

import numpy as np
import scipy
from scipy.optimize import brentq, minimize
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
BASE_SEED = 2026091329
B_ROBUST = 2. / np.sqrt(3.)
LAMBDA_STAR = 4. / (9. + 6.*np.sqrt(3.))
RETENTIONS = (0., .25, .5, .75, .9, .95, .99, 1.)
SCENARIOS = (('uniform', 4), ('uniform', 16),
             ('endpoint_beta', 4), ('endpoint_beta', 16))


def mean_square(prior, K):
    alpha = 1. if prior == 'uniform' else .3
    return 1. / ((2.*alpha+1.)*K)


def robust_score(b):
    """Lambda_sq/(K^2 P), evaluated in a stable polynomial ratio."""
    return b*b*(2.-b)/(3.*b+2.)


def loss(b, mu):
    """2 K^2 P times the coefficient lim MSE/N0."""
    return 4.*mu/(b*(2.-b)) + 1./(b*b)


def unconstrained_b(mu):
    t = np.sqrt(mu)
    return 2. / (1. + 2.*t/(np.sqrt(t*t+2.)+t))


def upper_boundary(eta):
    if eta == 0.:
        return 2.  # Limiting boundary; not the selected nondegenerate encoder.
    if eta == 1.:
        return B_ROBUST
    return brentq(lambda b: robust_score(b)-eta*LAMBDA_STAR,
                  B_ROBUST, 2., xtol=5e-15)


def selected_b(eta, mu):
    return min(unconstrained_b(mu), upper_boundary(eta))


def convex_comparison(mu, eta):
    """Solve an independent convex problem in (A,b,c), without the reduction.

    Its endpoint peak constraints imply the complete continuum peak constraint
    because A t+(b t+c)^2 is convex in t=s^2 on [0,1].  No sampled peak grid is
    used.  Reflection/projection in the theorem justifies restricting to these
    orthogonal curves for a symmetric prior.
    """
    bound = 1./(eta*LAMBDA_STAR)
    def objective(x):
        A,b,c = x
        return 4.*mu/A+1./b**2
    def gradient(x):
        A,b,c = x
        return np.array([-4.*mu/A**2, -2./b**3, 0.])
    def constraint(x):
        A,b,c = x
        return np.array([1.-c*c, 1.-A-(b+c)**2,
                         bound-4./A-1./b**2])
    def jacobian(x):
        A,b,c = x
        return np.array([[0.,0.,-2.*c],
                         [-1.,-2.*(b+c),-2.*(b+c)],
                         [4./A**2,2./b**3,0.]])
    initial = np.array([B_ROBUST*(2.-B_ROBUST),B_ROBUST,-1.])
    res = minimize(objective, initial, jac=gradient, method='SLSQP',
                   bounds=((1e-8,1.),(1e-8,2.),(-1.,1.)),
                   constraints={'type':'ineq','fun':constraint,'jac':jacobian},
                   options={'ftol':1e-11,'maxiter':500})
    b = selected_b(eta,mu)
    analytic = loss(b,mu)
    row = {'mu':mu, 'retention':eta, 'success':bool(res.success),
           'message':str(res.message), 'iterations':int(res.nit),
           'A':float(res.x[0]),'b':float(res.x[1]),'c':float(res.x[2]),
           'minimum_constraint_residual':float(min(constraint(res.x))),
           'analytic_loss':float(analytic),'convex_loss':float(res.fun),
           'absolute_loss_discrepancy':float(abs(res.fun-analytic)),
           'relative_loss_discrepancy':float(abs(res.fun/analytic-1.))}
    # A linesearch termination can occur at a boundary optimum.  Preserve the
    # solver flag and assess the independent feasibility/value residuals below.
    assert row['minimum_constraint_residual'] > -1e-9, row
    assert row['relative_loss_discrepancy'] < 2e-8, row
    return row


def statistics(x):
    return float(np.mean(x)), float(np.std(x,ddof=1)/np.sqrt(x.size))


def paired_gain(reference, candidate):
    rbar=float(reference.mean())
    difference=reference-candidate
    delta=float(difference.mean())
    gain=100.*delta/rbar
    influence=100.*((difference-delta)/rbar-delta*(reference-rbar)/rbar**2)
    se=float(np.std(influence,ddof=1)/np.sqrt(reference.size))
    return gain,se


def experiment(n):
    rows=[]
    scenarios=[]
    comparisons=[]
    N0=.01
    for idx,(prior,K) in enumerate(SCENARIOS):
        mu=mean_square(prior,K)
        b0=unconstrained_b(mu)
        Jref=loss(B_ROBUST,mu)
        scenarios.append({'prior':prior,'K':K,'mean_square':mu,
                          'unconstrained_b':float(b0),
                          'unconstrained_retention':float(robust_score(b0)/LAMBDA_STAR),
                          'maximum_asymptotic_gain_percent':float(100.*(1.-loss(b0,mu)/Jref))})
        rng=np.random.default_rng(np.random.SeedSequence([BASE_SEED,idx]))
        s=(rng.uniform(-1.,1.,(n,K)) if prior=='uniform'
           else 2.*rng.beta(.3,.3,(n,K))-1.)
        m=s.mean(axis=1)
        q=(s*s).mean(axis=1)
        target=q-m*m
        z=rng.standard_normal((n,2))
        noise=np.sqrt(N0/2.)/K*z
        def errors(b):
            mh=np.clip(m+noise[:,0]/np.sqrt(b*(2.-b)),-1.,1.)
            qh=q+noise[:,1]/b
            estimate=np.clip(qh-mh*mh,0.,1.)
            return (estimate-target)**2
        reference=errors(B_ROBUST)
        mse_ref,se_ref=statistics(reference)
        for eta in RETENTIONS:
            b=selected_b(eta,mu)
            A=b*(2.-b)
            actual=robust_score(b)/LAMBDA_STAR
            J=loss(b,mu)
            assert actual >= eta-2e-13
            residual=abs(4.*mu*b0*(b0-1.)-(2.-b0)**2)
            assert residual < 2e-14
            error=errors(b)
            mse,se=statistics(error)
            gain,gain_se=paired_gain(reference,error)
            rows.append({'prior':prior,'K':K,'P':1.,'mean_square':mu,
                         'required_retention':eta,'actual_retention':float(actual),
                         'constraint_active':bool(eta>robust_score(b0)/LAMBDA_STAR),
                         'a':float(np.sqrt(A)),'b':float(b),'c':-1.,
                         'normalized_separation':float(robust_score(b)),
                         'loss_coefficient_J':float(J),
                         'mse_over_N0_limit':float(J/(2.*K*K)),
                         'asymptotic_gain_percent_vs_robust':float(100.*(1.-J/Jref)),
                         'snr_db':20.,'N0':N0,'trials':n,
                         'mse_at_20db':mse,'se_mse_at_20db':se,
                         'robust_mse_at_20db':mse_ref,'robust_se_mse_at_20db':se_ref,
                         'paired_gain_percent_at_20db':gain,
                         'paired_se_gain_percent_at_20db':gain_se,
                         'gain_ci95_lower':gain-1.96*gain_se,
                         'gain_ci95_upper':gain+1.96*gain_se,
                         'sample_seed_entropy':f'{BASE_SEED},{idx}'})
        for eta in (.5,.9,.99):
            check=convex_comparison(mu,eta)
            check.update({'prior':prior,'K':K})
            comparisons.append(check)
    return rows,scenarios,comparisons


def figure():
    plt.rcParams.update({'font.family':'serif','font.size':8,
                         'axes.labelsize':8,'axes.titlesize':8,
                         'xtick.labelsize':7,'ytick.labelsize':7,
                         'legend.fontsize':7,'pdf.fonttype':42})
    fig,axes=plt.subplots(1,2,figsize=(7.0,2.65))
    eta=np.linspace(.5,1.,501)
    for prior,K in SCENARIOS:
        mu=mean_square(prior,K)
        b=np.array([selected_b(float(e),mu) for e in eta])
        gain=100.*(1.-loss(b,mu)/loss(B_ROBUST,mu))
        color='#1764AB' if K==4 else '#BF4C23'
        ls='-' if prior=='uniform' else '--'
        label=('Uniform' if prior=='uniform' else r'Beta$(0.3,0.3)$')+f', $K={K}$'
        axes[0].plot(eta,gain,color=color,ls=ls,lw=1.4,label=label)
        threshold=robust_score(unconstrained_b(mu))/LAMBDA_STAR
        y=100.*(1.-loss(unconstrained_b(mu),mu)/loss(B_ROBUST,mu))
        axes[0].plot(threshold,y,'o',ms=3.1,color=color,
                     mfc=color if prior=='uniform' else 'white')
    axes[0].set_xlabel(r'Required separation retention $\eta$')
    axes[0].set_xlim(.5,1.)
    axes[0].set_xticks(np.arange(.5,1.01,.1))
    axes[0].grid(True,alpha=.2,lw=.6)
    axes[0].set_ylabel('Small-noise MSE reduction (%)')
    axes[0].set_ylim(bottom=0.)
    axes[0].legend(loc='lower left',frameon=True,framealpha=.97,edgecolor='none')
    angle=np.linspace(0.,2.*np.pi,1001)
    for b,color,ls,label in ((B_ROBUST,'#565D65',':',r'Worst-case optimum'),
                              (selected_b(.9,1./48.),'#1764AB','-',r'$90\%$ retention'),
                              (unconstrained_b(1./48.),'#BF4C23','--',r'Prior optimum, $K=16$')):
        axes[1].plot(np.cos(angle)/np.sqrt(b*(2.-b)),
                     (1.+np.sin(angle))/b,color=color,ls=ls,lw=1.25,label=label)
    s=np.linspace(-1.,1.,501)
    axes[1].plot(s,s*s,color='#111111',lw=1.7,label=r'Feature curve $(s,s^2)$')
    axes[1].scatter((-1.,0.,1.),(1.,0.,1.),s=10,c='#111111',zorder=5)
    axes[1].set_xlabel(r'First feature coordinate')
    axes[1].set_ylabel(r'Second feature coordinate')
    axes[1].set_xlim(-1.52,1.52)
    axes[1].set_ylim(-.05,1.82)
    axes[1].set_aspect('equal',adjustable='box')
    axes[1].grid(True,alpha=.2,lw=.6)
    axes[1].legend(loc='upper center',bbox_to_anchor=(.5,1.27),ncol=2,
                   fontsize=6.2,frameon=False,handlelength=2.,columnspacing=.8)
    fig.tight_layout(pad=.6,w_pad=1.4)
    for ext in ('pdf','png'):
        fig.savefig(ROOT/'figures'/f'pareto_frontier.{ext}',dpi=240,bbox_inches='tight')
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--trials',type=int,default=200000)
    args=parser.parse_args()
    assert args.trials>=2
    rows,scenarios,comparisons=experiment(args.trials)
    payload={'target':'variance','noise':'proper complex Gaussian; E|N|^2=N0',
             'decoder':'clamp inverted mean to [-1,1], evaluate q-m^2, clamp to [0,1]',
             'scope':'global frontier for the specified small-noise coefficient; finite-noise observations are empirical',
             'seed':BASE_SEED,'trials_per_scenario':args.trials,
             'lambda_star_normalized':float(LAMBDA_STAR),'b_robust':float(B_ROBUST),
             'normalizations':{'separation':'Lambda_sq/(K^2 P)',
                               'loss':'J=2 K^2 P lim_(N0->0) MSE/N0'},
             'versions':{'python':platform.python_version(),'numpy':np.__version__,
                         'scipy':scipy.__version__,'matplotlib':matplotlib.__version__},
             'scenarios':scenarios,'convex_comparisons':comparisons,'rows':rows}
    for folder in ('results','figures'):
        (ROOT/folder).mkdir(exist_ok=True)
    (ROOT/'results'/'pareto_frontier.json').write_text(json.dumps(payload,indent=2)+'\n')
    with (ROOT/'results'/'pareto_frontier.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    figure()
    print(json.dumps({'rows':len(rows),'convex_comparisons':len(comparisons),
                      'max_relative_solver_discrepancy':max(r['relative_loss_discrepancy'] for r in comparisons),
                      'scenarios':scenarios,
                      'retention_90_percent':[r for r in rows if r['required_retention']==.9]},indent=2))


if __name__=='__main__':
    main()
