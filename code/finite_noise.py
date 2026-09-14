#!/usr/bin/env python3
"""Paired finite-Gaussian-noise comparisons; run from any working directory.

This is empirical evaluation of specified encoders/decoders, not a Gaussian-MSE
optimality test. SNR is the per-terminal peak ratio P/N0, where E|N|^2=N0.
"""
from pathlib import Path
import argparse
import csv
import json
import platform
import sys
import numpy as np
import scipy
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from decoders import quadratic, quartic, decode_gap

ROOT = Path(__file__).resolve().parents[1]
BASE_SEED = 2026091307
SNR_DB = np.arange(-10., 31., 5.)


def source_moments(prior):
    alpha = 1.0 if prior == 'uniform' else 0.3
    return 1. / (2.*alpha+1.), 3. / ((2.*alpha+1.)*(2.*alpha+3.))


def target_mean(prior, K, p):
    mu2, mu4 = source_moments(prior)
    if p == 2:
        return mu2*(1.-1./K)
    return mu4*(1.-1./K**3)-3.*(K-1)*mu2**2/K**3


def mean_power(prior, K, p):
    mu2, mu4 = source_moments(prior)
    if p == 2:
        return mu2/K
    alpha = 1.0 if prior == 'uniform' else .3
    mu6 = 15./((2.*alpha+1.)*(2.*alpha+3.)*(2.*alpha+5.))
    return (K*mu6+15.*K*(K-1)*mu4*mu2+15.*K*(K-1)*(K-2)*mu2**3)/K**6


def curves(p, prior, K):
    effective_M = p*np.sqrt(mean_power(prior,K,p))
    if p == 2:
        a, b, c = quadratic(2.)
        return {'optimal': (a,b,c), 'baseline': (1.,1.,-1.),
                'prior_tuned': quadratic(effective_M)}
    _, a, b, c = quartic(4.)
    r = 2./np.sqrt(5.)
    return {'optimal': (a,b,c), 'baseline': (r,r,-r/2.),
            'prior_tuned': quartic(effective_M)[1:]}


def paired_gain(reference, candidate):
    mr=np.mean(reference)
    diff=reference-candidate
    delta,se_delta=summary_stats(diff)
    gain=100.*delta/mr
    influence=100.*((diff-delta)/mr-delta*(reference-mr)/mr**2)
    se_gain=float(np.std(influence,ddof=1)/np.sqrt(len(reference)))
    return delta,se_delta,gain,se_gain


def decode_moments(m, t, z, K, p, coeffs, N0, P=1.):
    """Equivalent orthogonal strip/readout decoder with known translation.

    y_R=K*sqrt(P)*a*m+n_R; y_I=K*sqrt(P)*(b*t+c)+n_I.
    Subtracting the known offset removes c before moment inversion.
    """
    a,b,_ = coeffs
    sigma = np.sqrt(N0/(2.*P))/K
    mh = np.clip(m+sigma*z[:,0]/a,-1.,1.)
    th = t+sigma*z[:,1]/b
    return np.clip(th-mh**p,0.,1.)


def summary_stats(error):
    mse = float(np.mean(error))
    return mse, float(np.std(error,ddof=1)/np.sqrt(len(error)))


def run(n):
    rows=[]
    checks=[]
    for ki,K in enumerate((4,16)):
        for pi,prior in enumerate(('uniform','endpoint_beta')):
            seed = np.random.SeedSequence([BASE_SEED,ki,pi])
            rng=np.random.default_rng(seed)
            s = rng.uniform(-1.,1.,size=(n,K)) if prior=='uniform' else 2.*rng.beta(.3,.3,size=(n,K))-1.
            z=rng.standard_normal((n,2))
            m=s.mean(axis=1)
            for p in (2,4):
                t=(s**p).mean(axis=1)
                target=t-m**p
                mu=target_mean(prior,K,p)
                const_mse,const_se=summary_stats((target-mu)**2)
                coeffs=curves(p,prior,K)
                for name,(a,b,c) in coeffs.items():
                    y=K*np.column_stack((a*m[:200],b*t[:200]+c))
                    reconstructed=decode_gap(y,np.array([0.,c]),np.diag([a,b]),K,lambda x:x**p,(0.,1.))
                    noiseless=float(np.max(np.abs(reconstructed-target[:200])))
                    checks.append({'p':p,'K':K,'prior':prior,'encoder':name,'check':'noiseless','max_abs_error':noiseless})
                    assert noiseless < 2e-14
                for snr in SNR_DB:
                    N0=10.**(-snr/10.)
                    error={name:(decode_moments(m,t,z,K,p,coef,N0)-target)**2 for name,coef in coeffs.items()}
                    mo,se_o=summary_stats(error['optimal'])
                    mb,se_b=summary_stats(error['baseline'])
                    mt,se_t=summary_stats(error['prior_tuned'])
                    delta,se_delta,gain,se_gain=paired_gain(error['baseline'],error['optimal'])
                    _,_,gain_t,se_gain_t=paired_gain(error['baseline'],error['prior_tuned'])
                    _,_,tuned_vs_optimal,se_tuned_vs_optimal=paired_gain(error['optimal'],error['prior_tuned'])
                    L2_o=(p*p/coeffs['optimal'][0]**2+1./coeffs['optimal'][1]**2)/(K*K)
                    rows.append({'target':'variance' if p==2 else 'quartic_gap','p':p,'K':K,'prior':prior,
                                 'snr_db':float(snr),'P':1.,'N0':N0,'trials':n,
                                 'mse_optimal':mo,'se_optimal':se_o,'mse_baseline':mb,'se_baseline':se_b,
                                 'mse_baseline_minus_optimal':delta,'paired_se_difference':se_delta,
                                 'gain_percent':gain,'paired_se_gain_percent':se_gain,
                                 'gain_ci95_lo':gain-1.96*se_gain,'gain_ci95_hi':gain+1.96*se_gain,
                                 'mse_prior_tuned':mt,'se_prior_tuned':se_t,
                                 'tuned_gain_percent_vs_baseline':gain_t,'paired_se_tuned_gain_percent':se_gain_t,
                                 'tuned_gain_percent_vs_optimal':tuned_vs_optimal,'paired_se_tuned_vs_optimal':se_tuned_vs_optimal,
                                 'effective_M_prior_tuned':p*np.sqrt(mean_power(prior,K,p)),
                                 'high_snr_mse_over_N0_optimal':(1./coeffs['optimal'][1]**2+p*p*mean_power(prior,K,p)/coeffs['optimal'][0]**2)/(2*K*K),
                                 'high_snr_mse_over_N0_prior_tuned':(1./coeffs['prior_tuned'][1]**2+p*p*mean_power(prior,K,p)/coeffs['prior_tuned'][0]**2)/(2*K*K),
                                 'prior_mean':mu,'mse_prior_mean':const_mse,'se_prior_mean':const_se,
                                 'uniform_mse_bound_optimal':L2_o*N0,
                                 'sample_seed_entropy':f'{BASE_SEED},{ki},{pi}'})
                    # Check the implementation against the reusable decoder at representative SNR.
                    if snr==0.:
                        for name,(a,b,c) in coeffs.items():
                            y=K*np.column_stack((a*m[:200],b*t[:200]+c))+np.sqrt(N0/2.)*z[:200]
                            reference=decode_gap(y,np.array([0.,c]),np.diag([a,b]),K,lambda x:x**p,(0.,1.))
                            direct=decode_moments(m[:200],t[:200],z[:200],K,p,(a,b,c),N0)
                            discrepancy=float(np.max(np.abs(reference-direct)))
                            checks.append({'p':p,'K':K,'prior':prior,'encoder':name,'check':'decoder_agreement','max_abs_error':discrepancy})
                            assert discrepancy<2e-14
    return rows,checks


def figures(rows):
    plt.rcParams.update({'font.size':8,'axes.labelsize':8,'axes.titlesize':9,
                         'legend.fontsize':7,'xtick.labelsize':7,'ytick.labelsize':7,
                         'font.family':'serif','savefig.bbox':'tight','pdf.fonttype':42})
    fig,axes=plt.subplots(2,2,figsize=(7.0,4.25),sharex=True)
    for i,target in enumerate(('variance','quartic_gap')):
        for j,prior in enumerate(('uniform','endpoint_beta')):
            ax=axes[i,j]
            for K,color,marker in ((4,'#1764AB','o'),(16,'#BF4C23','s')):
                group=[r for r in rows if r['target']==target and r['prior']==prior and r['K']==K]
                xx=np.array([r['snr_db'] for r in group])
                yy=np.array([r['gain_percent'] for r in group])
                ee=1.96*np.array([r['paired_se_gain_percent'] for r in group])
                ax.errorbar(xx,yy,yerr=ee,color=color,marker=marker,ms=3.0,lw=1.15,capsize=2,label=f'Worst-case, $K={K}$')
                yy_t=np.array([r['tuned_gain_percent_vs_baseline'] for r in group])
                ee_t=1.96*np.array([r['paired_se_tuned_gain_percent'] for r in group])
                ax.errorbar(xx,yy_t,yerr=ee_t,color=color,marker=marker,mfc='white',ms=3.0,lw=1.05,ls='--',capsize=2,label=f'Prior-tuned, $K={K}$')
            ax.axhline(0.,color='0.55',lw=.7)
            ax.grid(True,alpha=.18)
            ax.set_title(('Variance' if i==0 else 'Quartic Jensen gap')+'; '+('uniform' if j==0 else 'endpoint Beta'))
            ax.set_xticks(np.arange(-10,31,10))
            if j==0: ax.set_ylabel('MSE reduction (%)')
            if i==1: ax.set_xlabel('Per-terminal peak SNR $P/N_0$ (dB)')
    handles,labels=axes[0,0].get_legend_handles_labels()
    fig.legend(handles,labels,loc='upper center',ncol=4,fontsize=6.8,
               bbox_to_anchor=(.5,1.025),frameon=False,columnspacing=1.0,handlelength=2.2)
    fig.tight_layout(pad=.7,w_pad=1.1,h_pad=.8,rect=(0,0,1,.97))
    for ext in ('pdf','png'):
        fig.savefig(ROOT/'figures'/f'finite_noise.{ext}',dpi=240)
    plt.close(fig)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--trials',type=int,default=200000)
    args=ap.parse_args()
    if args.trials < 1000: raise ValueError('At least 1000 trials required')
    rows,checks=run(args.trials)
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'figures').mkdir(exist_ok=True)
    with (ROOT/'results'/'finite_noise.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    payload={'schema_version':1,'description':'Paired finite-noise evaluation of worst-case peak-optimal, prior-aware high-SNR-tuned, and baseline curves with identical decoder architecture.',
             'base_seed':BASE_SEED,'trials_per_source_K_cell':args.trials,'source_K_cells':4,
             'target_noise_cells':len(rows),'independent_source_vectors':4*args.trials,
             'reuse':'Within each source/K cell, sources and standardized noise are reused for both targets, every SNR, and all encoders; confidence intervals are pointwise.',
             'noise':'N_R,N_I independent Normal(0,N0/2); E|N|^2=N0; SNR=P/N0; P=1.',
             'priors':{'uniform':'iid Uniform[-1,1]','endpoint_beta':'iid 2*Beta(0.3,0.3)-1'},
             'decoder':'Known-offset removal; invert diagonal feature scales; clip estimated mean to [-1,1]; t_hat-m_hat^p; clip target to [0,1].',
             'baseline_curves':{'variance':[1.,1.,-1.],'quartic_gap':[2./np.sqrt(5.),2./np.sqrt(5.),-1./np.sqrt(5.)]},
             'coefficients_and_scores':[
                 {'p':p,'prior':prior,'K':K,'design':name,
                  'coefficients_a_b_c':[float(a),float(b),float(c)],
                  'normalized_worst_case_squared_score':float(1./(p*p/a**2+1./b**2)),
                  'mean_power_2p_minus_2':mean_power(prior,K,p)}
                 for p in (2,4) for prior in ('uniform','endpoint_beta') for K in (4,16)
                 for name,(a,b,c) in curves(p,prior,K).items()],
             'prior_tuned':'Use the same quadratic/quartic coefficient formulas with M=p*sqrt(E[m^(2p-2)]), evaluated from analytic iid prior moments. This minimizes the high-SNR leading coefficient within the stated orthogonal curve family; it does not claim finite-noise or Bayesian optimality.',
             'intervals':'1.96 times paired asymptotic standard errors; ratio intervals use the paired delta method; no multiple-comparison adjustment.',
             'versions':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'matplotlib':matplotlib.__version__},
             'checks':checks,'rows':rows}
    (ROOT/'results'/'finite_noise.json').write_text(json.dumps(payload,indent=2)+'\n')
    figures(rows)
    print(json.dumps({'cells':len(rows),'trials_per_cell':args.trials,'checks':len(checks),'gain_range_percent':[min(r['gain_percent'] for r in rows),max(r['gain_percent'] for r in rows)],'negative_gain_cells':int(sum(r['gain_percent']<0 for r in rows)),'output':str(ROOT/'results'/'finite_noise.json')},indent=2))

if __name__=='__main__':
    main()
