# Finite-noise experiment design and interpretation

The experiment evaluates specified peak-constrained encoders and one common decoder architecture. It does not search over all Bayesian estimators, optimize finite-noise MSE, or claim that a worst-case objective implies Gaussian-MSE optimality.

## Fixed conditions

- Targets: variance `mean(s**2)-mean(s)**2` and fourth-order Jensen gap `mean(s**4)-mean(s)**4`. The latter is not the fourth central moment.
- Terminals: K = 4 and 16. Power: P = 1, enforced pointwise on every transmitter.
- Sources: independent Uniform[-1,1], or independent `2*Beta(0.3,0.3)-1`. The Beta prior concentrates probability toward both endpoints, not toward collective consensus.
- Noise: circular Gaussian N with independent real and imaginary components of variance N0/2, independent of sources. Thus E|N|²=N0.
- SNR: 10 log10(P/N0), evaluated at -10, -5, 0, 5, 10, 15, 20, 25, 30 dB. It is a per-terminal peak ratio; increasing K improves averaging at this fixed normalization.
- For each of four K/prior combinations, generate 200,000 independent source vectors and standardized noise draws. Reuse them across targets, SNR values, and all encoders. There are 800,000 independent source/noise pairs, 72 target/noise conditions, and 216 encoder-MSE estimates. The 14.4 million target/condition observations are not independent across SNR/target.
- Base seed: 2026091307; NumPy SeedSequence entropy is `[base_seed,K_index,prior_index]` and is recorded in each result row.

## Encoder comparisons

For E(s)=sqrt(P)[a*s+i*(b*s**p+c)], all designs use known-offset removal, feature-scale inversion, clipping of the recovered mean to [-1,1], readout `t_hat-m_hat**p`, and clipping to [0,1]. Coefficients change but the decoder architecture, data, and noise realization do not.

1. Baseline: (a,b,c)=(1,1,-1) for variance; (2/sqrt(5),2/sqrt(5),-1/sqrt(5)) for the quartic Jensen gap. These are the same specified baselines used in the analytic-score table. They are not asserted to be strong Bayesian baselines.
2. Worst-case: the proved peak/separation-optimal quadratic formula at M=2, or quartic formula at M=4.
3. Prior-aware: the same coefficient formulas with M_eff = p*sqrt(E[m**(2*p-2)]). This analytically minimizes the leading small-noise coefficient in the stated orthogonal feature-curve family. It uses the known source law, is not fitted to the sampled data, and makes no claim of finite-noise or unrestricted Bayesian optimality. Its worst-case score must still use the target's actual endpoint slope p, not M_eff.

The prior-mean estimator is a separate reference. It ignores the channel and uses the analytically known E[f]. It is not counted as an encoding scheme and does not satisfy noiseless exactness. Its purpose is to expose the limitations of the chosen exact decoder at low SNR.

## Analytic moments and small-noise coefficient

Write the symmetric source as s=2X-1 with X~Beta(alpha,alpha). Uniform corresponds to alpha=1; the endpoint prior uses alpha=0.3. Let mu_j=E[s**j]. Then

- mu2 = 1/(2 alpha+1)
- mu4 = 3/[(2 alpha+1)(2 alpha+3)]
- mu6 = 15/[(2 alpha+1)(2 alpha+3)(2 alpha+5)]
- E[m²] = mu2/K
- E[m⁶] = [K mu6 + 15 K(K-1)mu4*mu2 + 15 K(K-1)(K-2)mu2³]/K⁶
- E[variance] = mu2(1-1/K)
- E[quartic gap] = mu4(1-1/K³)-3(K-1)mu2²/K³

For both continuous priors, noiseless means and targets lie strictly inside the clipping intervals almost surely. The decoder gradient with respect to received real coordinates is `(-p*m**(p-1)/a,1/b)/(K*sqrt(P))`. The established global Lipschitz constant bounds the squared error divided by N0 by L²|Z|² for noise N=sqrt(N0)Z. Dominated convergence gives

MSE/N0 -> [1/b² + p² E[m**(2*p-2)]/a²]/(2K²P).

The limit concerns N0→0. A finite 20- or 30-dB observation is not treated as a proof of the limit, particularly for endpoint-concentrated priors where clipping can remain relevant at finite noise.

## Uncertainty and checks

The reported MSE standard error is the sample standard deviation of squared error divided by sqrt(n). For two encoders A and B, the MSE-difference standard error uses the paired per-trial squared-error differences. For the percentage reduction 100*(E[B]-E[A])/E[B], the code uses the paired delta-method influence function; the 95% interval is estimate ± 1.96 standard errors. These are pointwise asymptotic intervals, not simultaneous confidence bands. Source/noise reuse induces correlation across the plotted SNR points, and the analysis does not treat these points as independent replications.

Forty-eight checks compare the direct orthogonal formulas with the reusable matrix strip decoder: noiseless exactness and noisy decoder agreement for all 2 targets × 2 K × 2 priors × 3 encoders. These implementation checks do not independently establish the analytic encoder optimum.

## Outcomes (200,000 trials)

All 72 tested cells favor the separation-optimal curve over the specified baseline, with relative MSE reductions from 6.120% to 22.917%. Every tested cell also favors the prior-aware curve over the separation-optimal curve, with reductions from 5.688% to 72.008%. These observations demonstrate a substantial distinction between worst-case separation and prior-dependent average MSE. They do not establish either ordering beyond the listed conditions.

The known prior mean beats the separation-optimal curve and implemented decoder in 15 of 72 cells, all in the lower-SNR portion of the grid. For variance, uniform sources, K=4, and -10 dB, the MSEs are approximately 0.02294 (prior mean), 0.1032 (worst-case design), 0.1171 (baseline), and 0.08216 (prior-aware curve). A prior-aware decoder or shrinkage estimator could improve low-SNR performance; this experiment does not implement or optimize such a decoder.

The main figure reports MSE reduction against the same specified baseline for the worst-case and prior-aware designs; shared colors identify K and line styles identify the design criterion. It includes every SNR point and displays paired 95% intervals. The table reports absolute MSEs at a fixed representative SNR of 20 dB, not an SNR selected for the largest gains.

## Reproduction

From the paper directory:

`python3 code/finite_noise.py`

The default 200,000-trial run regenerates `results/finite_noise.json`, `results/finite_noise.csv`, `figures/finite_noise.pdf`, and `figures/finite_noise.png`. Dependencies are NumPy, SciPy, and Matplotlib; their actual versions are retained in the JSON record. The script accepts `--trials` for exploratory runs; the delivered paper uses the default count.
