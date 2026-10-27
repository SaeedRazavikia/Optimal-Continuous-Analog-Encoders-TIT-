# Variance robustness–small-noise-MSE frontier

Run from the paper directory:

```sh
python code/pareto_frontier.py --trials 200000
```

The script writes `results/pareto_frontier.json`, `results/pareto_frontier.csv`,
and `figures/pareto_frontier.pdf`/`.png`. It uses NumPy, SciPy, and Matplotlib;
the output JSON records their actual versions. Its source/noise seed is
2026091329, combined with the scenario index through NumPy `SeedSequence`.

## Scope and normalizations

The target is variance, the sources are independent and identically distributed,
and the common encoder has pointwise peak power P=1. We evaluate K=4 and K=16
under the uniform prior on [-1,1] and the endpoint-concentrated prior
S=2X-1, X distributed as Beta(0.3,0.3). Both distributions are symmetric and
have no atoms. Write mu=E[m²], which equals 1/(3K) and 1/(1.6K), respectively.

The encoder family is

$$E_b(s)=\sqrt{P}\,[\sqrt{b(2-b)}\,s+i(bs^2-1)],\qquad 1\le b<2.$$

The normalized separation and small-noise loss are

$$\ell(b)=\frac{\Lambda_{\rm sq}}{K^2P}
=\frac{b^2(2-b)}{3b+2},\qquad
J_\mu(b)=\frac{4\mu}{b(2-b)}+\frac{1}{b^2}.$$

For the implemented clipped strip/readout decoder, the limiting Gaussian MSE
coefficient is J_mu/(2K²P). Proper complex Gaussian noise satisfies
E|N|²=N0. The robustness constraint is ell(b) >= eta ell_star, where
ell_star=4/(9+6 sqrt(3)). Thus eta retains a fraction of **squared separation**;
the worst-case disturbance amplification increases by at most 1/sqrt(eta).

The code does not claim that this family/decoder minimizes finite-noise Bayesian
MSE. Global optimality of the stated asymptotic frontier comes from the paper's
structural, symmetry, peak-boundary, and scalar monotonicity arguments.

## Evaluation method and numerical comparison

The prior-only minimizer is

$$b_0=\frac{2}{1+2\sqrt{\mu}/(\sqrt{\mu+2}+\sqrt{\mu})}.$$

We select the smaller of b_0 and the root on [2/sqrt(3),2) of
ell(b)=eta ell_star. A bracketed scalar solver evaluates this monotone branch;
eta=0 and eta=1 receive their exact limiting/special-case treatment. The
constraint remains inactive until eta_c=ell(b_0)/ell_star.

An independent numerical comparison solves the convex problem in three
variables (A,b,c), without substituting A=b(2-b) or c=-1:

$$\min\ \frac{4\mu}{A}+\frac{1}{b^2},\qquad
c^2\le1,\quad A+(b+c)^2\le1,\quad
\frac4A+\frac1{b^2}\le\frac1{\eta\ell_\star}.$$

Here A,b are positive. The two endpoint peak constraints imply the full
continuum peak constraint because At+(bt+c)² is convex in t=s² on [0,1].
These are not grid approximations. We compare eta=0.5,0.9,0.99 in all four
scenarios: 12 solves total. The maximum relative objective discrepancy is
1.040e-9; the worst constraint residual is -2.408e-10. Ten SLSQP runs report
successful termination. The two K=16, eta=0.99 runs report a linesearch
termination while meeting the explicitly checked residual tolerances. The JSON
preserves these flags and messages. These floating-point comparisons are
consistency checks, not exact numerical certificates.

A separate internal reproduction implementation also evaluated the two uniform
eta=0.9 points using 75-digit Decimal arithmetic and direct boundary-polynomial
bisection, without importing this script. It recovered the reported b, a,
normalized separation, and both source-dependent objectives and gains. That
check is recorded in the independent reproduction report; it is not an external
researcher review.

## Main numerical findings

| Prior | K | Unconstrained b_0 | Inactive-constraint threshold eta_c | Maximum asymptotic MSE reduction (%) |
|---|---:|---:|---:|---:|
| Uniform | 4 | 1.500000 | 0.839090 | 18.5631 |
| Uniform | 16 | 1.688688 | 0.609097 | 39.0469 |
| Endpoint Beta | 4 | 1.404304 | 0.916687 | 9.7903 |
| Endpoint Beta | 16 | 1.608800 | 0.719085 | 30.2666 |

All gains use the worst-case-optimal encoder b=2/sqrt(3) as their reference.

| Prior | K | Required eta | Actual separation retention | Asymptotic MSE reduction (%) | Measured reduction at 20 dB, paired 95% interval (%) |
|---|---:|---:|---:|---:|---:|
| Uniform | 4 | 0.90 | 0.900000 | 17.6806 | 17.9890 [17.8385,18.1395] |
| Uniform | 16 | 0.90 | 0.900000 | 29.0731 | 29.1026 [29.0200,29.1852] |
| Endpoint Beta | 4 | 0.90 | 0.916687 | 9.7903 | 10.8525 [10.7027,11.0023] |
| Endpoint Beta | 16 | 0.90 | 0.900000 | 25.0879 | 25.1201 [25.0043,25.2358] |

For uniform sources, retaining 90% of squared separation increases the sharp
disturbance amplification by 5.41% and reduces the limiting MSE coefficient by
17.68% (K=4) or 29.07% (K=16). The shared active-constraint encoder has
b=1.427841419869 and a=0.903853815307.

The finite-noise study uses 200,000 independent source/noise draws per scenario,
with the same draws shared by every encoder in that scenario. It evaluates the
selected retentions 0,0.25,0.5,0.75,0.9,0.95,0.99,1, producing 32 rows. The
20 dB SNR is P/N0=100. Paired confidence intervals use the delta-method
influence function of the relative MSE reduction. These are pointwise Monte
Carlo intervals, without adjustment for simultaneous coverage. Noiseless mean
and second moment are perturbed by the inverted Gaussian observation, after
which the mean is clipped to [-1,1] and the variance estimate to [0,1]. A
finite-SNR gain need not equal the asymptotic gain, especially for the
endpoint-concentrated prior and small K.

## Figure interpretation

The left panel displays the theoretical reduction of the small-noise MSE
coefficient against the required separation retention. Markers identify the
inactive/active constraint transition. The plotted range is eta in [0.5,1];
the output table also includes lower retentions, which lie on the plateaus.

The right panel shows the feature curve (s,s²) and three containing ellipses
for the worst-case optimum, 90% retention, and the uniform K=16 prior optimum.
Their centers are (0,1/b), with semiaxes 1/sqrt(b(2-b)) and 1/b. Each ellipse
passes through the feature points (-1,1), (0,0), (1,1). Prior adaptation expands
the first-feature semiaxis and contracts the second-feature semiaxis. The
displayed geometry represents the power constraint in feature coordinates;
these ellipses are not receiver-noise confidence regions.

Both PDF and PNG were generated from the same plotting routine. The PNG was
visually inspected for clipping, labels, and legend interference.
