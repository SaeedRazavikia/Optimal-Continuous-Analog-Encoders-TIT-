# Independent implementation review

This review uses a second implementation in the same computational environment. It is not external human review, different-machine reproduction, or evidence of historical originality. The reviewer used the manuscript and recorded data, and inspected the experiment definitions. The new script does not import `certified_synthesis.py`, `finite_noise.py`, `verify_extension.py`, or `verify_decoders.py`.

The executable is `code/independent_reproduce.py`; its recorded output is `results/independent_reproduction.json`. Existing certificate, experiment, and verification results were not overwritten. The new script records its own SHA-256 digest and the input certificate digest.

## Exact exponential certificate

The original verifier uses degree-40 Taylor intervals with a uniform Lagrange remainder. The second verifier instead evaluates the positive degree-48 Taylor series. For an input `0 <= x <= 1`, it bounds the omitted tail by its first term divided by `1-x/50`; subsequent term ratios are at most `x/50`. It obtains negative-input enclosures by reciprocating the positive-input interval. All endpoints and operations use exact rational arithmetic.

The second implementation verifies every nonempty principal minor of the primal matrix, both score-constraint matrices, both dual multiplier matrices, and the dual residual. All are strictly positive. It also verifies every stored peak weight is nonnegative and certifies the dual normalization exceeds one. It computes the rational Schur complement independently: reducing the constant Gram entry preserves the feature block, reduces the peak, and gives an exactly zero rank-three determinant with a positive definite feature block.

For `q(s) = [1,s,exp(s)] H [1,s,exp(s)]^T`, direct differentiation gives

`q''(s) = 2 H11 + 2 H02 exp(s) + 2 H12 (s+2) exp(s) + 4 H22 exp(2s)`.

The separately evaluated derivative bound is less than `116.707425`, hence less than the stated value `117`. A fresh exact evaluation of all 1,001 grid points bounds the grid maximum by approximately `1.000000093893504`, below the recorded outward bound `1.000000093894`. The interpolation and scaling calculation recovers the exact stated lower bound. The separately reconstructed dual residual recovers the exact upper bound:

| Quantity | Independently reproduced value |
|---|---:|
| Lower bound | `209834839284 / 500029296947` |
| Upper bound | `104917556109394155472367 / 250000000000000000000000` |
| Relative gap `(U-L)/U`, percent | `0.005989109550760389` |
| Dual normalization lower bound, display | `1.0000000000011129` |
| Exact rank-reduced determinant | `0` |

The displayed decimals are not the certificate. Passing exact inequalities and the stored rational witnesses establish the enclosure. This check certifies the optimization witnesses, not the classification theorem, the entire research manuscript, or the novelty of its results.

## Analytic normalization and moment checks

The second implementation computes symmetric-source moments recursively from the Beta integral and raises the truncated moment-generating polynomial to its Kth power by exact rational convolution. This approach differs from the closed-form second- and sixth-moment expansions used in the original experiment script. Multiplying the nth coefficient by `n!/K^n` recovers the mean's nth moment.

It obtains the quadratic coefficients by 75-digit bisection of their stationarity equation, rather than substituting the original radical expression. It obtains the quartic coefficients by separately implemented 75-digit bisection of the defining root. Coefficientwise polynomial comparisons verify the continuum peak identities, rather than testing only sampled source values. Sixteen combinations of target, prior, terminal count, and robust/prior-tuned design reproduce the recorded coefficients, worst-case scores, source moments, target means, and small-noise MSE constants.

The comparison with the recorded 20- and 30-dB results is descriptive. A finite-SNR MSE need not equal its small-noise limit. Across the selected cells, the differences between `MSE/N0` and the analytic limit range from -12.61% to +0.151% at 20 dB and from -7.19% to +0.151% at 30 dB. For K=4 and the endpoint-concentrated Beta prior, the four design/target combinations remain 3.49–7.19% below their limits at 30 dB, corresponding to approximately 9.6–10.5 reported Monte Carlo standard errors. Therefore these cells must not be described as agreement with the limit within sampling uncertainty, or as already asymptotic.

For context, the new script also evaluates the exact finite-Gaussian-noise MSE polynomial for the **unclipped** readout from source and noise moments. This quantity has positive finite-polynomial corrections to the small-noise limit. The original experiment uses mean and output clipping, so it evaluates a different decoder. The discrepancy is compatible with finite-noise clipping and does not invalidate the dominated-convergence theorem. The independent check does not assert a numerical convergence rate.

## Decoder implementation

For a nondiagonal feature matrix, the second implementation projects directly onto the two received-plane halfspaces describing the mean strip. It then inverts the matrix and evaluates the target. This construction differs from the implemented feature-coordinate correction formula. Comparison against the reusable decoder covers 128 independently generated observations and 256 coordinate/readout comparisons, with maximum absolute discrepancy `5.33e-15`. This is an implementation check, not a proof of universal optimality.

## New Pareto frontier: bounded spot review

The new script independently solves the robustness-boundary cubic and checks two active-constraint points without importing `pareto_frontier.py`. At 90% retention of the optimal worst-case separation and uniform sources, both K=4 and K=16 use

`a = 0.9038538153068596`, `b = 1.4278414198686626`, `c = -1`.

The full peak identity is `|E(s)|^2 = 1-b^2 s^2(1-s^2) <= 1`. The normalized separation is `0.18564064605510183`, equal to `0.9` times the optimum. The source-dependent normalized small-noise losses are `0.8985220180770999` and `0.5925063820858933`, respectively. Relative to the fully robust design, these correspond to asymptotic reductions of `17.6805506172%` and `29.0731400923%`. All values agree with the newly stored frontier data. The claim concerns the small-noise coefficient and the stated decoder; it is not a finite-noise or unrestricted estimator-optimality assertion.

## Reproduction commands and remaining limits

Run the complete second implementation from the paper directory:

```bash
python code/independent_reproduce.py
```

For the exact certificate alone, without site packages:

```bash
python -S code/independent_reproduce.py --certificate-only --output results/independent_certificate_only.json
```

Both routes were executed successfully using absolute script paths from a working directory outside the paper directory. The certificate-only route uses Python's standard library. The full route additionally imports the existing NumPy-based decoder for comparison and thus uses the documented environment. The original documentation's commands target scripts present in the package, and their resolved output paths are based on the scripts' locations. This review did not rerun all original Monte Carlo cells or rebuild the manuscript; those are separate generation steps. No claim of independent human verification or different-machine reproduction has been made.

Before submission, an external reader should reproduce the proof independently and another researcher should run the package in a separately prepared environment. Those steps remain outstanding.
