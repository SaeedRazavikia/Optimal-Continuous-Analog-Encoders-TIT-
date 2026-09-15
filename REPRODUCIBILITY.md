# Reproducibility

Use Python 3.12 with the packages listed in `requirements.txt`. The recorded runs use NumPy 2.3.5, SciPy 1.17.0, and Matplotlib 3.10.8. Run these commands from the project directory:

```bash
python code/verify_extension.py
python code/verify_decoders.py
python -S code/certified_synthesis.py --verify-only
python code/finite_noise.py --trials 200000
python code/pareto_frontier.py --trials 200000
python code/independent_reproduce.py
python code/export_tikz_analytic.py
python code/export_tikz_empirical.py
latexmk -pdf manuscript.tex
```

`verify_extension.py` reuses the supplied structural checker and passes 135 checks. `verify_decoders.py` passes 98 implementation checks over 1,728 primary observations. Neither checker proves the universal mathematical claims. Their seeds and measured residuals are retained in `results/`.

`certified_synthesis.py --verify-only` verifies the stored rational primal and dual witnesses without invoking the numerical optimizer. Its interval arithmetic uses Python exact fractions and a degree-40 Taylor enclosure for exp on [-1,1]. It checks positive definiteness, endpoint score inequalities, finite dual support, normalization, and the continuous peak bound. The stored rational bounds, rather than displayed decimal coefficients, define the certificate. Run `python code/certified_synthesis.py` to regenerate candidates, rational certificates, and the figure. Candidate generation uses SLSQP; its status is not a mathematical certificate.

`finite_noise.py` evaluates variance and the quartic Jensen gap at K=4 and K=16 for two independent-source priors and nine noise levels. It uses 200,000 source/noise draws per source/K cell, common random numbers across compared encoders, and the same projected/clipped decoder architecture. The prior-tuned comparator uses analytic source moments. CSV and JSON include all cells, paired uncertainty, and the fixed prior-mean reference. Intervals are nominal pointwise Monte Carlo confidence intervals; the study makes no simultaneous coverage or Bayesian-optimality claim. Detailed settings and the high-SNR calculation appear in `notes/experiment_design.md`.

The general small-noise result is now Proposition `prop:general-small-noise`; the orthogonal polynomial specialization retains equation `eq:small-noise-mse`. For a fixed joint source law independent of proper complex Gaussian noise, the specified decoder has coefficient `tr(Q_pi G^-1)/(2 K^2)`. The assumptions include an almost-sure interior mean and a positive-definite prior-gradient matrix; any output clipping must also be inactive at noiseless observations almost surely. The source coordinates need not be independent for the general result. The theorem concerns a fixed encoder and the limit as noise vanishes; it does not interchange that limit with optimization over noise-dependent encoders or arbitrary estimators.

`pareto_frontier.py` reproduces the explicit variance tradeoff for K=4 and K=16 under the same uniform and endpoint-Beta priors. It generates `results/pareto_frontier.json`, `results/pareto_frontier.csv`, and the corresponding PDF/PNG figure. The recorded run uses 200,000 independent source/noise draws per scenario, shared across eight required separation-retention levels, giving 32 empirical rows at 20 dB. It also compares 12 analytic solutions with a separate three-variable convex calculation. These floating-point comparisons have maximum relative objective discrepancy about `1.04e-9`; two SLSQP runs report linesearch termination, with their flags and constraint residuals preserved. They are consistency checks, not exact numerical certificates. `notes/pareto_reproduction.md` gives the seed, normalization, checks, complete settings, and interpretation. The exact general frontier is proved using a five-variable inverse-metric formulation; the original separation problem also has an equivalent six-variable inverse formulation. Neither variable count removes the continuum of peak constraints.

`independent_reproduce.py` writes `results/independent_reproduction.json`. It does not import the original certificate, finite-noise, or verification scripts. Its second implementation uses degree-48 positive Taylor-tail bounds, reciprocal negative-input enclosures, exact rational interval arithmetic, and every principal minor. It reproduces the exponential bounds and the gap of `0.00598910955%`, verifies the exact Schur reduction, and checks 16 coefficient/moment combinations, 256 decoder comparisons, and two new frontier points. The full run imports the reusable NumPy-based decoder solely for comparison with a separate received-plane projection calculation. To run only the certificate without site packages, use:

```bash
python -S code/independent_reproduce.py --certificate-only --output results/independent_certificate_only.json
```

Both full and certificate-only second-implementation commands were run successfully using absolute script paths from outside the paper directory. This is a second implementation in the same environment, not independent human or different-machine reproduction. The new analytic checks recover moments by exact truncated moment-generating-function convolution and coefficients by 75-digit bisection. They do not rerun the full finite-noise experiment. `notes/independent_reproduction.md` records the scope and evidence.

Finite-SNR results must not be presented as automatic agreement with the small-noise limit. In the recorded K=4 endpoint-Beta cells, `MSE/N0` at 30 dB remains 3.49–7.19% below the limiting coefficient, approximately 9.6–10.5 reported Monte Carlo standard errors away. The implemented clipping remains relevant at finite noise; the separate script also calculates exact moments for the unclipped polynomial decoder as context. These differences do not invalidate the limit theorem, but they prevent claiming that the 30-dB cells are already asymptotic.

The implementation-error bound and the arXiv version’s qualitative approximate-rigidity proposition are analytic results. Their conclusions rely on the hypotheses in the manuscript: peak-feasible encoder approximation and bounded residual gains for the former; a fixed encoder continuity modulus and decoder Lipschitz budget for the latter. No simulation establishes a quantitative approximate-rigidity rate, and the paper does not claim one.

The quadratic and quartic global optima have analytic interval peak identities and convex optimality certificates in the manuscript. Generic polynomial sampling is not treated as proof. The exponential example has a separate exact-arithmetic primal/dual certificate.

Compile the included IEEEtran document with `latexmk -pdf manuscript.tex`. The build runs pdfLaTeX and BibTeX for `bibliography.bib`; the included class and bibliography style preserve the manuscript format. Required TeX packages include amsmath, amssymb, amsthm, mathrsfs, mathtools, booktabs, array, microtype, graphicx, placeins, balance, hyperref, TikZ/PGF, PGFPlots (compatibility level 1.18), and adjustbox. The output is the 50-page submission version, `manuscript.pdf`. Build `manuscript_arxiv.tex` with the same command to retain the ancillary criterion, approximate-rigidity, and Lean-verification appendices in `manuscript_arxiv.pdf`. Both builds use the same typography and main-text sources.

The final PDF is rendered and inspected after compilation. `REVISION_NOTES.md` records the revised manuscript and verification scope. `SHA256SUMS.txt` covers delivered source files. Re-running experiments or building the PDF changes generated timestamps/hashes as expected.

## Native LaTeX figure revision

All six manuscript figures now compile directly from `figures/tikz/` with TikZ/PGFPlots. The committed tables in `figures/data/` suffice for compilation. The two `export_tikz_*.py` scripts regenerate those tables from archived results and analytic formulas, preserving all source values and confidence intervals. This presentation revision did not generate new Monte Carlo samples. The numerical scripts may retain historical Matplotlib exports, but the manuscript does not use them. See `figures/README.md` for isolated figure compilation.

The Lean artifact is documented in `formalization/README.md`; pinned dependencies, proof sources, a complete manuscript coverage inventory, and the verification report are included in `formalization/`. `formalization/verification/report.json` records the audited declarations and exact source hashes. `formalization/COVERAGE.md` and `formalization/EXTENSION_SCOPE.md` identify the verified statements and the remaining proof obligations. Compilation and an axiom audit apply to those declarations; they do not establish unformalized manuscript results.

## Numerical source provenance

The numerical scripts and archived experiment records in this package are unchanged from repository commit `7a513ed38147a73f109f9b184dafba59c17ee89b`. The manuscript and Lean formalization have subsequent revisions. Reproduction instructions were updated for the current BibTeX build and artifact structure. The exact numerical source hashes are recorded in `NUMERICAL_SOURCE.json`.
