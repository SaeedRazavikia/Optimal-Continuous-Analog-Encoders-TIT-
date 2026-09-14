# External review packet (retained from the preceding revision)

Status: prepared; no researcher has been contacted through this workflow. External specialist assessment and different-machine reproduction remain outstanding.

## Review brief

**Subject:** Review request: continuous computation rigidity and peak-constrained encoder design

Dear Colleague,

We would appreciate a focused mathematical and originality review of the attached manuscript and source package. We study a shared continuous planar encoder for one-use additive computation of a fixed moment-and-mean target. Our argument derives necessary feature geometry from scalar exactness, obtains the exact worst-case separation, and gives global peak-constrained synthesis. We also derive a robustness-constrained small-noise frontier and an explicit quadratic specialization.

We seek an adversarial assessment of the theorem dependencies and their significance relative to restricted additive functional equations and established convex design methods. We do not claim a new general affine-uniqueness principle, matrix optimization method, or unrestricted finite-noise Bayesian optimum. A report identifying an implication from prior work, a proof gap, or an overstatement would be especially useful.

## Priority questions

1. Does an existing local additive theorem, combined with invariance of domain, imply our original one-way-collision lemma? Is the scalar-exactness reduction substantial or a short supporting application? Please distinguish originality from correctness.
2. Do the common chart, convolution support, and fixed unequal-slope anchors justify the global conclusion for an interior-C1 feature, including affine subintervals?
3. Does score sharpness use attainable perturbations correctly near consensus endpoints without assuming a uniform neighborhood radius? Are rigidity and score assumptions properly separated?
4. Do inverse-metric synthesis, attainment, Gram uniqueness, convexity in the separation floor, and the plateau/active-branch argument hold at both endpoints?
5. Does quadratic symmetry and domination preserve feasibility while improving both objectives, so the explicit frontier covers the full continuous exact-encoder class?
6. Do the almost-sure interior conditions and global Lipschitz domination justify the small-noise formula for the specified decoder? Are all statements limited to its leading coefficient?
7. Does qualitative approximate rigidity state sufficient common regularity? We claim no explicit rate. Are the implementation and peak-feasible quantization assumptions adequate?

The primary-source applicability map appears in `notes/novelty_review.md` and `notes/novelty_challenge.md`. An originality objection should name the prior theorem and match its hypotheses to ours.

## Reading map

| Purpose | Files |
|---|---|
| Model and assumptions | `manuscript.tex`, `sections/model.tex`, `sections/assumptions.tex` |
| Essential necessity and conditioning | `sections/rigidity.tex`, `sections/synthesis.tex`, `sections/decoding.tex` |
| New design frontier | `sections/inverse_synthesis.tex`, `sections/pareto.tex` |
| Implementation and stability | `sections/implementation.tex`, `sections/approximate_rigidity.tex` |
| Positioning and overlap | `NOVELTY_MATRIX.md`, `CONTRIBUTION_OVERLAP.md`, the novelty notes |
| Recorded internal scrutiny | `notes/structural_review.md`, `notes/proof_review.md` |

For independent reconstruction, read the manuscript before the internal proof notes. Please identify each challenged implication and a counterexample, missing assumption, or proposed correction.

## Different-machine reproduction

Use a fresh source-package copy because generation scripts write their results and figures into that copy. Run from its root directory and record operating system, Python version, package versions, and failures. The documented environment uses Python 3.12.

The first check needs only Python's standard library and the stored rational witnesses:

```bash
python -S code/independent_reproduce.py --certificate-only --output results/external_certificate_check.json
```

Expected result: successful exact inequalities and relative gap approximately 0.00598910955%, with rational bounds in the output. Optimizer status is not the certificate.

For a fresh POSIX numerical environment:

```bash
python3.12 -m venv review_env
source review_env/bin/activate
python -m pip install -r requirements.txt
python code/independent_reproduce.py --output results/external_reproduction_check.json
```

The full second implementation checks certificates, analytic coefficients and moments, a separately constructed received-plane projection, and two active-frontier points. It does not rerun every Monte Carlo cell or independently prove the theorems.

Regenerate the main numerical evidence in the fresh copy:

```bash
python code/verify_extension.py
python code/verify_decoders.py
python -S code/certified_synthesis.py --verify-only
python code/finite_noise.py --trials 200000
python code/pareto_frontier.py --trials 200000
python code/make_figures.py
python build.py
```

The first two scripts report 135 and 98 checks. The frontier script produces 32 empirical rows and 12 convex numerical comparisons; interpret preserved optimizer statuses alongside residuals. For uniform sources, the 90%-retention points have b approximately 1.427841419869 and limiting MSE reductions approximately 17.68055% at K=4 and 29.07314% at K=16. Finite-noise gains need not equal these limits.

Compare rational outputs exactly, numerical quantities with documented tolerances, and simulations with paired uncertainty intervals. Plots and PDFs need not be bit-identical across library or TeX versions. Consult `REPRODUCIBILITY.md`, `notes/independent_reproduction.md`, and `notes/pareto_reproduction.md` for definitions, build prerequisites, and limits.

## Requested return

A useful report contains mathematical defects or the explicitly checked proof scope; missing antecedents and their implications; reproduction logs and deviations; and suggested claim narrowing. External review can reduce uncertainty but cannot guarantee exhaustive priority or journal acceptance.
