# Certified nonpolynomial synthesis

The new section is `sections/certified_synthesis.tex`; it belongs immediately after the existing synthesis section. It uses labels `sec:certified`, `thm:certifiedgrid`, `eq:certifiedgrid`, `eq:dualwitness`, `eq:expcertificate`, and `fig:certified`.

## Scope and novelty

This section closes a computational completeness gap in the manuscript. It combines standard finite-grid convex optimization, a linear interpolation remainder, and weak duality. It does not claim that discretization, interpolation error control, rational interval arithmetic, or SDP dual certification is new. The contribution is their explicit integration with the paper's globally exact encoder formulation and a reproducible nonpolynomial example. The theorem adds the assumption phi in C2 solely for this certified numerical scheme; it does not restrict the rigidity or exact-score results.

## General theorem

For `q_H(s)=z(s)^T H z(s)`, the bound

`|q_H''| <= 2 ||H|| (Z1^2 + Z0 Z2)`

controls a linear interpolation remainder by `M h^2/8`. The finite-grid optimum `U_h` is an upper bound on the continuous optimum. Scaling its primal Gram matrix and lambda by `P/(P+M h^2/8)` gives an achieved lower bound. Three fixed spanning feature vectors uniformly bound every grid-feasible Gram matrix, making the gap O(h2). Endpoint inclusion and these three anchors are stated explicitly. Nested grids are unnecessary for convergence, although they would imply monotonically decreasing exact upper bounds.

For an arbitrary verified candidate, including a candidate that slightly violates sampled peak constraints, use the verified sampled maximum `b_h` and scale by `P/(b_h+M h^2/8)`. Any finite nonnegative peak weights alpha and PSD score multipliers D± satisfying the documented dual residual and normalization give the global upper bound `P sum alpha`. No solver success status or unverified floating eigenvalue is used as a certificate.

## Implemented example and exact certificates

Target: `mean(exp(s_k)) - exp(mean(s_k))`, on [-1,1], any K>=4, P=1. Scale coefficients by sqrt(P) and multiply scores by K2 P for other settings.

- Candidate: SciPy SLSQP, 401 peak samples, seven real variables. This solves the finite convex formulation using nonlinear eigenvalue constraints. A candidate is not trusted without verification.
- Primal witness: stored rational 3x3 H, diagonal perturbation 1e-8, rational lambda reduced by 1e-8. Exact interval principal-minor checks certify H and both score LMIs positive definite.
- Primal continuum certificate: 1001 rational sample points. Exact Taylor interval calculations yield sampled maximum at most 1.000000093894. The direct exponential-feature derivative bound is M=117. Therefore the entire unscaled curve has peak at most 1.000058593894. Reciprocal scaling yields the feasible certificate, then exact Schur-complement reduction reconstructs a planar curve without worsening peak.
- Dual: rational positive definite 2x2 matrices, rational nonnegative peak weights at -1, 159/200, 1 and anchor repair weights at -1,0,1. Exact interval arithmetic certifies the 3x3 dual residual positive definite and the score normalization at least one.
- Exponential enclosure: degree-40 Taylor polynomial around zero, remainder bounded in absolute value by 3/41! on [-1,1]. All interval endpoints and matrix arithmetic use Python Fraction, so floating roundoff cannot invalidate a successful certificate.
- Stored rational bounds:
  - L = 209834839284 / 500029296947
  - U = 104917556109394155472367 / 250000000000000000000000
- Decimal bounds: 0.41964508992808314 <= Lambda*/(K2 P) <= 0.4196702244375766.
- Relative gap `(U-L)/U` = 0.0000598910955076, i.e. 0.00598910955076%.
- The displayed decimal encoder coefficients are for orientation only. The exact rational scaled Gram matrix, Schur-complement reduction, and exact real factorization define the certified encoder.

## Reproduction

Run from the paper directory:

```
python code/certified_synthesis.py --verify-only
```

This verifies the stored primal/dual certificates without optimization. It uses only Python's standard library, including exact Fraction arithmetic; it does not load NumPy, SciPy, or an optimizer. To regenerate candidates, witnesses, the results JSON and figures:

```
python code/certified_synthesis.py
```

Generation used Python with NumPy, SciPy 1.17.0 and Matplotlib. SLSQP multiplier extraction requires SciPy with `OptimizeResult.multipliers` support; verify-only does not use that property. Runtime is a few seconds in the supplied environment. Different optimization environments can generate different valid witnesses, so the stored certificate is the authoritative reproducibility target.

## Meaning and limits of the figure

The convergence plot fixes one approximate candidate and a fixed dual witness; only the verification grid changes. Its residual floor includes candidate and repair errors. It is not a numerical test of exact finite-grid reoptimization at every resolution, and it does not prove O(h2); the theorem proves that rate for exact grid optimizers. No Gaussian error claim or comparative novelty claim is inferred from this example.
