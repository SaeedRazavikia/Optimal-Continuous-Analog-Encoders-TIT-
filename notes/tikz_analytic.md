# Native analytic-encoder and certificate figures

The figure bodies in `figures/tikz/optimal_curves.tex` and
`figures/tikz/certified_synthesis.tex` use TikZ/PGFPlots exclusively. Encoder
paths use their analytic parametric equations; the figures do not embed any
PDF or raster artwork. The common blue/orange/teal/gray palette is supplied
by the manuscript preamble.

Run `python3 code/export_tikz_analytic.py` to regenerate the three small data
tables. This standard-library exporter evaluates the closed-form quadratic
coefficients, bisects the quartic scalar equation, and reconstructs the
exponential coefficients from the stored scaled rational Gram witness.
It does not rerun optimization or experiments. The tables carry full
floating-point display precision; the analytic identities and rational
certificate remain the sources of proof.

## Analytic curves

Place the three-panel plot in the explicit-optimal-curves section, after
the moment-interaction result. Each panel shows the unit peak boundary,
the stated baseline, the optimal curve, exact peak contacts, source-value
annotations, and the normalized optimal separation score. The quartic
contact labels use the rho defined in the accompanying theorem.

Suggested caption:

> Optimal encoder geometry under the same pointwise peak constraint,
> normalized by sqrt(P). The markers identify the exact peak contacts.
> Panels (a) and (c) use the baseline sqrt(P)[s+i(s^2-1)]; panel (b) uses
> (2sqrt(P)/sqrt(5))[s+i(s^4-1/2)]. Here bar-lambda equals
> Lambda_sq/(K^2 P). The quadratic readout changes the optimal scales,
> whereas the quartic feature changes the contact structure.

## Certified nonpolynomial synthesis

Preserve the original figure placement following the exponential example.
The left panel shows the analytic exponential curve reconstructed from
the **scaled** certificate, including the candidate contact inputs
-1, 159/200, and 1. These are not exact contacts of the final feasible
curve: conservative certification puts their normalized power near
0.9999414. Open markers and the phrase 'candidate contacts' distinguish
these inputs from the analytic peak contacts in the preceding figure.

The right panel preserves the original experiment: hold the candidate
Gram matrix and dual upper witness fixed, and refine only the verification
grid. Its five displayed gap percentages are computed from the stored
exact rational lower and upper bounds. The final value is 0.00598910955%.
This is a certified global-score gap, not an empirical solver error or an
MSE percentage. The fixed-candidate limiting gap includes witness repair
and candidate errors; the plot does not claim asymptotic convergence to
zero for the fixed data.

Suggested caption:

> Certified exponential-feature synthesis. (a) The reconstructed feasible
> encoder and unit peak boundary; open markers identify candidate contact
> inputs before conservative feasibility repair. (b) The certified global
> relative gap for verification grids with 51--1001 points, with the
> candidate and dual upper witness fixed. The final gap is below 0.006%.

Both figure bodies passed an isolated two-pass LaTeX compilation and
visual inspection. The preview has no LaTeX warnings. The parent workflow
performs the full manuscript compilation and page-level visual review,
and owns the shared preamble and figure placement.
