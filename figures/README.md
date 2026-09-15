# Editable LaTeX figures

Every figure in the manuscript is drawn directly with TikZ/PGFPlots. The manuscript does not embed raster plots or pre-rendered figure PDFs.

| Input under `tikz/` | Purpose | Placement |
|---|---|---|
| `system_model.tex` | Shared encoders, complex multiple-access channel, additive noise, and prescribed computation | System-model introduction |
| `certified_synthesis.tex` | Exponential encoder and certified verification-grid gap | Certified synthesis |
| `optimal_curves.tex` | Variance, quartic Jensen gap, and moment-interaction curves with peak contacts | Explicit optimal curves |
| `decoder_geometry.tex` | Received moment region, containing strip, and projection decoder | Decoding |
| `pareto_frontier.tex` | Robustness–asymptotic-MSE tradeoff and containing ellipses | Frontier theorem |
| `finite_noise.tex` | Paired finite-SNR comparisons and confidence intervals | Numerical evidence |

`tikz/styles.tex` defines the shared palette and plot styles. Curves also use different line styles and markers so their identities remain clear in monochrome. Captions are maintained in the manuscript sections.

The committed numeric tables under `data/` are sufficient to compile the paper. To regenerate these tables from the stored results and analytic formulas, run from the manuscript root:

```bash
python code/export_tikz_analytic.py
python code/export_tikz_empirical.py
```

These commands export plotting data; they do not run a new optimization or Monte Carlo study. The primary results and certificate files retain their existing meanings.

Compile the entire paper with `latexmk -pdf manuscript.tex`. To export one figure independently on a configured TeX installation, run from the manuscript root:

```bash
pdflatex -jobname=optimal_curves '\def\FigureName{optimal_curves}\input{figures/standalone.tex}'
```

Replace `optimal_curves` in both places with another figure name from the table. Keep the working directory at the manuscript root so PGFPlots can resolve the data tables.
