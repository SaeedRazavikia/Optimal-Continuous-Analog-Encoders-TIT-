# Reproducing the paper and experiments

Run the commands below from the repository root. Lean proof verification is
documented separately in [formalization/README.md](../formalization/README.md).

## Build the paper

Install a configured TeX distribution with `latexmk`, pdfLaTeX, BibTeX,
IEEEtran, TikZ/PGFPlots, and the packages declared in `Main.tex`. Then run:

```sh
python3 build.py
```

The output is `build/Main.pdf`. The wrapper also works when invoked by its
absolute path from another directory. It builds the current `Main.tex` and
resolves its bibliography automatically. Generated TeX files stay in `build/`.

The six manuscript figures and their shared style file are editable LaTeX
sources in `figures/`. Their plotting data are embedded, so building the paper
does not require Python packages or a new experiment run.

## Check the exact numerical certificate

This check uses Python's standard library and the committed rational witnesses:

```sh
python3 -S code/certified_synthesis.py --verify-only
```

It checks the exponential-design certificate with exact rational arithmetic.
It does not invoke the numerical optimizer or replace the general Lean proof.

## Run the numerical checks

Create an isolated Python environment and install the pinned dependencies:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python code/independent_reproduce.py
python code/verify_decoders.py
python code/verify_extension.py
```

The first command after installation independently implements the certificate
and selected analytic and decoder calculations. The other checks test the
decoder implementation and example formulas. These are numerical checks, not
proofs of the universal mathematical statements. The second implementation is
part of this project; it is not external human review.

## Regenerate the experiments

With the same environment active, run:

```sh
python code/finite_noise.py --trials 200000
python code/pareto_frontier.py --trials 200000
```

The committed JSON files in `results/` are the reference outputs. These commands
and the numerical-check commands overwrite their corresponding result files.
They may also create CSV diagnostics and PDF/PNG plots. Use a separate checkout
if you want to compare a new run with the committed results. Seeds, settings,
package versions, and uncertainty estimates are recorded in the JSON outputs.

Regenerating experiments does **not** update the values embedded in the
manuscript's LaTeX figures; inspect and transfer any intended changes explicitly.
The experiments compare specified designs and decoders at finite noise. They do
not establish unrestricted finite-noise MSE optimality.

For the full settings and interpretation, see the
[finite-noise experiment design](experiments/experiment_design.md),
[variance frontier experiment](experiments/pareto_reproduction.md), and
[independent implementation notes](experiments/independent_reproduction.md).
