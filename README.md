# Geometric Optimization of Continuous Encoders for Moment-Based Computation

Saeed Razavikia. Revised September 15, 2026.

The manuscript studies exact computation of real-valued moment-based functions over a multiple-access channel using one shared continuous encoder and one complex channel use. It characterizes the required encoder structure under stated assumptions, optimizes peak-constrained separation, and develops sharp decoding and a robustness–small-noise tradeoff. The extension treats two prescribed additive statistics under a common-completion identification condition.

Build the current IEEE single-column manuscript with:

~~~sh
latexmk -pdf manuscript.tex
~~~

Edit the LaTeX files in the root and sections directory, and use bibliography.bib for references. The figure sources and plotting data are included. The source package also contains the numerical code, archived experiments, and exact rational certificates. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for commands and [NUMERICAL_SOURCE.json](NUMERICAL_SOURCE.json) for their original source identities.

The Lean project is in [formalization/](formalization/). Its [coverage inventory](formalization/COVERAGE.md) distinguishes complete formal statements from conditional components and remaining manuscript obligations. The full continuous-encoder converse and some further specializations remain incomplete. A successful build and axiom audit certify the declarations actually written, not unformalized paper results.

Run the pinned Lean build and audit from the formalization directory:

~~~sh
lake exe cache get
python3 verify.py
~~~

The audit records exact proof-source hashes and logical dependencies. The project uses no additional mathematical axioms or unfinished proofs. [REVISION_NOTES.md](REVISION_NOTES.md) describes the current changes; older development and submission notes retained in the repository describe earlier snapshots.
