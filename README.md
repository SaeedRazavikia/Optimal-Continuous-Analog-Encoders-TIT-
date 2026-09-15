# Geometric Optimization of Continuous Encoders for Moment-Based Computation

Saeed Razavikia. Revised September 15, 2026.

The manuscript studies identifiability and robust computation of real-valued moment-based functions over a multiple-access channel using one shared continuous encoder and one complex channel use. It characterizes the required encoder structure under stated assumptions, optimizes peak-constrained separation, and develops sharp decoding and a robustness–small-noise tradeoff. The extension treats two prescribed additive statistics under a common-completion identification condition.

Build the 51-page submission version (including references) with:

~~~sh
latexmk -pdf manuscript.tex
~~~

Build the 57-page extended arXiv version with:

~~~sh
latexmk -pdf manuscript_arxiv.tex
~~~

Both builds use the same font, margins, spacing, main results and proofs. The arXiv wrapper enables the ancillary criterion, approximate-rigidity and Lean-verification appendices. The submission excludes those appendices; their sources remain in this package. The former assumptions table is replaced by the concise assumptions in Section II-D.

Edit the LaTeX files in the root and sections directory, and use bibliography.bib for references. The figure sources and plotting data are included. The source package also contains the numerical code, archived experiments, and exact rational certificates. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for commands and [NUMERICAL_SOURCE.json](NUMERICAL_SOURCE.json) for their original source identities.

The Lean project is in [formalization/](formalization/). Its [coverage inventory](formalization/COVERAGE.md) distinguishes complete formal statements from conditional components and remaining manuscript obligations. The full continuous-encoder converse and some further specializations remain incomplete. A successful build and axiom audit certify the declarations actually written, not unformalized paper results.

Run the pinned Lean build and audit from the formalization directory:

~~~sh
lake exe cache get
python3 verify.py
~~~

The audit records exact proof-source hashes and logical dependencies. The project uses no additional mathematical axioms or unfinished proofs. [REVISION_NOTES.md](REVISION_NOTES.md) describes the current changes; older development and submission notes retained in the repository describe earlier snapshots.
