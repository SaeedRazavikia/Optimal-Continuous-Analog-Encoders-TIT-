# Review corrections and formal verification — September 15, 2026

## Manuscript corrections

The revision preserves the title, section structure, main mathematical claims, and numerical values. It makes these targeted corrections:

- Uses “infimum” for the all-pair separation criterion in the introduction.
- Defines the dissimilarity-based criterion explicitly and distinguishes its symbol from the decoder.
- Describes paired-delta-method intervals as nominal pointwise 95% confidence intervals.
- Makes continuity explicit for the prescribed bounded preprocessing curve in the extension example and proof.
- Clarifies the fixed-encoder optimization over exact decoders and the scope of the strip decoder's small-noise statement.
- Removes unnecessary differentiability from the collision lemma.
- Protects capitalization of scheme names, mathematical terms and Lean in the bibliography.
- Adds an immutable numerical-source citation and restores scripts, archived results and reproduction instructions to the source package.
- Updates Appendix I and proof-coverage documents to describe the enlarged checked development and remaining gaps.

Table values, figure data and certificate bounds agree with the archived numerical records. The exact rational certificate was independently rerun. Simulation intervals remain empirical evidence, separate from Lean verification.

## Formalization changes

Fourteen additional proof modules extend the preceding 33-module artifact. The new development proves general two-statistic compactness and positive attainment, positive definiteness from common-completion identification, general sharp decoding and the circular-Gaussian trace limit with output clipping, continuity of the attained Gram frontier, enclosing-ellipse equivalence, the explicit quadratic frontier, C² grid certification and its O(h²) scaling loss, dissimilarity transfer, and approximate-computation stability for the actual compact encoder class.

The rigidity components now include genuine local inverse charts, local continuous extension and convolution smoothing, propagation from the dense identifying set, and integration through endpoints. Local factorization must still be derived from exact computation using planar invariance of domain. Full unrestricted classification and its assembly, the analytic identification criterion, general endpoint-gradient specializations, and further coverage-inventory items remain incomplete. Approximate stability's affine-family conclusion retains exact-classification as a dependency. Missing results are not inserted as axioms or claimed as proved.

The exact declaration inventory and proof-source hashes are in formalization/verification/report.json. COVERAGE.md records all 17 numbered statements and additional unnumbered claims, distinguishing complete coefficient-class results from unrestricted statements.

## Validation and version identity

The full build passed (2,781 jobs), and the `lean --trust=0` audit passed for 673 declarations in 47 modules, with all 55 source/configuration hashes matching. The pinned Lean 4.24.0/mathlib project rejects warnings; only propext, Classical.choice and Quot.sound are accepted. Compiler binaries and dependency caches are excluded.

The final manuscript compiles to 59 pages without warnings, unresolved references, or overfull/underfull boxes. Changed pages were rendered and visually inspected. SHA256SUMS.txt records the packaged files. Numerical scripts and archived results retain their exact source identities at commit 7a513ed38147a73f109f9b184dafba59c17ee89b.

The manuscript's proof-artifact citation identifies audited proof commit 6783e9c68823213e2f4bc31259ab6a1ad6072d89. Updates are published on the existing codex/lean-two-statistic-extension branch and draft pull request, without merging main. A local audit and a GitHub Actions run are separate records.

## Reproduction

Build the paper with `latexmk -pdf manuscript.tex`. Run `lake exe cache get` and `python3 verify.py` from formalization for the proof audit. See REPRODUCIBILITY.md for numerical commands and formalization/README.md for precise verification scope.
