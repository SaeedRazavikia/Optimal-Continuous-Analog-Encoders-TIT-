# Final content review — September 15, 2026

The corrected submission is **49 pages including references**; the extended arXiv version is **55 pages**. Both retain the existing font, margins, spacing and figure scale.

## Corrections

- Removed submission-only introduction claims about the approximate-rigidity and criterion-comparison appendices; these claims now appear only in the arXiv version, where the appendices are included.
- Stated K≥1 explicitly in the system model.
- Clarified that a continuous decoder attains the amplification infimum when finite, instead of saying it attains “every finite value.”
- Replaced the claim that projection is essential with the precise statement that it controls the raw inverse outside the noiseless received set; the McShane extension is another valid construction.
- Clarified the separation floor γ, which divides the operational score by K² and is not the separate K²P normalization used in numerical tables.
- Distinguished the quantizer symbol from the second-moment sum Q and stated its bounded-input error domain.
- Qualified the introduction's strictly increasing frontier branch consistently with the theorem's conditional statement.
- Clarified that the freely chosen preprocessing representation requires only continuous γ; the classification theorem has stronger assumptions.
- Clarified that prior-aware tuning, rather than every reported MSE improvement, can reduce robustness.
- Corrected the amplitude-modulation attribution: Goldenbaum et al. propose a digital nested-lattice construction and remain cited for nomographic representation and their stated coding result. [Primary paper](https://arxiv.org/pdf/1310.7123)
- Cited both Theorem 14 and Lemma 17 for Wagstaff et al.'s topology argument: the lemma establishes injectivity and the theorem applies the dimension argument. [Primary paper](https://jmlr.org/papers/volume23/21-0730/21-0730.pdf)

## Review and validation

Independent focused reviews covered the original rigidity and score proofs, Gram synthesis and enclosing ellipses, the unified extension and its specializations, decoding and small-noise limits, the frontier, certification, numerical tables/figures and literature attribution. These reviews found no substantive mathematical or numerical error in the checked material.

All numerical table bodies, plotted data, archived results and rational certificate values are unchanged. The mathematical results and proofs are unchanged; the amplification proposition has the wording clarification listed above. The complete source retains 17 formal statements; the submission includes 15, with the ancillary criterion-transfer and approximate-rigidity results kept for arXiv.

Both final PDFs compile without unresolved references, warnings or overfull/underfull boxes, and revised pages were rendered and inspected. All 55 audited Lean source/configuration hashes remain identical to proof commit 6783e9c68823213e2f4bc31259ab6a1ad6072d89. The existing formalization scope and open obligations remain explicit; this editorial review introduces no new formal proofs.

## Build and deliverables

```sh
latexmk -pdf manuscript.tex
latexmk -pdf manuscript_arxiv.tex
```

The source archive contains both build files, all arXiv-only appendices, the numerical reproduction package, the Lean project and SHA256SUMS.txt. The former assumptions table remains replaced by the concise assumptions in Section II-D. Corrections are published on the existing draft PR without merging main.
