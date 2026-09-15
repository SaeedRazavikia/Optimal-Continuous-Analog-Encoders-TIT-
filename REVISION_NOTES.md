# Communications terminology revision — September 15, 2026

The submission remains **51 pages including references** and the extended arXiv version **57 pages**, with unchanged typography.

- Replaced “input configurations” with **input vectors**, introduced the vector of transmitter observations in the introduction, and used received sums explicitly where the distance is measured in the received plane.
- Defined **identifiable computation** in plain terms: the noiseless received sum uniquely determines the desired function value. The formal collision condition is unchanged, and the extension's common-completion condition remains distinct.
- Replaced visible “small-noise” wording with **high-SNR** or **asymptotic MSE coefficient**, as appropriate, throughout the abstract, body, proofs, captions, tables, figure labels, and coverage inventory.
- Specified the Gaussian noise convention: N0 is the complex noise variance/noise power per channel use, and each real component has variance N0/2. The high-SNR limit is N0→0 at fixed P, K, encoder, and input distribution; P/N0 denotes the per-transmitter peak SNR.
- Kept finite-SNR performance separate from optimization of the limiting MSE coefficient. Existing internal labels and numerical filenames remain stable.
- Shortened repeated explanations and the abstract to retain the page count while making the terminology explicit.

Both PDFs compile cleanly. Revised pages and the updated figure label were rendered and inspected. All 143 displayed mathematical blocks, numerical table values, plotted data, and audited Lean proof sources are unchanged. The 17 formal-statement extracts in COVERAGE.md match the current full manuscript source. The remaining formalization obligations are unchanged; this revision adds no formal proofs.

---

# Presentation and terminology revision — September 15, 2026

The submission is **51 pages including references**; the extended arXiv version is **57 pages**. This uses the author's approved two-page allowance for a clearer presentation. Font, margins, spacing, figure scale, and the submission/arXiv split are unchanged.

## Presentation changes

- Reframed the collision condition as **function identifiability**: equal noiseless received sums imply equal desired-function values. The model explicitly defines “f is identifiable through E” and “E identifies f,” and states the equivalent existence of a noiseless receiver.
- Rebuilt the introduction around one progression: function-dependent digital modulation, which collisions matter, the continuous-curve perspective, the variance example, identifiability, noise sensitivity, and geometric optimization.
- Explained why the two coordinates of a complex symbol carry real-valued additive statistics, and how restricting a continuous encoder to a finite alphabet gives a digital constellation. The text does not claim finite-alphabet global optimality from a continuous-class result.
- Clarified the abstract and scoped the projection decoder to the original function class.
- Added short transitions at the assumptions, characterization, convex design, enclosing ellipse, extension, decoding, certification, numerical results, and conclusion.
- Distinguished the extension's common-completion assumption on the prescribed preprocessing functions and postprocessing F from the identifiability condition on an encoder.
- Replaced computation-related “exactness” throughout the manuscript and retained “exact” where it refers to an algebraic identity, numerical certificate, score, or formula.

## Validation and scope

Both PDFs compile without unresolved references or overfull/underfull boxes; revised pages were rendered and inspected. All 143 displayed mathematical blocks match the preceding version byte for byte. Formal statements have only equivalent terminology changes. The coverage inventory's 17 statement extracts match the current full source verbatim; the submission retains 15 results.

Numerical scripts, recorded results, plotted data, and certificate values are unchanged. The package check verifies all 20 original numerical Git-blob identities and all 55 audited Lean source/configuration hashes. The Lean declaration names remain stable, and the coverage inventory explains their correspondence to identifiability/noiseless recovery. This presentation revision adds no formal proofs and does not change the remaining formalization obligations.

## Builds

```sh
latexmk -pdf manuscript.tex
latexmk -pdf manuscript_arxiv.tex
```

The source archive includes both build files and all arXiv-only appendices. The existing draft GitHub branch receives the revision without merging main.

---

# Previous content review — September 15, 2026

Before the presentation revision below, the submission was **49 pages including references** and the extended arXiv version was **55 pages**. Both retain the existing font, margins, spacing and figure scale.

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
