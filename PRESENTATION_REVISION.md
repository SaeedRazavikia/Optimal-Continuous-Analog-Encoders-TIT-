# Presentation and submission revision

This revision implements the requested focus on contribution positioning, companion overlap, submission preparation, and native LaTeX figures. It does not initiate outside review or a new reproduction study.

## Manuscript changes

- Recast the introduction around three contributions: necessary encoder features, exact robustness and peak design, and the global robustness–small-noise-accuracy frontier.
- Compared the actual supplied bivariate companion manuscript, replacing the earlier roadmap-only allocation. The introduction and bibliography identify that related draft without inventing its publication or submission status.
- Expanded the system model into shared encoding, the complex multiple-access observation equation, target/exactness, and the design objective. Defined the per-terminal peak condition and noise convention explicitly.
- Added a full-width system diagram and a received-plane projection figure. The latter distinguishes the exact four-terminal moment region from the containing strip used by the decoder; the text explains the depicted region.
- Rebuilt every existing plot in TikZ/PGFPlots. Placed explicit encoder curves with their analytic theorems and the frontier figure with the tradeoff result. Preserved archived numerical values and paired uncertainty.
- Added a transparent acknowledgment of AI-assisted content development, with the governing IEEE policy and final author responsibilities documented in `SUBMISSION_PREPARATION.md`.

## Figure design

The six figures use a consistent serif mathematical style, restrained blue/orange/teal colors, vector lines, and distinguishable markers or dashes. Axes describing Euclidean geometry preserve equal scales. Source-value contacts, feasibility boundaries, confidence intervals, and the distinction between an encoder curve and a feature-space ellipse remain explicit.

Every visual compiles natively from LaTeX. `figures/README.md` gives the complete source map; the standalone wrapper exports individual figures without changing the manuscript.

## Submission materials

- `SUBMISSION_PREPARATION.md`: source-grounded requirements and the remaining author-specific declarations.
- `COVER_LETTER_DRAFT.md`: substantive cover-letter draft with the contribution and related-manuscript disclosure.
- `CONTRIBUTION_OVERLAP.md`: comparison of the actual supplied companion and the present manuscript.
- `NOVELTY_MATRIX.md`: established precedents and the specific claims retained here.

The current PDF and source archive are prepared for author review. Submission itself and declarations about current publication status, author approval, or competing interests require the author's factual confirmation.
