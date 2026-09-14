# TIT audit and required outputs

## Mathematical audit priorities

| ID | Check | Failure that must be ruled out |
| --- | --- | --- |
| A1 | Common-input completion for equal encoded triples | Using a fourth variable when $K=3$, changing other inputs inconsistently, or requiring injectivity of a derivative without the stated convexity assumptions |
| A2 | Local fiber-variation lemma | Missing openness, lack of injection for fixed fiber coordinate, or an unjustified continuity assumption on the decoder |
| A3 | Convolution regularity step | Integrating outside the common local chart, an unjustified cutoff, insufficient regularity of the feature, or differentiating an arbitrary continuous decoder |
| A4 | Global affine dependence and nondegeneracy | Locally varying coefficients treated as globally constant, overlooked endpoint behavior, or dependent feature vectors |
| A5 | Exact squared score | Proving only a lower bound, using unattainable moment perturbations, or exchanging limiting operations without control |
| A6 | Synthesis and rank reconstruction | A higher-dimensional Gram solution incorrectly called planar, lost peak constraints, missing compactness, or an unbounded/zero optimum |
| A7 | Explicit solutions | Incorrect output normalization, missing competing parameter ranges, spurious quartic roots, unverified KKT signs, or numerical equality treated as a proof |
| A8 | Polynomial extension | Dropping the common-parity/nonnegative-coefficient assumptions or overlooking the pure highest-second-moment case |
| A9 | Operational decoder | An explicit noiseless readout incorrectly called globally Lipschitz under noise; confusing uniform amplification, fixed-radius risk, and MSE |
| A10 | Transfer and class breadth | Inferring universal symmetric-function coverage, finite-alphabet optimality, or uncentered-exponential optimality from the squared result |

## Deliverables for the next model

1. `RESEARCH_ASSESSMENT.md`: an independent content judgment, the strongest defensible contribution, and the main unresolved issues.
2. `PROOF_AUDIT.md`: exact source locations, reconstructed arguments, defects found, and repairs. Label this an internal assessment rather than external peer review.
3. `CLAIMS_UPDATED.json`: preserve claim IDs, record assumptions, proof status, dependencies, and whether each result belongs in the manuscript.
4. `NOVELTY_MATRIX.md`: primary-source comparisons and explicit uncertainty about priority.
5. `CONTRIBUTION_OVERLAP.md`: theorem-level allocation between TIT and TCOM.
6. `manuscript.tex`, bibliography, figures, and a compiled PDF, when the validated results support a coherent article. Retain verified author information and do not infer missing coauthors. Use a title appropriate to the new content unless the researcher has explicitly fixed a title for this new paper; the legacy coherence title is not binding.
7. Reproducible scripts and result files for any new substantive numerical evidence, with environment requirements and a clear distinction between old and new runs.
8. `REPRODUCIBILITY.md`: how to rebuild the draft and reproduce the reported figures. Include continuum-certification details where claimed.
9. A final source ZIP containing the new work and enough proof context to review it independently.

If a central result fails, produce items 1–5 and the strongest corrected development rather than a manuscript that conceals the problem. Do not turn a research limitation into a claim of publication readiness.

## Adequate verification

Check assumptions and analytic certificates first. Run numerical checks to catch algebraic, normalization, boundary, and implementation errors. Broaden computation only to address a remaining concrete risk. The existing verification scripts are useful starting points; passing them does not prove the topological lemma or establish novelty.
