# Research assessment after further development

The manuscript now links exact continuous computation, worst-case disturbance protection, and prior-dependent small-noise efficiency in one global design problem. This supports a focused journal submission draft; historical originality and acceptance remain unresolved.

## What strengthens the contribution

- The necessity proof derives local factorization from scalar exactness and classifies every admissible continuous shared planar encoder. Additional internal adversarial review found no invalidating defect under the stated hypotheses. The closest restricted-additive precedent receives explicit credit.
- Inverse-metric coordinates give six-variable separation synthesis and five-variable constrained small-noise synthesis. The latter has a linear objective in these coordinates. We prove attainment, uniqueness of the optimal feature Gram matrix, continuity and convexity in the separation floor, and a plateau followed by an active strictly increasing branch.
- For quadratic features, an even readout, and a symmetric mean law, symmetry and domination yield an explicit frontier over the full continuous exact class. For independent uniform sources, retaining 90% of optimal squared separation reduces the limiting MSE coefficient by 17.68% at K=4 and 29.07% at K=16, while increasing the sharp disturbance factor by at most 5.41%. These percentages describe different quantities.
- A qualitative approximate-rigidity corollary covers compact encoder classes with a common decoder Lipschitz bound. Deterministic quantization and residual-channel bounds clarify implementation sensitivity.
- A second implementation reproduces the exponential certificate, analytic moments and coefficients, a received-plane decoder comparison, and selected frontier points. The exact certificate has a relative enclosure gap of approximately 0.00598911%.

## What remains unresolved

1. **Historical priority and significance.** The local reduction may be judged a short application of established additive rigidity and topology. The complete design chain and explicit frontier should carry the contribution statement. A specialist should assess this issue.
2. **External proof scrutiny.** Internal agent reviews do not constitute review by researchers outside this workflow. The proof chain is ready for external reconstruction.
3. **Different-environment reproduction.** The second implementation ran in the same environment. The complete package has not yet been reproduced on an independently prepared machine or container.
4. **Scope.** The frontier optimizes the leading small-noise coefficient for the specified decoder and source law over continuous exact encoders. It does not optimize unrestricted finite-noise Bayesian risk or justify exchanging optimized noise-dependent designs with a small-noise limit. Approximate rigidity has no explicit rate.
5. **Draft comparison.** The author confirmed that the bivariate draft is not planned for submission. The current paper omits its citation; the internal comparison distinguishes its finite-noise results from the present robustness-constrained small-noise design.

Independent reproduction found that some endpoint-concentrated K=4 cells remain below their asymptotic MSE constants by several Monte Carlo standard errors at 30 dB. The decoder includes clipping; these cells must not be described as already asymptotic. This limits numerical interpretation, not the proved limit.

The next useful actions are external theorem review and different-machine reproduction. `EXTERNAL_REVIEW_PACKET.md` supplies a concrete brief and commands; `DEVELOPMENT_RECORD.md` records the completed work.
