# Coverage of the current manuscript

This inventory covers ten results in
[arXiv:2610.21536v1](https://arxiv.org/abs/2610.21536v1).
The [statement and proof guide](../docs/STATEMENTS.md) connects each paper result
to its Lean declarations. [paper_targets.json](paper_targets.json) retains the
reviewed statement excerpts, paper links, and declaration mappings.
`python3 check_correspondence.py` checks this local correspondence record;
mathematical correspondence to the external paper still requires reading the
statements and their hypotheses.

The core verified areas are full heterogeneous rigidity, general
SDP attainment, Gaussian converse and optimization proofs, and general grid
certification. The Gaussian results include the fixed-prior all-Borel limit,
the fixed-encoder worst-case limit, and optimization over noise-dependent
encoder designs, with an attained noise-independent encoder and decoder.
All ten numbered results now have complete recorded correspondence, including
the exact minimum decoder, its Gaussian limit, the finite-node endpoint score,
and the unrestricted quadratic/quartic optima. Additional unnumbered claims
and numerical examples remain outside the scope described below.

A successful [`verification/report.json`](verification/report.json) checks the
stated Lean declarations. It does not turn a specialized or conditional result
into a broader manuscript theorem. Earlier inventories are available in
[Git history](https://github.com/SaeedRazavikia/Rigidity-and-Limits-of-Continuous-Encoders/tree/54d1083238b5e3e9a009138c3bb69c09d37f58e9/formalization/historical).

## Current statements

All namespaces below have the prefix `Analog.`. Links open the source containing
the named declarations.

| Manuscript target | Verified correspondence | Scope and remaining work |
|---|---|---|
| `thm:rigidity` | [`HeterogeneousFullRigidity.heterogeneous_rigidity`](Analog/HeterogeneousFullRigidity.lean) proves the full iff under the manuscript's original closed-domain assumptions. | **Complete.** Arbitrary continuous node encoders, separate feature curves, common nonsingular columns, individual offsets, and both source endpoints. Completion separation, actual moment-domain density, planar invariance of domain, local charts, encoder regularity, derivative relations, and tangent anchors are derived. No decoder regularity or extra C² hypothesis is assumed. |
| `thm:sdp` | [`HeterogeneousAttainment.heterogeneous_sdp_attained`](Analog/HeterogeneousAttainment.lean), `optimal_positive_iff_euclidean_lipschitz`, and [`HeterogeneousGlobalOptimum.unrestricted_sdp_attained`](Analog/HeterogeneousGlobalOptimum.lean). | **Complete.** Actual operational maximum and exact secant-SDP maximum are both attained with equal value, including dependent features, singular Gram blocks, and zero optimum. Positivity is equivalent to Lipschitz continuity on the actual attainable set. Under rigidity assumptions the same attained optimum dominates every continuous peak-feasible encoder, including those without exact computation. |
| `prop:amplification` | [`Decoder.sharp_uniform_decoder`](Analog/Amplification.lean) and `zero_score_no_finite_uniform_decoder`. | **Complete operational alternatives.** Generic arbitrary received/target maps cover heterogeneous encoders. A continuous decoder attains the sharp finite constant at positive score; zero score excludes every finite constant. The latter represents the manuscript's `+∞` convention without treating infinity as a real number. |
| `thm:decoder` | [`CompactMinimumDecoder.heterogeneous_minimum_decoder`](Analog/CompactMinimumDecoder.lean), [`CompactMinimumDecoder.momentConstant_eq`](Analog/CompactMinimumDecoder.lean) | **Complete.** The displayed minimum over the actual compact moment set is attained at every observation. This specific decoder is globally Lipschitz, exact, and attains the smallest uniform amplification constant `1 / sqrt(score)`. The channel uses the sum of all individual offsets and the actual factor `K`; singular columns are allowed. |
| `prop:radius-minimax` | [`RadiusMinimax.borel_radius_minimax`](Analog/RadiusMinimax.lean). | **Complete.** For compact continuous-input models, an actual maximizing pair and a Borel consistency-midpoint decoder attain half the pair modulus. The lower bound applies to every decoder, including radius zero and nonidentifiable maps. The finite input cube and complex channel are covered by this generic result. |
| `thm:identifiable-minimax` | [`GaussianFixedMinimax.fixed_encoder_minimax`](Analog/GaussianFixedMinimax.lean) and [`GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved`](Analog/GaussianOptimizedMinimax.lean). | **Complete.** Both actual all-Borel-decoder minimax limits hold as noise tends to zero from above. The optimized theorem uses the actual finite-node attainable image, derives its compactness/nonemptiness and coefficient compactness, excludes singular limiting channels, and includes designs that vary with noise. An attained fixed peak-feasible nonsingular encoder and one explicit noise-independent decoder achieve the same coefficient. The true channel is `K U`; normalization by total complex noise `2v` and the resulting `1/(2K²)` coefficient are proved. |
| `prop:general-small-noise` | [`MinimumDecoderGaussianLimit.heterogeneous_fixed_prior_minimum`](Analog/MinimumDecoderGaussianLimit.lean), [`MinimumDecoderGaussianLimit.fixed_prior_minimum_inverse_trace`](Analog/MinimumDecoderGaussianLimit.lean) | **Complete.** Both the all-Borel optimal risk and the particular minimum-formula decoder have the prescribed Gaussian limit. The minimum is over the actual attainable image; compactness is derived, the true channel is `K U`, all offsets are retained, and the coefficient has factor `1/(2K²)`. The fixed decoder is independent of both the regular prior and the noise level. |
| `prop:score` | [`FiniteNodeScore.lemma_one_score`](Analog/FiniteNodeScore.lean), [`FiniteNodeScore.lemma_one_sharpness`](Analog/FiniteNodeScore.lean) | **Complete.** The endpoint inverse-Gram formula and arbitrarily short sharp pairs are proved for the actual `Fin K` model, arbitrary node offsets, and both strict convexity/concavity alternatives. Exact equality of quotient sets transfers the shared-feature proof to node-indexed inputs. Endpoint slopes use the derivative within the closed source interval. |
| `thm:parabola` | [`PolynomialGlobalOptima.quadratic_global_optimal`](Analog/PolynomialGlobalOptima.lean), `quartic_global_optimal`, and [`PolynomialOptimizerFacts`](Analog/PolynomialOptimizerFacts.lean). | **Complete.** Original even C¹ strictly convex/concave readouts, every positive power budget `P`, the displayed encoder and score formulas, and the unique quartic root. Endpoint symmetry and positive slope magnitude are derived. Averaging offsets preserves the aggregate and peak feasibility; proved rigidity gives comparison with every continuous peak-feasible encoder, including zero-score competitors. |
| `thm:certifiedgrid` | [`HeterogeneousGrid.certified_discretization`](Analog/HeterogeneousGrid.lean), `scaling_gap_isBigO`, and [`HeterogeneousGlobalOptimum.grid_maximum_global_bound`](Analog/HeterogeneousGlobalOptimum.lean). | **Complete.** Actual node-dependent grids and common Gram block; sampled and continuum optimizer attainment; derived C² spectral remainders with the sharp `1/8` factor; one common feasible scaling; the objective bracket; uniform `O(h²)` scaling loss; and reconstructed continuous encoders with score at least `K²ρ_hλ_h`. All moment-pair secants are retained. The unrestricted-encoder interpretation follows from the proved rigidity/global-optimum bridge. |

## Additional current claims

- **General finite matrix dual witness:**
  [`HeterogeneousDualCertificate.current_program_dual_upper_bound`](Analog/HeterogeneousDualCertificate.lean)
  derives the bound directly from the current PSD constraints, finite
  nonnegative weights, normalizing scalar identity, and common-block matrix
  identity. The trace inequalities are proved from the matrices, rather than
  supplied as an extra scalar premise. `FiniteCertificates` supplies the
  associated scaling and absolute/relative gap arithmetic.
- **Gradient sandwich:** the general interior lower bound, convex-superset
  upper bound, and compact-convex equality have not been assembled into the
  current manuscript statement. The earlier endpoint localization is a
  special case.
- **Numerical examples:** the paper's numerical certificate and experiments
  are not part of this formalization repository. The general Lean certification
  theorems do not individually verify every reported numerical value.
- **Remaining examples and exposition:** not every moment-set description,
  output-range calculation, counterexample, or empirical plot is formalized.
  Earlier frontier, transfer, and approximate-rigidity results remain in the
  project, but do not add numbered targets to the current manuscript.

## Reading the verification record

The strongest named correspondences are collected in
[`THEOREM_MAP.md`](THEOREM_MAP.md). The proof chain is documented in
[`notes/completion-rigidity.md`](notes/completion-rigidity.md),
[`notes/completion-separation.md`](notes/completion-separation.md),
[`notes/completion-sdp.md`](notes/completion-sdp.md),
[`notes/completion-global-optimum.md`](notes/completion-global-optimum.md),
[`notes/completion-grid.md`](notes/completion-grid.md),
[`notes/fixed-prior-gaussian-limit.md`](notes/fixed-prior-gaussian-limit.md), and
[`notes/gaussian-fixed-minimax.md`](notes/gaussian-fixed-minimax.md),
[`notes/compact-minimum-decoder.md`](notes/compact-minimum-decoder.md),
[`notes/minimum-decoder-gaussian.md`](notes/minimum-decoder-gaussian.md),
[`notes/finite-node-score.md`](notes/finite-node-score.md),
and [`notes/polynomial-global-optima.md`](notes/polynomial-global-optima.md).
The final optimized theorem is in
[`Analog/GaussianOptimizedMinimax.lean`](Analog/GaussianOptimizedMinimax.lean).
This inventory is the current scope record. No missing conclusion is inserted
as an axiom.
