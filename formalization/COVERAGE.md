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
The table retains the separate representation and example wrappers that are
not claimed to be complete.

A successful [`verification/report.json`](verification/report.json) checks the
stated Lean declarations. It does not turn a specialized or conditional result
into a broader manuscript theorem. Earlier inventories are available in
[Git history](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/tree/54d1083238b5e3e9a009138c3bb69c09d37f58e9/formalization/historical).

## Current statements

All namespaces below have the prefix `Analog.`. Links open the source containing
the named declarations.

| Manuscript target | Verified correspondence | Scope and remaining work |
|---|---|---|
| `thm:rigidity` | [`HeterogeneousFullRigidity.heterogeneous_rigidity`](Analog/HeterogeneousFullRigidity.lean) proves the full iff under the manuscript's original closed-domain assumptions. | **Complete.** Arbitrary continuous node encoders, separate feature curves, common nonsingular columns, individual offsets, and both source endpoints. Completion separation, actual moment-domain density, planar invariance of domain, local charts, encoder regularity, derivative relations, and tangent anchors are derived. No decoder regularity or extra C² hypothesis is assumed. |
| `thm:sdp` | [`HeterogeneousAttainment.heterogeneous_sdp_attained`](Analog/HeterogeneousAttainment.lean), `optimal_positive_iff_euclidean_lipschitz`, and [`HeterogeneousGlobalOptimum.unrestricted_sdp_attained`](Analog/HeterogeneousGlobalOptimum.lean). | **Complete.** Actual operational maximum and exact secant-SDP maximum are both attained with equal value, including dependent features, singular Gram blocks, and zero optimum. Positivity is equivalent to Lipschitz continuity on the actual attainable set. Under rigidity assumptions the same attained optimum dominates every continuous peak-feasible encoder, including those without exact computation. |
| `prop:amplification` | [`Decoder.sharp_uniform_decoder`](Analog/Amplification.lean) and `zero_score_no_finite_uniform_decoder`. | **Complete operational alternatives.** Generic arbitrary received/target maps cover heterogeneous encoders. A continuous decoder attains the sharp finite constant at positive score; zero score excludes every finite constant. The latter represents the manuscript's `+∞` convention without treating infinity as a real number. |
| `thm:decoder` | [`Decoder.pairwise_exists_lipschitz`](Analog/Decoder.lean), `sharp_uniform_decoder`, and `clip_uniform` construct a global exact Lipschitz decoder, prove the sharp uniform constant, and preserve the bound under output clipping. | These generic results apply to the current received map. The exact displayed **minimum over the compact moment set** has not been identified with that extension in a dedicated current-model theorem. The separately proved strip decoder remains a specialization. |
| `prop:radius-minimax` | [`RadiusMinimax.borel_radius_minimax`](Analog/RadiusMinimax.lean). | **Complete.** For compact continuous-input models, an actual maximizing pair and a Borel consistency-midpoint decoder attain half the pair modulus. The lower bound applies to every decoder, including radius zero and nonidentifiable maps. The finite input cube and complex channel are covered by this generic result. |
| `thm:identifiable-minimax` | [`GaussianFixedMinimax.fixed_encoder_minimax`](Analog/GaussianFixedMinimax.lean) and [`GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved`](Analog/GaussianOptimizedMinimax.lean). | **Complete.** Both actual all-Borel-decoder minimax limits hold as noise tends to zero from above. The optimized theorem uses the actual finite-node attainable image, derives its compactness/nonemptiness and coefficient compactness, excludes singular limiting channels, and includes designs that vary with noise. An attained fixed peak-feasible nonsingular encoder and one explicit noise-independent decoder achieve the same coefficient. The true channel is `K U`; normalization by total complex noise `2v` and the resulting `1/(2K²)` coefficient are proved. |
| `prop:general-small-noise` | [`FixedPriorGaussianLimit.fixed_prior_limit_inverse_trace`](Analog/FixedPriorGaussianLimit.lean) proves the full one-sided limit of actual optimal risk over all Borel decoders, with the prescribed inverse-Gram trace coefficient. `exact_decoder_prior_limit` proves the same leading risk for every fixed globally Lipschitz decoder exact on the attainable set. | **The statistical converse and equality are complete.** The prior may approach the boundary and need only have a positive C¹ density on an open full-mass interior region. The likelihood/additive-Gaussian bridge, compact-test score identity, variational density, and upper bound are proved. The separate identification of the displayed minimum-formula decoder is the remaining representation issue listed under `thm:decoder`. |
| `prop:score` | [`GeneralScore.general_operational_score`](Analog/GeneralScore.lean), `general_score_small_distance_sharpness`, and [`MomentPaths`](Analog/MomentPaths.lean). | The shared-feature endpoint formula and actual shrinking admissible pairs are proved under the written shape/regularity assumptions. A dedicated wrapper to the current `Fin K` model with arbitrary heterogeneous offsets remains unassembled; the current aggregate and offset-cancellation identities are available in `HeterogeneousScore`. |
| `thm:parabola` | [`quadratic_optimal_all_power`](Analog/PowerScaling.lean), [`GeneralQuadratic`](Analog/GeneralQuadratic.lean), [`Quartic.quartic_optimal_all_power`](Analog/QuarticPower.lean), and the operational variance specialization. | The all-power quadratic/quartic coefficient-Gram optima and stated parameter formulas are proved. Full rigidity and unrestricted SDP comparison are now available, but the current theorem's complete wrapper for general even strictly convex/concave readouts, offset averaging, and comparison with every continuous encoder collection remains separate. |
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
[`notes/gaussian-fixed-minimax.md`](notes/gaussian-fixed-minimax.md).
The final optimized theorem is in
[`Analog/GaussianOptimizedMinimax.lean`](Analog/GaussianOptimizedMinimax.lean).
This inventory is the current scope record. No missing conclusion is inserted
as an axiom.
