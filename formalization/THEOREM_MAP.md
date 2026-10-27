# Paper-to-Lean correspondence

The [statement and proof guide](../docs/STATEMENTS.md) is the reader-facing
entry point for [arXiv:2610.21536v1](https://arxiv.org/abs/2610.21536v1).

[`COVERAGE.md`](COVERAGE.md) records the scope of all ten current manuscript
targets. This map names the strongest relevant declarations and the bridges
used by the newly completed proofs. Every namespace starts with `Analog.`.
A source link identifies the file; the declaration name identifies the exact
theorem to inspect.

## The ten manuscript targets

| Target | Principal declarations | Exact scope |
|---|---|---|
| `thm:rigidity` | [`HeterogeneousFullRigidity.heterogeneous_rigidity`](Analog/HeterogeneousFullRigidity.lean) | Original closed-source/closed-mean assumptions; exact computation iff common nonsingular feature columns and individual offsets. Both directions and source endpoints are included. |
| `thm:sdp` | [`HeterogeneousAttainment.heterogeneous_sdp_attained`](Analog/HeterogeneousAttainment.lean); `optimal_positive_iff_euclidean_lipschitz`; [`HeterogeneousGlobalOptimum.unrestricted_sdp_attained`](Analog/HeterogeneousGlobalOptimum.lean) | Attainment and no relaxation gap in the actual heterogeneous program, including dependent features and zero/singular optima; positivity iff Euclidean Lipschitz continuity; unrestricted continuous-encoder optimum under rigidity assumptions. |
| `prop:amplification` | [`Decoder.sharp_uniform_decoder`](Analog/Amplification.lean); `zero_score_no_finite_uniform_decoder` | Sharp attained finite constant for positive actual score, and impossibility of any finite constant at zero score, for arbitrary input and received maps. |
| `thm:decoder` | [`Decoder.pairwise_exists_lipschitz`](Analog/Decoder.lean); `sharp_uniform_decoder`; `clip_uniform` | Exact global Lipschitz extension and sharp uniform bound. The displayed compact-moment minimum formula is not yet identified in a named current-model theorem. |
| `prop:radius-minimax` | [`RadiusMinimax.borel_radius_minimax`](Analog/RadiusMinimax.lean) | Actual maximizing pair, Borel midpoint decoder, and optimal half-modulus error for compact continuous-input models, including radius zero. |
| `thm:identifiable-minimax` | [`GaussianFixedMinimax.fixed_encoder_minimax`](Analog/GaussianFixedMinimax.lean); [`GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved`](Analog/GaussianOptimizedMinimax.lean) | Full fixed-encoder and optimized all-Borel minimax limits, actual finite-node attainable domain, attained coefficient minimum, and a single noise-independent optimal encoder/decoder. Changing designs and singular limiting channels are handled by proved converses. |
| `prop:general-small-noise` | [`FixedPriorGaussianLimit.fixed_prior_limit_inverse_trace`](Analog/FixedPriorGaussianLimit.lean); `exact_decoder_prior_limit` | Genuine all-Borel-decoder risk infimum has the full one-sided Gaussian limit. The coefficient is the actual inverse-Gram trace; every fixed Lipschitz exact decoder has the same leading average risk on an interior-supported prior. |
| `prop:score` | [`GeneralScore.general_operational_score`](Analog/GeneralScore.lean); `general_score_small_distance_sharpness` | Endpoint-dual score formula and actual shrinking pairs for the shared-feature source model. A direct current `Fin K`/arbitrary-offset wrapper remains separate. |
| `thm:parabola` | [`quadratic_optimal_all_power`](Analog/PowerScaling.lean); [`GeneralQuadratic.optimalParameter_manuscript`](Analog/GeneralQuadratic.lean); [`Quartic.quartic_optimal_all_power`](Analog/QuarticPower.lean) | All-power coefficient-Gram optimum and stated parameter/root formulas. The complete current general-readout/unrestricted-encoder wrapper is not claimed by these declarations alone. |
| `thm:certifiedgrid` | [`HeterogeneousGrid.certified_discretization`](Analog/HeterogeneousGrid.lean); `scaling_gap_isBigO`; [`HeterogeneousGlobalOptimum.grid_maximum_global_bound`](Analog/HeterogeneousGlobalOptimum.lean) | Actual node grids, all secants, sampled/continuum maxima, sharp C² remainder, feasible scaling, objective bracket, uniform quadratic loss, operational synthesis, and unrestricted-encoder interpretation under rigidity. |

## Rigidity dependency chain

| Step | Declaration | What is derived |
|---|---|---|
| Continuous rectangular functional equation | [`LocalPexider.rectangle_affine_of_continuousOn`](Analog/LocalPexider.lean) | Common affine slope from a continuous Pexider identity, including endpoints; no differentiability premise. |
| Two-completion separation | [`CompletionSeparation.dense_open_separation_of_receiver_alternatives`](Analog/CompletionSeparation.lean) | Dense open nonzero completion-gradient determinants from the actual affine/nowhere-affine receiver alternatives and independent feature coordinates. |
| Actual finite-node recovery | [`HeterogeneousCompletion.identifying_collision_neighborhood`](Analog/HeterogeneousCompletion.lean) | Exact scalar computation yields local recovery of both partial moment sums from physical completion readouts; all fixed-node contributions and `1/K` factors are retained. |
| Actual moment-domain density | [`HeterogeneousCompletionDensity.dense_identification`](Analog/HeterogeneousCompletionDensity.lean) | Density at every regular triple from attained per-node image extrema, strict interior ranges, true receiver domains, and the readout inverse-function theorem. |
| Planar topology | [`PlanarBrouwer.brouwer_fixed_point_planeClosedUnitBall`](Analog/PlanarBrouwer.lean); [`PlanarInvariance.isOpen_image`](Analog/PlanarInvariance.lean) | Ordinary planar Brouwer and invariance of domain are proved. The intermediate fixed-point typeclass is instantiated by a theorem, not an extra axiom. |
| Local charts and automatic regularity | [`HeterogeneousLocalCharts.heterogeneous_local_chart`](Analog/HeterogeneousLocalCharts.lean); [`HeterogeneousRegularity.contDiffAt_of_dense_triple_factorizations`](Analog/HeterogeneousRegularity.lean) | Actual source-coordinate charts and C¹ encoders from continuous encoders and exact moment recovery, using local averaging. |
| Derived tangent anchors and endpoint integration | [`HeterogeneousSeparation.affine_of_independence_and_triple_determinants`](Analog/HeterogeneousSeparation.lean); [`HeterogeneousAnalyticRigidity.planar_affine_of_dense_charts`](Analog/HeterogeneousAnalyticRigidity.lean) | Independent cross-node anchors, common derivative coefficients, and separate offsets on the full closed source interval. |
| Nonsingular common columns | [`HeterogeneousFullRigidity.nonsingular_affine_of_exact`](Analog/HeterogeneousFullRigidity.lean) | Local moment recovery excludes a singular common coefficient map. All chart, density, regularity, and anchor premises have been discharged. |

## Operational design and certification bridges

| Component | Declaration | Exact scope |
|---|---|---|
| Actual aggregate and distance | [`HeterogeneousScore.received_encoder_mean`](Analog/HeterogeneousScore.lean); `received_squaredDistance` | Sum of node offsets plus `K` times the common-column moment map; actual received squared distance equals `K²` times the Gram quadratic form. |
| Attained-pair score | [`HeterogeneousScore.affine_operational_score`](Analog/HeterogeneousScore.lean); `affine_score_bound_iff` | Exact input-pair/attained-moment-pair equivalence, including singular columns and the actual nonconvex attainable set. |
| All-rank reconstruction | [`SingularGram.reconstructPSD_gram`](Analog/SingularGram.lean); `reconstructPSD_energy_le`; `reconstructPSD_common_columns` | Every PSD block has a planar reconstruction preserving the common lower Gram block and both cross entries, while not increasing continuum peak power. Singular and zero blocks are allowed. |
| Physical feasible synthesis | [`HeterogeneousSynthesis.feasible_operational_synthesis`](Analog/HeterogeneousSynthesis.lean) | Actual continuous node encoders, all continuum peak bounds, and score at least `K²λ`; exact computation when `λ>0`. |
| Compactness with dependent features | [`HeterogeneousAttainment.coefficient_maximum_attained`](Analog/HeterogeneousAttainment.lean); `heterogeneous_operational_maximum_attained` | Compactness is proved in the finite-dimensional space of actual encoder functions, so no injective coefficient parameterization or feature independence is required. |
| Positive score to unrestricted optimality | [`HeterogeneousScore.positive_score_implies_exact`](Analog/HeterogeneousScore.lean); [`HeterogeneousGlobalOptimum.unrestricted_sdp_attained`](Analog/HeterogeneousGlobalOptimum.lean) | Positive-score competitors fall under proved rigidity; zero-score competitors are also bounded. No exactness hypothesis is imposed on arbitrary competing encoders. |
| Grid optimizer attainment | [`HeterogeneousGridFeasible.maximum_attained`](Analog/HeterogeneousGridFeasible.lean) | Actual common-block sampled or continuum program with all moment secants; bounds and compactness derived from the fixed spanning grid samples. |
| Spectral interpolation and scaling | [`HeterogeneousGrid.c2_grid_certificate`](Analog/HeterogeneousGrid.lean); `certified_discretization` | Per-node C² feature maxima, maximum spectral remainder over nodes, sharp `1/8` interpolation factor, and common scaling preserving every secant. |
| Uniform discretization loss | [`HeterogeneousGrid.scaling_gap_isBigO`](Analog/HeterogeneousGrid.lean) | `O(h²)` from fixed spanning anchors and one unequal-target pair; no assumed uniform optimizer bound. |
| Full matrix dual witness | [`HeterogeneousDualCertificate.current_program_dual_upper_bound`](Analog/HeterogeneousDualCertificate.lean) | Actual PSD matrices, node weights, finite attained secants, and the common-block identity imply the program upper bound. Matrix trace inequalities are derived. |
| Certified scalar gaps | [`FiniteCertificates.absolute_gap_bound`](Analog/FiniteCertificates.lean); `relative_loss_bound` | Absolute and relative loss from certified primal/dual inequalities; the relative bound requires a positive lower certificate. |

## Gaussian proof components

| Component | Declaration | Exact scope |
|---|---|---|
| Actual Gaussian likelihood | [`GaussianScoreIdentity`](Analog/GaussianScoreIdentity.lean) | Product Gaussian likelihood, normalized density laws, and compact-flux integration by parts without differentiating the decoder. |
| Likelihood/additive-noise agreement | [`GaussianLawBridge`](Analog/GaussianLawBridge.lean) | Equality of the physical independent additive complex-Gaussian law and the likelihood law, including the real-coordinate variance/total-noise conversion. |
| Arbitrary-decoder converse | [`GaussianBayesConverse.regular_prior_bayes_converse_total_noise`](Analog/GaussianBayesConverse.lean) | Lower asymptotic for the genuine infimum over Borel decoders under a regular prior; derived score inequality and variational approximation. |
| Two-readout achievability | [`GeneralTargetGaussianAchievability.prior_limit`](Analog/GeneralTargetGaussianAchievability.lean); `worst_case_limit` | Constructed noise-independent endpoint-extension decoder; actual prior and compact-set worst-case Gaussian asymptotics for both receiver postprocessings. |
| Full fixed-prior equality | [`FixedPriorGaussianLimit.fixed_prior_limit`](Analog/FixedPriorGaussianLimit.lean); `fixed_prior_limit_inverse_trace` | Full one-sided limit at zero total noise, matching upper and lower bounds, original target, arbitrary Borel decoders, and actual matrix-inverse trace coefficient. |
| Exact Lipschitz decoder coefficient | [`FixedPriorGaussianLimit.exact_decoder_prior_limit`](Analog/FixedPriorGaussianLimit.lean) | Any fixed globally Lipschitz exact decoder has the same leading prior-averaged coefficient; local derivatives follow from exactness on the interior. |
| Full fixed-encoder minimax equality | [`GaussianFixedMinimax.fixed_encoder_minimax`](Analog/GaussianFixedMinimax.lean) | Attained prescribed coefficient maximum, full one-sided limit of genuine all-Borel minimax risk, and the matching worst-case limit of one fixed Borel decoder, whose finite risk is proved. |
| Moving designs and singular exclusion | [`GaussianMinimaxConverse.moving_minimax_converse`](Analog/GaussianMinimaxConverse.lean); `singular_minimax_diverges_of_spanning` | Actual worst-case lower asymptotics along changing Gram matrices; lost directions and spanning gradients force divergence, with local priors and smooth detecting tests constructed. |
| Actual local probability priors | [`LocalBallPrior.exists_regular_prior_above`](Analog/LocalBallPrior.lean); `exists_ball_prior_close` | Normalized ball densities have mass one, positivity and C¹ regularity on their open full-mass region, and expectations approximating any continuous coefficient at the center. |
| Attained coefficient design | [`GaussianDesignAttainment.inverse_gram_design_minimum`](Analog/GaussianDesignAttainment.lean) | Both the maximum over moments and the minimum over nonsingular peak-feasible parameters are attained. Compactness and finite-epigraph nonsingularity are derived. |
| Physical channel and normalization | [`GaussianParameterChannel`](Analog/GaussianParameterChannel.lean); [`GaussianOptimizedMinimax.optimizedRisk_eq_infimum_div`](Analog/GaussianOptimizedMinimax.lean) | The channel equals `K U` with the actual sum of node offsets. The exact inverse-Gram coefficient has factor `1/(2K²)`, and positive-noise normalization commutes with the actual outer risk infimum. |
| Full noise-dependent design optimization | [`GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved`](Analog/GaussianOptimizedMinimax.lean) | The actual outer risk infimum divided by total complex noise converges to the attained minimum. A fixed peak-feasible nonsingular parameter and its fixed explicit decoder attain the same limit; neither depends on the noise level. Actual moment compactness/nonemptiness are derived from the source features. |

## Retained specialized developments

Earlier shared-curve score identities, explicit strip decoders, variance
operational optima, quartic certificates, Gram frontiers, criterion transfer,
and conditional approximate stability remain in the build. Their precise
statements remain useful, but do not automatically supply an unassembled
current-model wrapper. The earlier specialized map is available in
[Git history](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/blob/54d1083238b5e3e9a009138c3bb69c09d37f58e9/formalization/historical/v0.2.0/THEOREM_MAP.md).

The terminal declarations above cover the core rigidity, design, Gaussian,
and certification developments. The separate current representation/example wrappers still outside
the named theorem assembly are identified in `COVERAGE.md`.
