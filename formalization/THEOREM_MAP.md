# Principal manuscript-to-Lean correspondence

The table identifies exact checked statements. `COVERAGE.md` separately lists
all manuscript results, their current source locations, hypotheses, and remaining gaps. The unified extension is mapped separately in `EXTENSION_SCOPE.md`; its coefficient-class design and analytic reduction from dense local charts are checked, while its complete continuous-encoder theorem remains unverified. The main text now combines exact structure and optimal design in one section; supporting lemmas and the score proposition appear in the proof appendices. Result labels provide stable identifiers across renumbering.

| Manuscript component | Lean declaration | Scope |
|---|---|---|
| General triple collision, `lem:collision` | `Analog.GeneralCollision.triple_collision_preserves_moments` | Full revised statement; no differentiability assumptions, and endpoint inputs are also allowed. |
| Open-slice constancy step, `lem:topology` | `Analog.open_slice_fiber_constancy` | Explicit openness hypothesis; planar invariance of domain is not proved. |
| Derivative step, `lem:affine` | `Analog.DifferentialRigidity.kernel_annihilation_iff_affine_slopes` | Two distinct feature-slope anchors and the kernel hypothesis; see the module for the analytic extensions. |
| Closed-interval derivative integration | `Analog.DifferentialRigidity.planar_differential_rigidity` | Continuity, interior differentiability, nonaffinity and component kernel conditions; no automatic differentiability or coefficient independence. |
| Operational infimum | `Analog.Operational.le_score_iff` | Nonconstant target and nonnegative pairwise cost; no encoder parametrization. |
| Variance score specialization | `Analog.Curve.variance_operational_score` | All planar quadratic curves, including degenerate cases; actual infimum, K >= 2. |
| Shrinking pairs | `Analog.Curve.variance_score_small_distance_sharpness` | Actual admissible tuples approach the variance score at arbitrarily small received distance. |
| General quadratic coefficient design | `Analog.GeneralQuadratic.quadratic_optimal_closed_form` | All M > 0, unit power; exact closed-form parameter and all quadratic competitors. |
| General-power quadratic design | `Analog.quadratic_optimal_all_power` | All M > 0, P > 0; complete quadratic Gram optimization. |
| Operational variance optimum | `Analog.quadratic_variance_operational_optimal` | Actual score, every P > 0 and K >= 2, all planar quadratic competitors. |
| Quartic coefficient design | `Analog.Quartic.quartic_planar_optimal` | All M > 0, unit power; root existence/uniqueness, complete projection reduction and certificate. |
| General-power quartic design | `Analog.Quartic.quartic_optimal_all_power` | All M > 0 and P > 0; all planar quartic coefficient competitors. |
| Sharp amplification | `Analog.Decoder.sharp_uniform_decoder` | Positive operational score; actual attaining Lipschitz decoder and global minimality. |
| Zero-score amplification case | `Analog.Decoder.zero_score_no_finite_uniform_decoder` | No finite uniform decoder for a nonconstant target. This supplies the infinite-value case without an extended-real infimum definition. |
| Complex variance channel | `Analog.ArbitraryEncoder.sharp_variance_decoder` | Exact Euclidean metric bridge and all complex additive disturbances, K >= 2. |
| Explicit variance decoder | `Analog.Curve.explicitVarianceDecoder_optimal` | Actual received inverse and strip formula; global Lipschitz continuity, all-input/all-noise bound and minimality; nondegenerate quadratic curve, K >= 2. |
| Correlated strip projection | `Analog.Strip.project_unique_minimizer` | Explicit corrected clipping is the unique metric-strip projection. |
| Strip nonexpansiveness | `Analog.Strip.project_squared_nonexpansive` | All real input pairs and every positive-definite 2x2 Gram metric. |
| Variance strip readout | `Analog.Strip.projected_variance_error` | Endpoint dual-form error bound against every true strip point. |
| Output clipping | `Analog.Decoder.clip_uniform` | Preserves the original uniform constant when the interval contains every target value. |
| Implementation mismatch | `Analog.Decoder.decoded_implementation_error` | Coherent encoder and gain perturbations plus arbitrary additive noise. |
| Peak-safe quantization | `Analog.Decoder.peak_safe_quantization` | Contraction plus a bounded quantizer error; does not prove scalar B-bit spacing or phase-error formulas. |
| Schur complement | `Analog.GramSynthesis.psd3_iff_schur` | Genuine positivity of the full quadratic form, with a positive-definite feature block. |
| Rank-one score constraints | `Analog.GramSynthesis.rank_one_psd_iff` | Exact reciprocal dual-form characterization. |
| Planar synthesis | `Analog.GramSynthesis.positive_sdp_synthesis` | Constructive direction at every positive feasible SDP point; preserves the full continuum peak bound and score constraints. |
| General operational score | `Analog.GeneralScore.general_operational_score` | Full general nondegenerate affine-feature statement; actual finite-input infimum, K>=2, one-sided endpoint derivatives. |
| General shrinking pairs | `Analog.GeneralScore.general_score_small_distance_sharpness` | Actual admissible unequal-target pairs for every positive radius and tolerance. |
| Actual moment paths | `Analog.MomentPaths.exists_source_path_at_mean` | Two moving transmitter inputs realize any first-order moment direction at every interior empirical mean. |
| Local moment geometry | `Analog.RigidityCompletion.tripleMomentInterior_of_nonaffine` | Actual open moment neighborhoods under original continuous/interior-C1/nonaffine feature hypotheses. |
| Affine-family exactness | `Analog.RigidityCompletion.FeatureEncoder.exact_iff_det_ne_zero_of_nonaffine` | Complete exactness equivalence and coefficient independence within the affine-feature family. |
| Rigidity from local fibers | `Analog.RigidityAnalysis.rigid_representation_of_local_fibers` | Actual exact continuous encoder; retains interior differentiability and local moment-fiber constancy, derives the independent closed-interval representation. |
| General operational design | `Analog.GeneralDesign.positive_sdp_operational_synthesis` | Constructed continuous exact peak-feasible encoder with actual score≥K²λ; positive feasible SDP point, general feature/readout assumptions. |
| SDP compactness | `Analog.SynthesisAttainment.feasible_isCompact` | Actual seven-coordinate continuum feasible set, with explicit spanning feature anchors; compactness is derived. |
| SDP maximum | `Analog.SynthesisAttainment.maximum_attained` | Maximum of the actual separation coordinate under continuum constraints; optimizer existence is proved. |
| Small-noise limit | `Analog.SmallNoise.leading_mse_power_exact` | Actual integrated MSE/noise-power limit from Lipschitz decoding, finite noise second moment, exactness and a.s. derivative. |
| Variance small-noise limit | `Analog.SmallNoise.variance_leading_mse` | The specified complex variance decoder; derives its differentiability at interior recovered means. |
| Independent isotropic noise | `Analog.SmallNoise.isotropic_directional_second_moment` | Product-measure independence and explicit coordinate covariance hypotheses; verifies the one-half factor. |
| Inverse-risk geometry | `Analog.Frontier.risk_strict_convex` | Actual inverse-Gram risk, with positive variance parameter. |
| Gram infimum frontier | `Analog.Frontier.value_convex`, `Analog.Frontier.value_monotone` | Actual infimum over continuum-feasible Gram designs; nonempty feasible sets stated explicitly. |
| Qualitative frontier | `Analog.Frontier.plateau_exact`, `Analog.Frontier.optimal_actual_floor_eq`, `Analog.Frontier.value_strict_after_plateau` | Precise plateau/activity/increase statements; explicit optimizer witnesses where needed. |
| Positive SDP attainment | `Analog.SynthesisAttainment.positive_maximum_attained_of_strict_shape` | Original continuous/strict feature hypotheses and P>0; no anchor, compactness, or optimizer premise. |
| Operational maximum | `Analog.SynthesisAttainment.operational_maximum_attained` | Actual finite-input score maximum over ALL six-coefficient affine-feature curves, including singular and constant competitors; continuous exact attainer. |
| Attained frontier | `Analog.FrontierAttainment.frontier_attained_on_maximal_interval` | Actual risk minimum at every floor in the full feasible interval, including zero; anchors and compactness derived. |
| Unique attained Gram | `Analog.FrontierAttainment.minimum_unique_gram_of_strict_shape` | Existence and uniqueness of minimizing Gram matrix from strict feature shape and a feasible reference. |
| Compact-range recovery | `Analog.PlanarTopology.continuous_recovery_of_compact`, `continuous_triple_moment_recovery` | Derives continuous recovery on the actual compact received range from collision preservation; does not reverse the fibers. |
| Source-curve embedding | `Analog.PlanarTopology.exact_encoder_injOn`, `exact_encoder_closedEmbedding` | Injectivity and closed embedding follow from actual exactness under the original K≥4 assumptions; this is not planar invariance of domain. |
| General two-statistic geometry | `Analog.GeneralRigidity.independent_tangents`, `pairStatistic_local_section`, `regularTripleImage_nonempty` | Independent tangent anchors, actual inverse-function sections and a nonempty regular triple-statistic image follow from the stated statistic regularity and functional independence. |
| Automatic encoder regularity | `Analog.EncoderRegularity.contDiffAt_of_triple_factorization`, `planar_affine_of_local_charts` | Continuous local source-box factorizations imply automatic C¹ regularity and endpoint-inclusive affine representation, using a local Tietze extension and normalized convolution; encoder differentiability is not assumed. |
| Dense-chart rigidity reduction | `Analog.EncoderRegularity.planar_affine_of_dense_charts` | Uses `DensePlanarCharts` only above O and the actual regular triple image contained in closure O; derives smoothness and dense propagation. Producing these charts from exactness and common-completion identification remains unverified. |
| General sharp strip decoder | `Analog.GeneralDecoder.decode_optimal`, `decode_exact`, `decode_uniform` | Actual implemented decoder for the general moment family; exactness, global Lipschitz bound and minimal all-input/all-complex-noise amplification. Endpoint slopes are within-interval derivatives, with no differentiability outside I. |
| General leading MSE | `Analog.GeneralSmallNoise.source_leading_mse_inverseGram` | Actual admissible source lists, derived inverse-channel differentiation and bounded measurable slope moments, and independent isotropic noise give the inverse-Gram risk divided by 2K². |
| Actual Gaussian specialization | `Analog.GaussianNoise.gaussian_source_leading_mse` | Constructs circular complex Gaussian noise from two independent real Gaussian laws of variance 1/2 and derives its moments; no covariance or noise-integrability premise remains. |
| Output-clipped leading MSE | `Analog.GeneralSmallNoise.clipped_leading_mse_inverseGram`, `Analog.GaussianNoise.gaussian_clipped_leading_mse` | Preserves the general trace formula when the true output is strictly inside the clipping interval almost surely; no uniform distance from the endpoints is required. |
| Closed-interval frontier continuity | `Analog.FrontierContinuity.attained_continuous_frontier_of_strict_shape`, `mseValue_continuousOn` | Continuity and attainment for the full feasible Gram-floor interval, including both endpoints; anchors and optimizer witnesses are derived from strict feature shape, positive power and positive prior variance. |
| Enclosing-ellipse equivalence | `Analog.InverseSynthesis.positive_of_feasible`, `feasible_iff_ellipse`, `ellipse_to_gram`, `gram_to_ellipse`, `roundtrip_gram`, `endpoint_cost_preserved` | Derives positive definiteness and both feasibility directions, with the actual inverse-Gram and endpoint costs preserved. |
| Attained inverse synthesis | `Analog.InverseSynthesis.inverse_optimum_attained_of_strict_shape` | Positive attained inverse optimum equals the reciprocal maximal Gram floor; the unrestricted operational interpretation still requires rigidity. |
| Quadratic constrained frontier | `Analog.QuadraticFrontier.upper_root_exists_unique`, `clippedParameter_plateau_iff`, `clipped_curve_optimal_all_power` | Unique upper root, plateau, clipped parameter and actual constrained quadratic coefficient optimum for every positive power, including maximal floor. Scalar premises 0<M_eff<M remain; source-prior specializations are separate. |
| Certified continuum grid synthesis | `Analog.CertifiedGrid.c2_grid_certificate`, `certified_grid_bracket`, `grid_maximum_attained` | Actual sampled/continuum SDP optima and scaled feasible certificate, with C² derivative data, attained norm maxima and the spectral constant 2‖H‖(Z₁²+Z₀Z₂) derived. |
| Uniform grid convergence | `Analog.CertifiedGrid.grid_scaling_gap_isBigO` | Fixed spanning anchors yield a uniform Gram-operator bound and the actual O(h²) scaling loss; numerical witness values and solver outputs remain separate evidence. |
| Criterion transfer | `Analog.CriterionTransfer.score_transfer`, `peak_constrained_moment_transfer`, `collision_score_zero` | Actual dissimilarity-score identity from the local quadratic limit and general shrinking pairs, with the received-distance range derived from peak power; the nonexact collision case is also checked. |
| General attained-pair SDP | `Analog.TwoStatisticAttainment.feasible_isCompact_of_independent`, `attained_statistic_maximum` | The actual seven-variable SDP on attained statistic pairs is compact and attains a positive maximum from statistic independence, continuity, positive power and a nonconstant Lipschitz desired function. |
| General positive-definite realization | `Analog.TwoStatisticPositivity.positive_feasible_gram`, `localIdentification_of_commonCompletion` | Common-completion identification on the actual dense regular image forces a positive-score feasible Gram block to be positive definite; definiteness is derived rather than assumed. |
| General operational optimum | `Analog.TwoStatisticPositivity.general_operational_maximum_attained`, `general_sdp_operational_attainment` | Positive attained SDP optimum, continuous exact planar realization and comparison against all two-statistic coefficient curves, including singular curves. The unrestricted continuous-encoder classification remains separate. |
| Constructed compact stability modulus | `Analog.ApproximateRigidity.exists_stability_modulus`, `pairDefect_lipschitz`, `pairDefect_le_approximation` | Constructs a nonnegative nondecreasing modulus tending to zero from compact defect sublevels; the actual pair defect is Lipschitz and controlled by approximate Lipschitz decoding. |
| Continuous-encoder stability | `Analog.ApproximateRigidity.encoderClass_isCompact`, `continuous_encoder_stability` | Derives Arzelà–Ascoli compactness from the actual peak and common-modulus constraints and constructs the proximity modulus. Only identification of every exact encoder with the chosen class remains a premise; the affine-class instance still needs unrestricted rigidity. |

The strongest checked rigidity reduction now derives automatic encoder regularity,
dense propagation and endpoint-inclusive affine representation from continuous
local charts over the identifying statistic set. The remaining step is producing
those charts from exactness and common-completion identification through planar
topology. Compact-range recovery and the conditional open-slice lemma do not
supply that step. Analytic common-completion and endpoint-localization
specializations also remain unverified. The checked decoder, synthesis, frontier,
criterion-transfer and stability components therefore do not constitute a proof
of every unrestricted continuous-encoder conclusion, or of the entire manuscript.


## Quadratic certificate

The general-M proof no longer depends on an informal reflection reduction.
The peak constraints at 0 and the average at -1,1 imply, for b >= 1,

$$
bA+(b-1)B+\|bc+v\|^2
=b(A+\|c+v\|^2)+b(b-1)\|c\|^2\le b^2.
$$

With `M^2*b*(b-1)=(2-b)^2`, the exact certificate is

$$
b(b-1)(A+M^2B)[bA+(b-1)B]-bAB
=(b-1)[bA-(2-b)B]^2.
$$

It yields the universal Gram-score bound. The candidate has the exact energy
`1-b^2*s^2*(1-s^2)`, proving the full continuum peak constraint. The stable
parameter formula and its equality to the manuscript expression are both
checked.

## Quartic certificate

The development proves the unique root in `(0,1/3)`, substitutes the explicit
coefficients into the full peak identity, and proves all three multiplier
stationarity equations. Rational tangent inequalities turn those equations
into a global two-contact converse. Reflection and projection reduce every
planar coefficient curve to this orthogonal problem; degenerate cases are
handled explicitly. Scaling then restores arbitrary positive power.

## Audit

`audit_targets.json` is the explicit declaration manifest. `Audit.lean`
requests the axiom dependencies of those declarations, and `verify.py`
checks that the audit contains exactly that manifest and no unexpected
axioms. The packaged source hashes must match `verification/report.json`.

