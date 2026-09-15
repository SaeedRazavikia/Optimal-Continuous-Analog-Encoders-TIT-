# Principal manuscript-to-Lean correspondence

The table identifies exact checked statements. `COVERAGE.md` separately lists
all manuscript results, their current source locations, hypotheses, and remaining gaps. The unified extension is mapped separately in `EXTENSION_SCOPE.md`; its complete continuous-encoder theorem remains unverified. The main text now combines exact structure and optimal design in one section; supporting lemmas and the score proposition appear in the proof appendices. Result labels provide stable identifiers across renumbering.

| Manuscript component | Lean declaration | Scope |
|---|---|---|
| General triple collision, `lem:collision` | `Analog.GeneralCollision.triple_collision_preserves_moments` | Full statement, with weaker readout regularity and endpoint inputs allowed. |
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

