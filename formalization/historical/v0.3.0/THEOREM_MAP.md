# Principal current manuscript-to-Lean correspondence

Use `COVERAGE.md` for the complete ten-statement inventory and remaining
obligations. This map names the strongest relevant declarations without
promoting specializations or conditional results to full manuscript theorems.
Every namespace below starts with `Analog.`.

| Current component | Declaration | Precise scope |
|---|---|---|
| Node-dependent aggregate | `HeterogeneousScore.received_encoder_mean` | Actual finite sum equals the sum of offsets plus K times the shared columns applied to the empirical moments; K>0. |
| Node-dependent Gram distance | `HeterogeneousScore.received_squaredDistance` | Actual received distance is K² times the common Gram quadratic form, including singular columns. |
| Attained-pair score | `HeterogeneousScore.affine_operational_score` | Actual nonconstant-target input quotient infimum equals K² times the actual attainable-pair quotient infimum. |
| Current SDP pair constraints | `HeterogeneousScore.affine_score_bound_iff` | Exact equivalence between operational threshold and all attained-pair inequalities; no convexification. |
| Sufficient heterogeneous exactness | `HeterogeneousScore.exact_computation_of_det` | Invertible shared columns recover every readout of both moments. |
| Positive-score exactness | `HeterogeneousScore.positive_score_implies_exact` | Arbitrary heterogeneous encoders; positive actual score and nonconstant target. |
| All-rank Gram reconstruction | `SingularGram.reconstructPSD_gram` | Every PSD three-variable form, including singular/zero lower block; preserves both cross entries and all lower-block entries, and reduces offset energy. |
| Continuum peak preservation | `SingularGram.reconstructPSD_energy_le` | Reconstruction decreases energy for every feature vector, not only samples. |
| Heterogeneous common columns | `SingularGram.reconstructPSD_common_columns` | Same lower Gram block yields identical columns despite distinct offsets. |
| Constructive current SDP synthesis | `HeterogeneousSynthesis.feasible_operational_synthesis` | Actual continuous heterogeneous encoders, continuum peak bounds and score ≥K²λ from any PSD/separation feasible point; exactness if λ>0. Singular G and λ=0 are allowed. |
| Distinct-node derivative propagation | `HeterogeneousRigidity.common_slopes_of_four_anchors` | Explicit independent anchors and triple determinant identities; neither is derived here from exact computation. |
| Endpoint-inclusive integration | `HeterogeneousRigidity.integrate_common_derivatives` | Actual node-indexed derivatives integrate to common coefficients and separate constants on the closed source interval. |
| Global amplification | `Decoder.sharp_uniform_decoder` | Arbitrary received map, nonconstant target, positive operational score; an exact continuous Lipschitz decoder attains the minimum finite constant. |
| Zero-score impossibility | `Decoder.zero_score_no_finite_uniform_decoder` | No finite uniform amplification for nonconstant target at zero score. |
| McShane existence | `Decoder.pairwise_exists_lipschitz` | Constructs a global Lipschitz exact extension from the actual pairwise bound. |
| Output clipping | `Decoder.clip_uniform` | Preserves exactness and all-noise uniform bounds when the clipping interval contains target values. |
| Fixed-radius operational minimax | `RadiusMinimax.radius_minimax` | Explicit consistency midpoint attains half the pair modulus, minimal among all decoders; bounded target and nonnegative radius. |
| Compact fixed-radius minimax | `RadiusMinimax.compact_radius_minimax` | Continuous received/target maps on a nonempty compact input space; actual maximizing pair and optimal decoder. |
| Borel radius-minimax decoder | `RadiusMinimax.borel_radius_minimax` | Full compact-input statement with a measurable explicit consistency midpoint, an attained worst pair, and a lower bound against every decoder. |
| Original-family exact score | `GeneralScore.general_operational_score` | Shared feature/readout specialization with the theorem's regularity/shape assumptions; includes actual finite-input infimum. |
| Original-family shrinking pairs | `GeneralScore.general_score_small_distance_sharpness` | Actual admissible tuples approach the endpoint score at arbitrarily small received distance. |
| Quadratic optimum | `quadratic_optimal_all_power` | All positive shape parameters and power; complete quadratic coefficient-Gram comparison. |
| Variance operational optimum | `quadratic_variance_operational_optimal` | Actual variance score over all quadratic coefficient curves. |
| Quartic optimum | `Quartic.quartic_optimal_all_power` | Exact root and certificate, continuum peak feasibility, all quartic coefficient competitors and positive power. |
| Existing Gaussian achievability | `GaussianNoise.gaussian_source_leading_mse` | Constructed circular Gaussian and earlier restricted target/decoder; not arbitrary-decoder minimax. |
| Existing clipping asymptotic | `GaussianNoise.gaussian_clipped_leading_mse` | Additional almost-sure interior output condition; not a Bayes converse. |
| Existing single-curve grid theorem | `CertifiedGrid.c2_grid_certificate` | Earlier single-feature/endpoint-LMI SDP, with derived C² spectral remainder. |
| Existing grid convergence | `CertifiedGrid.grid_scaling_gap_isBigO` | Uniform fixed-anchor bound and O(h²) scaling loss for that specialization. |
| PSD trace-product sign | `FiniteCertificates.psd_trace_product_nonnegative` | Genuine arbitrary-dimensional real PSD matrices; product need not be symmetric. |
| Finite dual arithmetic | `FiniteCertificates.finite_secant_upper_bound` | All finite nonnegative weights; the trace inequality and common-block identity remain explicit premises. |
| Continuum scaling | `FiniteCertificates.scale_all_peaks`, `scale_all_separations` | All nodes/inputs and all separation inequalities, not an omitted-constraint sampling claim. |
| Certificate gaps | `FiniteCertificates.absolute_gap_bound`, `relative_loss_bound` | Absolute and relative loss from primal/dual inequalities; positive lower certificate for relative loss. |

## Retained specialized developments

All earlier modules remain in the build and axiom audit. Shared-curve SDP
attainment, inverse synthesis, continuous Gram frontiers, quadratic constrained
frontiers, criterion transfer, and conditional approximate stability remain
useful results. The old detailed map is retained in
`historical/v0.2.0/THEOREM_MAP.md` solely as historical reference. Its manuscript
labels, source paths, and theorem coverage must not be used for current claims.

## Not established by this map

There is no completed Lean theorem for the current unrestricted heterogeneous
rigidity characterization, dependent-feature SDP attainment, optimized Gaussian
minimax equality, or arbitrary-Borel-decoder Bayes converse. The current
manuscript proof is reviewed in the notes, but a review is not kernel evidence.
