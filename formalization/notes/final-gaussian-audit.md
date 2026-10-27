# Independent final Gaussian audit

Date: 2026-10-27. Result: passed. This was a read-only review of the final
statements, definitions, and assembly proofs against the supplied source
statement snapshot, in particular
`prop:general-small-noise` and `thm:identifiable-minimax`. No proof-source changes
were made during this audit. The corresponding paper is
[arXiv:2610.21536v1](https://arxiv.org/abs/2610.21536v1).

## Final statements checked

- `FixedPriorGaussianLimit.fixed_prior_limit_inverse_trace` gives the full
  one-sided optimal Bayes-risk limit in inverse-Gram trace form.
- `FixedPriorGaussianLimit.exact_decoder_prior_limit` proves that every fixed
  globally Lipschitz decoder exact on the attainable set achieves the prescribed
  coefficient for an interior-supported prior. Decoder differentiability is
  derived from exactness. The already constructed optimal Lipschitz decoder
  supplies this interface.
- `GaussianFixedMinimax.fixed_encoder_minimax` gives the fixed-encoder
  all-Borel minimax limit, an attained maximum coefficient, and one explicit
  noise-independent Borel decoder attaining that coefficient.
- `GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved` uses the
  actual finite-node attainable moment image. It supplies an attained
  peak-feasible identifiable parameter, its global coefficient minimality,
  the full one-sided limit of the raw risk infimum divided by total noise
  power, and the achieving limit of the same fixed parameter's explicit decoder.

## Hypothesis correspondence

`IntervalReadout` records continuous receiver values and slopes on the closed
interval and the derivative equation in its interior. This is the manuscript's
closed-interval C1 data; it does not impose C2 regularity. The global C1 extension
and its bounded derivative are proved, rather than assumed in the final results.

The Bayes result assumes a measurable nonnegative normalized integrable density,
C1 and strictly positive on an open set of full prior mass. No global Fisher
regularity, boundary decay, or finite prior Fisher information is required.
The rectangle support condition is explicit. The theorem allows more priors
than the manuscript by not requiring the open full-mass set to be contained in
the attainable interior; that containment is used for the exact-decoder result.

The optimized result derives compactness and nonemptiness of the actual moment
image from continuous source features. It derives compactness of peak-feasible
coefficient parameters from per-node independence. The nonempty identifiable
class is witnessed by a sufficiently small identity channel.

The assumption `attainable γ ⊆ closure (interior (attainable γ))` agrees with the
manuscript's equality: the reverse inclusion follows because this image is
compact, hence closed. `GradientSpans` is imposed on the whole attainable set;
the manuscript's spanning assumption on the interior implies it directly.
Continuity and interior density then provide the required interior detecting
points. Thus this is not an added stronger spanning assumption.

The explicit `hrect` input records that attainable moments lie in the prescribed
receiver rectangle. For the original mean intervals this follows from
`HeterogeneousMomentCompactness.attainable_subset_closedDomains`; it is not an
additional geometric regularity condition. The final Gaussian coefficient
optimization is over identifiable affine parameters, as in the manuscript's
class `B_P`. Under the separately proved full rigidity hypotheses, that class
also represents every continuous peak-feasible exactly computing encoder.

## Statistical semantics and normalization

`GaussianWorstCase.pointRisk` is a nonnegative squared-error integral in
`ℝ≥0∞`. `worstRisk` is its supremum over actual attainable moments, and the
decoder infimum ranges over all measurable real-valued decoders. Infinite-risk
decoders are retained. A constant decoder proves the optimum finite before
conversion to a real number; no continuity, unbiasedness, or noiseless exactness
restriction is imposed on competing decoders.

The actual received affine sum is identified with the parameter channel by
`GaussianParameterChannel.received_eq_channel`. Its linear part is `K U`, and
its offset is the sum of node offsets. The density-model variance `v` is the
variance of each real noise coordinate, so total complex noise power is `2 v`.
`parameter_inverse_energy` supplies the factor `K⁻²`. The final coefficient is
therefore exactly `(1 / (2 K²)) max wᵀ G⁻¹ w`. The fixed-prior theorem's Gram
matrix is the full channel Gram matrix; its displayed `trace/2` has the same
normalization after substituting `T = K U`.

`optimizedRisk_eq_infimum_div` proves the equality between the normalized
outer infimum and the raw outer infimum divided by positive total noise power.
The final statement uses the latter directly. Its filter is the full right-hand
neighborhood of zero, not just one selected vanishing-noise sequence.

## Converse and optimization dependencies

The moving regular-design converse constructs supported local priors and smooth
test fields. At a singular limiting design it constructs a nonzero lost
direction and derives divergence from a local detecting gradient. Neither a
statistical lower bound nor singular-limit divergence is assumed by the final
theorem. The compact outer-optimization argument proves the required uniform
lower behavior from sequential converses and compact extraction; it does not
assume a finite-noise optimizer or interchange limits and infima without proof.

Coefficient attainment is proved by compact epigraph minimization. Gradient
spanning forces the minimizer nonsingular. The upper bound uses the actual
Gaussian law and a single explicit inverse-channel endpoint-extension decoder;
its uniform expansion and the required integrability are proved.

## Kernel checks

Independent `lake env lean --trust=0` import audits were run for the final Bayes,
worst-case, parameter-channel, moving-converse, singular-converse, fixed-minimax,
and optimized-minimax results. Their transitive `#print axioms` outputs contain
only `propext`, `Classical.choice`, and `Quot.sound`. In particular this includes
`optimized_minimax_achieved`, `heterogeneous_optimized_minimax_achieved`, and
`constructed_decoder_attains`. No additional axiom or deferred proof obligation
was found. The project's complete aggregate build and declaration audit are
recorded separately by the main verification workflow.
