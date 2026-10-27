# Proposition 3: the displayed minimum decoder

`Analog/MinimumDecoderGaussianLimit.lean` closes the decoder representation
issue in `prop:general-small-noise`. The statistical converse remains the
previously verified `FixedPriorGaussianLimit.fixed_prior_limit_inverse_trace`.
The new proof identifies the particular attained minimum in Theorem 3 and
applies the proved exact-decoder Gaussian asymptotics to that same function.

The terminal declaration is
`Analog.MinimumDecoderGaussianLimit.heterogeneous_fixed_prior_minimum`.
It proves both the all-Borel-decoder optimal-risk limit and the risk limit of
the minimum-formula decoder for the actual finite-node moment image. Its
coefficient is the prior average of the inverse-Gram quadratic form divided
by `2 K²`. The true channel is `K U`; its offset is the sum of all node offsets.
`fixed_prior_minimum_inverse_trace` states the same conclusion directly as a
matrix inverse trace for that true channel.

The essential bridges are:

- `moment_score_positive`: nonsingularity and the constructed Lipschitz exact
  extension imply positive moment score for a nonconstant target.
- `minimumDecoder_regular`: the minimum formula is globally Lipschitz with
  the sharp score constant and is exact at every attainable moment.
- `minimum_decoder_prior_limit`: exactness on the interior determines the
  local derivative, so the minimum decoder has the required average Gaussian
  coefficient for every interior-supported probability law.
- `parameter_coefficient`: explicit conversion from the true channel to the
  physical `1/(2 K²)` coefficient.
- `minimumDecoder_eq_paper_decoder`: pointwise equality with
  `CompactMinimumDecoder.momentDecoder`, the function used for Theorem 3.
  Its proof reindexes the very same minimum, including equality of the
  defining quotient sets and sharp constants.

The physical theorem derives compactness and nonemptiness from continuity of
the node features. Its remaining assumptions are the original nonsingular
coefficient encoder, nonconstant prescribed target, the target's closed
coordinate intervals, and a positive C¹ prior density on an open full-mass
subset of the actual attainable interior. It does not replace the moment
set by its convex hull, assume differentiability of the minimum decoder,
or allow the decoder to depend on the prior or noise level.
