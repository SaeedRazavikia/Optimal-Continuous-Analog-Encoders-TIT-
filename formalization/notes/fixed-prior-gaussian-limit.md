# Completed fixed-prior Gaussian estimation limit

`Analog/FixedPriorGaussianLimit.lean` combines the all-Borel-decoder lower
bound with the constructed endpoint-extension upper bound in the actual
Gaussian likelihood model. The equality of the density model and independent
additive complex Gaussian model is proved in `GaussianLawBridge`, not assumed.

`fixed_prior_limit` proves the full one-sided limit of the genuine optimal
risk divided by total complex noise power. The infimum ranges over all Borel
decoders and uses nonnegative Lebesgue squared risks, including infinite-risk
decoders. The target is the original prescribed sum of readouts, not its
extension: almost-sure target equality transfers the statistical model exactly.

The prior assumptions are measurable nonnegative normalized Lebesgue density,
local C¹ regularity and positivity on an open full-mass region, and support in
the two closed readout intervals. Bounded gradients, bounded target values,
finite constructed-decoder risk, global decoder regularity, and the matching
upper coefficient are all derived. No estimator derivative or score inequality
is supplied as an extra hypothesis.

`fixed_prior_limit_inverse_trace` identifies the exact coefficient as

```
trace( E[w wᵀ] * (Tᵀ T)⁻¹ ) / 2,
w = (ψ₁′(m₁), ψ₂′(m₂)).
```

The channel `T` includes the manuscript's factor K, so this is its
`trace(W G⁻¹)/(2K²)`. The Gram identification and actual matrix inverse are
proved by `GaussianGramCoefficient`. All second-moment integrability required
for that identity is derived from the original interval slope bounds.

`exact_decoder_prior_limit` additionally proves that every fixed globally
Lipschitz decoder exact on the attainable set has this same leading
prior-averaged coefficient under an interior-supported probability law. Its
local derivative is forced by exactness; it is not assumed. This result is
stated with the independent additive Gaussian law, which `GaussianLawBridge`
identifies with the likelihood law.
