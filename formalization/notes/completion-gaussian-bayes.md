# Fixed-prior Gaussian Bayes converse

`Analog/GaussianBayesConverse.lean` assembles the actual likelihood-based van
Trees inequality and the constructed compact smooth-test variational theorem.
It proves a statistical lower asymptotic statement for the infimum over **all
Borel decoders**, rather than assuming an information inequality or density
of the test class.

## Main result

`regular_prior_bayes_converse` applies to a Borel density `p ≥ 0` of integral
one on the real moment plane, positive and C¹ on an open set `Ω` carrying
all prior mass. The target `f` is globally C¹ with bounded gradient and has
an almost-sure bounded range under the prior. The receiver is an invertible
real-linear map `S : ℂ ≃L[ℝ] ℂ`; its two coordinate rows and independent
Gaussian observation density are actual definitions.

For every positive variance sequence `vₙ → 0`, the theorem proves

`LowerAsymptotic (fun n => optimalRisk p f S c (v n) / v n)`

with coefficient

`∫ m, ‖S.symm.toContinuousLinearMap.adjoint (gradient f m)‖² ∂priorLaw p`.

`LowerAsymptotic risk T` means every real `a < T` eventually satisfies
`a ≤ risk n`; this avoids real-liminf conventions for unbounded sequences.
`regular_prior_bayes_converse_total_noise` supplies the manuscript's noise
normalization `N₀ = 2v` and the corresponding coefficient divided by two.

## Actual model and proof chain

- `optimalRisk` is the real value of the infimum of nonnegative Lebesgue
  squared-error risks over every measurable decoder. Clipping to the bounded
  target interval proves this infimum is finite and identifies it with the
  infimum of finite real clipped risks. Unbounded and infinite-risk decoders
  remain included correctly.
- `test_components` turns each genuine C∞ compact interior complex field into
  real C¹ component tests, with proved support properties.
- `sensitivity_eq_inner` and `channelInformation_eq_energy` prove the exact
  prior-integral numerator and receiver-energy denominator identities.
- `optimalRisk_test_bound` applies `GaussianVanTrees.regular_information_bound`
  to every clipped decoder and passes the bound to the actual infimum. Prior
  score information is finite by local positivity and compact test support,
  not by a global Fisher-information assumption.
- `test_lower_asymptotic` takes the noise limit for each fixed test.
- `regular_prior_bayes_converse` uses the proved inverse-Gram variational
  supremum from `WeightedVariational`, including its constructed smooth
  approximation, to obtain the full coefficient. It does not interchange
  a decoder infimum and a noise limit.

## Manuscript interface

The finite closed-interval readout must be connected to a global C¹ target
with bounded gradient. `EndpointExtension` constructs the scalar extension;
the target-composition bridge is separate. Identifying the inverse-adjoint
energy with the displayed matrix trace is the separate coordinate-algebra
bridge in `GaussianGramCoefficient`. This file proves the fixed-prior
converse; changing receiver sequences, singular-limit exclusion, and final
joint design/minimax optimization are handled separately.

## Validation

The module contains 11 public theorems. Ordinary Lean compilation and kernel
checking with `--trust=0` pass without warnings, admitted proofs, new axioms,
or native-decision shortcuts.
