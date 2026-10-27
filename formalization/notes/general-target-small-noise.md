# General-target small-noise achievability

`Analog/GeneralTargetSmallNoise.lean` removes the earlier restriction to targets
of the form m₂−ψ(m₁). The target F is an arbitrary real-valued function on the
moment plane. The theorem uses an invertible real-linear affine channel and
an exact globally Lipschitz decoder.

At every interior moment, exactness determines the decoder's local germ as
F composed with the inverse affine channel. `exact_decoder_eventuallyEq` and
`exact_decoder_hasFDerivAt` prove this fact and derive the decoder derivative
from the target derivative. Decoder differentiability is not an input premise.

`general_target_leading_mse` applies the checked dominated-convergence theorem
to general square-integrable noise, even when the noise and moment variables
are coupled. Its derivative field need not be separately assumed measurable.

`gaussian_clm_second_moment` evaluates the actual constructed standard circular
Gaussian law for every real continuous linear functional L:

    ∫ (L z)² dCN(0,1) = ((L 1)² + (L i)²)/2.

It uses the previously proved Gaussian coordinate/cross moments and derives
all needed square and product integrability.

The main Gaussian specialization is
`gaussian_general_target_leading_mse`. For a probability source law, measurable
moments almost surely in the interior, and almost-sure target derivatives J,
it proves the normalized actual MSE limit

    (1/2) ∫ [(Jω(T⁻¹1))² + (Jω(T⁻¹i))²] dμ.

Here T includes the full channel scaling (K times the common encoder matrix).
This is the inverse-channel directional-energy form of the current general
leading-MSE coefficient. The proof derives product-measure integrability of
the directional derivative square from decoder Lipschitzness and the finite
Gaussian second moment, then applies Fubini and the exact Gaussian covariance
identity. It assumes neither integrability nor measurability of J as an
independent hypothesis.

This establishes arbitrary-target **achievability** for the current regular
interior moment laws, and in fact for any interior-supported source law with
the stated derivative assumptions. It is not a van Trees lower bound, an
arbitrary-estimator Bayes converse, or a worst-case minimax optimization result.

Validation: the whole module compiles with the pinned Lean 4.24.0/mathlib
revision without warnings. The project-level report records aggregate audit
status.
