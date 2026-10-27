# Uniform Gaussian achievability

`Analog/UniformSmallNoise.lean` proves the uniform step required by the current
fixed-encoder worst-case upper bound. It works on the actual complex observation
plane and uses the constructed circular Gaussian law.

The inputs are a differentiable fixed decoder F with its actual real Fréchet
derivative field J, a global derivative-norm bound, and uniform continuity of
J. These are the properties obtained by the manuscript's C¹ endpoint extension
and inverse affine channel. The theorem does not assume a Taylor remainder
estimate, a uniform risk expansion, or bounded optimizer sequences.

The proof chain is explicit:

1. `uniform_taylor_bound` derives a uniform first-order remainder estimate
   from derivative uniform continuity using the convex mean-value theorem.
2. `lipschitz_of_derivative_bound` derives the global Lipschitz bound.
3. `tail_integral_tendsto` proves that the noise-only second-moment tail
   vanishes by dominated convergence under the actual Gaussian law.
4. `normalized_error_difference_bound` and `risk_difference_bound` bound the
   difference between normalized actual risk and derivative energy uniformly
   over **all** noiseless observations. No supremum is placed inside a
   potentially nonmeasurable integrand.
5. `risk_tendstoUniformly` proves actual uniform convergence to
   ((J(x)1)²+(J(x)i)²)/2.
6. `worst_case_amplitude_limit` derives an attained maximizing coefficient
   on any nonempty compact noiseless set and squeezes the actual supremum
   of normalized Gaussian risks.
7. `worst_case_power_limit` converts to noise power N using perturbation √N z
   and normalization by N.

The main theorem is:

```
Analog.UniformSmallNoise.worst_case_power_limit
```

It exhibits x⋆ in the compact set maximizing derivative energy and proves

```
sSup ((powerRisk F N) '' M) → energy J x⋆  as N ↓ 0.
```

`powerRisk F N x` is exactly the integral of the squared error
(F(x+√N z)−F(x))² under CN(0,1), divided by N. The Gaussian factor 1/2 is
proved from the actual law in `GeneralTargetSmallNoise`, not assumed as a
covariance premise.

For the manuscript application, F here denotes the fixed global decoder
obtained after the invertible affine channel, and M denotes the compact
noiseless received set. The derivative energy is then the inverse-Gram
coefficient, including the K² normalization carried by the affine channel.
The endpoint-extension and coordinate-transformation interfaces are separate
from this uniform analytic theorem.

This completes the uniform upper-achievability argument under its derived
extension properties. It is not a lower bound against arbitrary Borel
estimators and does not prove minimax equality by itself.

Validation: module compilation and the `--trust=0` check use the pinned
Lean 4.24.0/mathlib revision. The final aggregate status is recorded separately
in `verification/report.json`.
