# Local prior regularity and compact test fluxes

`Analog/RegularPriorFlux.lean` supplies the localization step used by the
Gaussian score argument under the manuscript's regular-prior assumptions.
It works on `Plane = ℝ × ℝ` and requires only:

- an open set Ω;
- `ContDiffOn ℝ 1 p Ω` for the prior density p;
- `0 < p(m)` on Ω when a quotient by p is involved;
- a globally C¹ test function η with compact support inside Ω.

It places no regularity or positivity assumption on p outside Ω.
`flux_contDiff` proves that a=pη is globally C¹ because it is locally zero
off the test support. `flux_hasCompactSupport` and
`flux_derivative_support_subset` show that neither multiplication nor
first directional differentiation enlarges that support.

`flux_energy_regular` proves continuity, compact support, and Lebesgue
integrability of a²/p. `flux_information_regular` proves the same for
(Da[z])²/p for any fixed direction z. All quotients use total real division;
their numerators vanish outside the regular region. Consequently no finite
global prior Fisher-information assumption is introduced.

`flux_zero_of_prior_zero` proves a=0 and Da[z]=0 wherever p=0. This supports
cancellation of the likelihood/prior density in the joint-measure score
identity. `vector_flux_information_regular` handles the squared sum of two
directional flux derivatives. `vector_flux_energy_regular` handles the full
two-component flux acted on by any two continuous linear mean coordinates,
including singular mean maps. Both yield continuous compactly supported
integrable quotients from the original local-prior hypotheses. `localized_division` exposes the general continuous-supported
quotient principle for assembling sums of test-field components.

The module compiles without warnings under the pinned Lean/mathlib setup.
It proves these localization and integrability facts; the Gaussian joint-law,
weighted score, and asymptotic converse assembly live in separate modules.
