# Constructed smooth test fields and the inverse-Gram variational identity

`Analog/WeightedVariational.lean` supplies the approximation and variational
foundation used in the current Gaussian converse. It does not assume the
existence of a test-field approximation or the value of a variational optimum.

The main theorem is `inverse_gram_variational_supremum`. For an actual
invertible continuous linear encoder factor `S`, a bounded continuous gradient
field `w`, and a probability measure assigning full mass to an open set `Ω`, it
proves

$$
\sup_{\eta\in C_c^\infty(\Omega)}
\frac{\bigl(\int\langle\eta,w\rangle\,d\pi\bigr)^2}
 {\int\|S\eta\|^2\,d\pi}
=\int\|(S^{-1})^*w\|^2\,d\pi.
$$

The right-hand integrand is the inverse-Gram energy: if `G = SᵀS`, it is
`wᵀ G⁻¹ w`. The formal statement uses the inverse adjoint of an actual linear
equivalence, so it does not replace the geometry with assumed scalar moments.
The model can be any finite-dimensional real parameter space with values in a
complete real inner-product space. The prior can be any Borel probability;
its positive density and finite global Fisher information are not needed for
this variational lemma.

## Construction and verified interfaces

- `compact_cutoff_sequence` constructs compact interior cutoffs from a compact
  exhaustion of `Ω`. The cutoff is eventually one at each point of `Ω`.
- `smooth_compact_approximation` constructs uniform smooth approximants by
  convolution with a normalized compact bump. A positive thickening radius
  keeps their compact supports strictly inside `Ω`.
- `smooth_test_field_approximation` combines the cutoffs and mollifiers into
  actual smooth compact interior fields, with pointwise convergence and an
  explicit integrable error bound.
- `smooth_test_field_L2_density` proves convergence in the actual prior's
  squared-L² error for continuous square-integrable fields.
- `inner_toLp_eq_integral` and `integral_inner_square_le` prove the genuine
  integrated Cauchy--Schwarz upper bound through the Hilbert L² space.
- `smooth_test_moments` proves convergence of the two actual moment integrals
  appearing in the quotient; `smooth_variational_supremum` proves the
  unweighted supremum; invertible linear change gives the weighted theorem.
- `positive_energy_test_approaches_supremum` supplies positive-denominator
  tests approaching every positive optimum. Zero fields contribute zero in
  the set definition, but no lower bound depends on total division at zero.
- `exists_positive_scalar_test` constructs a smooth compact interior scalar
  test with strictly positive correlation from a positive scalar second
  moment. For a singular direction `v`, apply it to `h(m)=⟨v,w(m)⟩`, then use
  the vector test `η(m)=χ(m)v`.

The smooth tests are a subset of the manuscript's `C_c^1` tests. They already
attain the same variational supremum; the integrated Cauchy--Schwarz upper
bound applies to every square-integrable test. Consequently using this
smaller smooth test class loses no information in the converse.

## Use in the completed Gaussian theorems

The statement assumes a globally defined bounded continuous extension of the
gradient field. [EndpointExtension](../Analog/EndpointExtension.lean) constructs
the required one-dimensional extensions by extending the postprocessing
derivatives constantly past their endpoint intervals.
[FixedPriorGaussianLimit](../Analog/FixedPriorGaussianLimit.lean) assembles
the two-coordinate target extension and its gradient.
[GaussianGramCoefficient](../Analog/GaussianGramCoefficient.lean) identifies
the inverse-adjoint energy with the coordinate inverse-Gram expression.
These application requirements are therefore derived in the completed proofs.

The Gaussian likelihood score identity, regular-prior information integrability,
and arbitrary-decoder risk bound are supplied by the separate Gaussian
converse modules. The final statistical assembly is complete; see
[the Gaussian proof overview](completion-gaussian.md) and
[COVERAGE.md](../COVERAGE.md) for its terminal declarations and exact scope.
The project-level audit checks the formal statements and their proof dependencies.
