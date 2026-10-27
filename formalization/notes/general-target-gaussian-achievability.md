# Constructed two-statistic Gaussian achievability

`Analog/GeneralTargetGaussianAchievability.lean` constructs the manuscript's
noise-power-independent decoder from each readout's value and derivative on
its closed attainable coordinate interval. `IntervalReadout` assumes only
continuity of both on the interval and the derivative identity on its open
interior. The construction integrates the endpoint-clamped derivative.

The resulting inverse-affine-channel decoder is globally C¹ and Lipschitz,
with globally bounded, uniformly continuous derivative. Exactness and the
prescribed derivative hold on the closed rectangle, including its boundary.
These facts are proved, not additional assumptions.

`worst_case_limit` proves convergence of the actual supremum of normalized
Gaussian MSE over every nonempty compact attainable moment set in that
rectangle. It identifies an attained maximal coefficient, equal to one half
the sum of the two squared inverse-channel directional derivatives.
`prior_limit` proves the corresponding actual prior-averaged Gaussian risk
limit under any probability law and measurable supported moment map; it needs
neither an interior-only prior nor a separate derivative-integrability premise.

The received linear equivalence `T` includes the manuscript's scale `K`; its
translation `c` includes the total encoder offset. The root-owned
`GaussianGramCoefficient` identifies the directional coefficient with the
inverse-Gram expression. The statistical converse against arbitrary Borel
estimators is supplied separately by `GaussianBayesConverse` and the law bridge.
