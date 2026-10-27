# Arbitrary Borel risks and Gaussian limit deductions

`Analog/BorelRisk.lean` formalizes nonnegative squared risk with an ENNReal
Lebesgue integral. An arbitrary Borel decoder can have infinite risk, so its
real Bochner integral must not be used unconditionally. The module proves
that clipping to the bounded target interval gives L² error, decreases the
actual nonnegative risk, and preserves the infimum over Borel decoders.
It then identifies that finite extended-real optimum with the real infimum
of the clipped squared risks. No exactness or unbiasedness is assumed.

`Analog/GaussianConverseLimits.lean` proves the sequential consequences of
information inequalities: a fixed-test lower bound at a nonsingular limit,
risk divergence when the positive denominator tends to zero and the numerator
is nonzero, the passage through a variational family, and convergence of the
actual optimized risk when one fixed decoder attains the matching bound.
Positive-noise normalization commutes with the actual risk infimum by a proved
algebraic identity. No infimum/limit interchange is used.

These limit lemmas deliberately expose the information-bound and test-family
premises. By themselves they are not proofs of the manuscript's Gaussian
converse. `GaussianScoreIdentity`, `GaussianVanTrees`, and `WeightedVariational`
provide the model-level ingredients; the final coverage report identifies
which application/optimization interfaces have been assembled.

Both modules compile with the pinned Lean environment. Final aggregate kernel
and axiom status is recorded in `verification/report.json`.
