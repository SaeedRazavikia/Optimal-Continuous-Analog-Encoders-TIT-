# Gaussian density / additive-noise model equality

`Analog/GaussianLawBridge.lean` proves that the actual likelihood-density joint
measure in the converse equals the pushforward of the prior times an
independent standard circular complex Gaussian through the additive channel.

`jointLaw_eq_additive_pushforward` requires only a measurable nonnegative
prior weight and positive coordinate variance. The prior need not be
normalized or integrable for this measure identity. The proof derives the
conditional Gaussian laws using actual affine pushforwards of variance-1/2
coordinates, identifies their product density, and applies Tonelli to every
nonnegative measurable test function.

Public consequences transfer integrability in both directions, identify real
integrals, and identify genuine nonnegative squared risks even for arbitrary
Borel decoders of infinite risk. `additiveObservation_asComplex` gives the
exact affine complex expression `c + S m + sqrt(2v) • z`, matching the explicit
decoder's small-noise model and its total noise normalization `N₀ = 2v`.

The module has 10 public theorems. Ordinary Lean compilation and `--trust=0`
kernel checking pass without warnings, admitted proofs, new axioms, or native
decision shortcuts.
