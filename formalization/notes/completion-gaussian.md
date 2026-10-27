# Gaussian converse completion work

The current Gaussian proof is based on the actual product Gaussian likelihood,
not on an assumed information inequality. The following additions have compiled
with Lean 4.24.0 and mathlib at the project's pinned revision.

- `GaussianScoreIdentity.lean` derives the likelihood derivative, compactly
  supported parameter integration by parts, Gaussian first and second moments,
  exact weighted-score covariance, and vector-field score information. It also
  constructs the joint probability law from the original nonnegative normalized
  Lebesgue density, proves the corresponding prior law is a probability measure,
  and lifts prior-almost-sure statements to the joint law.
- `RegularPriorFlux.lean` constructs the global C1 compact flux `p η` from a
  density regular only on the open test-support region. Both prior information
  and channel information are integrable automatically. No finite global prior
  Fisher information or boundary density regularity is assumed.
- `GaussianVanTrees.lean` proves the genuine nonnegative squared-risk lower
  bound for every Borel decoder, including infinite-risk decoders. It derives
  all score integrability premises and uses `BorelRisk` clipping. Its finite-risk
  and all-Borel forms apply to two-component compact interior test fields and
  arbitrary (including singular) receiver rows.
- `WeightedVariational.lean` constructs compact interior smooth approximations
  by normalized convolution and compact cutoffs. It proves the exact weighted
  inverse-Gram variational supremum and constructs a detecting scalar test from
  a nonzero directional target second moment.
- `GaussianBayesConverse.lean` assembles the actual fixed-prior all-Borel Bayes
  lower asymptotic coefficient from the preceding theorems. The separate total
  complex noise power corollary includes the factor 1/2. The prior is only C1
  and positive on a full-prior open set. The globally C1 target hypothesis is
  discharged for the manuscript's closed-interval postprocessing by
  `EndpointExtension.lean`.
- `GaussianSequentialConverse.lean` proves fixed-test bounds for changing
  receiver rows and actual optimized Borel risk. Its singular-direction theorem
  constructs the detecting smooth test, then proves divergence of normalized
  optimal risk when sensed energy in that direction tends to zero. A positive
  target directional second moment and positive finite-stage channel energy
  are explicit hypotheses; no score, test-existence, or information-bound
  premise is assumed.

- `GaussianLawBridge.lean` identifies the actual conditional and joint likelihood
  laws with independent standard complex Gaussian additive observations, including
  nonnegative squared-risk identities.
- `GaussianMovingGram.lean` proves the full variational lower bound along changing
  receiver Gram matrices. Test-energy convergence follows from the three actual
  Gram entries and integrable compact test moments; it is not assumed.
- `GaussianWorstCase.lean` defines conditional Gaussian risk, the extended-real
  supremum over the actual moment domain, and the actual infimum over all Borel
  decoders. Tonelli proves Bayes risk is the prior average of conditional risk.
  A constant decoder proves the optimized worst-case risk is finite. Consequently
  the genuine Bayes optimum is at most the genuine worst-case optimum.
- `LocalBallPrior.lean` constructs normalized uniform probability densities on
  positive-radius interior balls and proves local C1 positivity, full support,
  mass one, and approximation of continuous expectations at any interior point.
- `GaussianMinimaxConverse.lean` uses those actual local priors to prove the
  nonsingular moving-Gram worst-case converse on any moment domain contained in
  the closure of its interior. The inverse-Gram coefficient maximum is attained
  on nonempty compact domains. Its singular theorem starts from spanning interior
  gradients and a lost nonzero moment direction, constructs a detecting point,
  prior and smooth scalar test, and proves divergence of the actual optimized
  normalized worst-case risk.

The Gaussian proof chain includes statistical converses, variational
completeness, local priors, and minimax risk optimization. The completed
fixed-prior equality and attainment by the displayed minimum decoder are
assembled in [MinimumDecoderGaussianLimit](../Analog/MinimumDecoderGaussianLimit.lean).
[GaussianFixedMinimax](../Analog/GaussianFixedMinimax.lean) proves the
fixed-encoder minimax equality, and
[GaussianOptimizedMinimax](../Analog/GaussianOptimizedMinimax.lean) proves
the optimized equality and its attainment by a fixed encoder and decoder.
[COVERAGE.md](../COVERAGE.md) records their exact correspondence to the paper;
[verification/report.json](../verification/report.json) records the aggregate audit.
