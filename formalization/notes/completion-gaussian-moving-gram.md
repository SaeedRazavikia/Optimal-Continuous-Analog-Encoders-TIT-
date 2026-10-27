# Moving-Gram Gaussian Bayes converse

`Analog/GaussianMovingGram.lean` proves the full variational lower coefficient
along changing invertible receiver maps, under convergence of only their
three real Gram entries. Offsets and arbitrary Borel decoders may change at
each noise level. The prior satisfies the same local C¹ positivity and
full-mass-open-set assumptions as the fixed-prior converse.

`moving_gram_bayes_converse` concludes

`LowerAsymptotic (fun n => optimalRisk p f (S n) (c n) (v n) / (2*v n))`

with coefficient

`(∫ m, ‖S₀.symm.toContinuousLinearMap.adjoint (gradient f m)‖² ∂priorLaw p)/2`.

The theorem assumes convergence of `gramA (S n)`, `gramB (S n)`, and
`gramC (S n)` to those of an invertible limiting factor `S₀`. It does not
require the receiver factors themselves to converge, and does not assume
convergence of test energies. The exact quadratic expansion derives that
energy convergence from the three compact-test moments. Positivity of the
same nonzero test under each invertible receiver is also proved.

The proof applies the actual likelihood-based optimized information bound
from `GaussianSequentialConverse` to each constructed compact test, then
uses the actual inverse-Gram variational supremum from `WeightedVariational`.
There is no assumed information inequality, no assumed approximation
conclusion, and no interchange of optimization with the noise limit.

Singular limiting Gram matrices are excluded by the separate scalar-test
converse in `GaussianSequentialConverse`; extraction of a Gram limit and the
final outer design/minimax optimization remain separate assembly steps.

The module has 6 public theorems. Ordinary Lean compilation and `--trust=0`
kernel checking pass without warnings, admitted proofs, new axioms, or native
decision shortcuts.
