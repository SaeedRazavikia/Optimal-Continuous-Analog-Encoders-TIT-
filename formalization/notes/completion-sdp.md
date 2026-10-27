# Completion of the general heterogeneous SDP theorem

`Analog/HeterogeneousAttainment.lean` closes the coefficient-class attainment
and Lipschitz-positivity portions of the current [paper](https://arxiv.org/abs/2610.21536v1), `thm:sdp`.
The theorem compares actual node-indexed encoders, not a surrogate objective.
It permits dependent local feature families, singular common Gram matrices,
and zero optimal score. It adds no compactness or optimizer hypothesis.

## Compactness without identifiable coefficients

The manuscript projects coefficient matrices onto the span of local feature
variations. The formal proof uses an equivalent finite-dimensional argument:

1. `coefficientMap` sends all node offsets and the two shared columns linearly
   into the space of actual continuous node-encoder functions on the compact
   source interval. Its range is finite-dimensional regardless of any kernel
   in this parameterization.
2. `peakSet_isClosed` and `peakSet_norm_bound` prove that the actual continuum
   peak constraints form a closed uniformly bounded set in this range.
   `peakSet_isCompact` derives compactness from finite-dimensionality.
3. `feasibleSet_isCompact` includes a nonnegative separation coordinate and
   every actual input-pair inequality. One fixed unequal-target pair bounds
   the separation coordinate; continuity of each received-distance expression
   makes the complete feasible set closed. Thus no target continuity,
   positive separation, or independent feature assumption is needed here.
4. `operational_maximum_attained` maximizes the separation coordinate on this
   compact set. `Operational.le_score_iff` identifies it with the true quotient
   infimum. The zero encoder proves nonemptiness even at zero power/score.

The function-space norm uses the standard product max norm on real coordinates.
This affects the auxiliary boundedness proof only; all peak and score
constraints themselves use the manuscript's exact sum of squared coordinates.
`product_lipschitz_iff_euclidean` also proves equivalence with an explicit
Euclidean-distance Lipschitz condition, so no metric convention is left implicit.

## Current-model assembly

`heterogeneous_operational_maximum_attained` specializes the function-space
argument to `HeterogeneousScore` and its actual attainable image. It derives
an optimal common-column/node-offset encoder under precisely these hypotheses:

- each prescribed local feature curve is continuous on [-1,1];
- the readout is nonconstant on the actual attainable set;
- power is nonnegative.

`heterogeneous_sdp_attained` additionally assumes K>0 and exhibits:

- an `SDPPoint K` satisfying `SDPFeasible`, which is the current full family
  of PSD block, continuum peak, and all attained-pair secant constraints;
- maximality of its separation coefficient against every feasible matrix family;
- actual node-dependent peak-feasible encoder coefficients;
- the exact relation `operational score = K² × optimal separation`;
- comparison against every common-column/node-offset coefficient encoder.

The proof maps the attained encoder to its actual Gram matrices and uses
`HeterogeneousSynthesis.feasible_operational_synthesis` for the reverse
comparison. This proves no relaxation gap and simultaneous attainment of
both optimization problems, including singular and zero-score cases.

## Positivity if and only if Lipschitz continuity

`positive_feasible_implies_lipschitz` bounds the full Gram quadratic form by
`(|A| + 2|C| + |B|) × distance²` and converts the positive secant inequality
into an actual `LipschitzOnWith` bound on the attainable set.

`lipschitz_implies_positive_feasible` constructs a positive multiple of the
identity Gram matrix. The uniform norm of the continuous features supplies
its continuum power bound. The separation coefficient is strictly positive
at every positive power. The constructed point is proved PSD and satisfies
all pairs, not merely finitely many samples.

`positive_feasible_iff_lipschitz` combines these directions.
`optimal_positive_iff_lipschitz` gives the same equivalence at **any** attained
optimal SDP point, and may be applied directly to `heterogeneous_sdp_attained`.
`optimal_positive_iff_euclidean_lipschitz` states the result with the precise
Euclidean norm of the manuscript.

## Scope

This module proves the coefficient-class SDP theorem, including attainment,
zero relaxation gap, and the positivity characterization.
[HeterogeneousGlobalOptimum](../Analog/HeterogeneousGlobalOptimum.lean)
proves that, under the paper's rigidity assumptions, the same value is optimal
over **all continuous peak-feasible encoders**, using the classification proved in
[HeterogeneousFullRigidity](../Analog/HeterogeneousFullRigidity.lean).
This completes Theorem 2's unrestricted-encoder conclusion. The separate
Gaussian statistical results and their exact scope are listed in
[COVERAGE.md](../COVERAGE.md).

Validation: the complete module compiled with the pinned Lean 4.24.0 and
mathlib revision, without warnings. The project-level verification report
records the aggregate kernel/axiom check. No `sorry`, new axiom, numerical
oracle, or assumption of the desired optimum occurs in this module.
