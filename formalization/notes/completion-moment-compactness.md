# Actual heterogeneous moment compactness

`Analog/HeterogeneousMomentCompactness.lean` derives compactness and
nonemptiness of `HeterogeneousScore.attainable γ` directly from the finite
source tuples and continuity of each node's feature curve on `[-1,1]`.
It proves equality with the range over the compact source-subtype product;
the attainable set is not enlarged by taking a convex hull or closure.

The public `compactFeatures` restricts the actual node feature curves to
the compact source interval. `independentFeatures` derives the compact
function-space independence hypothesis from the original nodewise
`TwoStatisticAttainment.IndependentStatistics` assumptions. A wrapper
derives compactness of the actual coefficient peak set from these inputs.

`attainable_subset_closedDomains` proves containment in the product of the
canonical **closed** coordinate intervals, defined by the sum of each
node's image infimum and supremum divided by the actual node count. The
definition is identical to `HeterogeneousFullRigidity.closedMeanDomain`.
Both feature extrema and both scalar mean endpoints are shown to be
attained by actual source values or tuples.

The open `HeterogeneousCompletionDensity.meanDomain` serves a different
purpose in local differentiation. Full attainable sets include endpoint
moments, so this module deliberately does not assert their containment in
the open mean domains. No independence or positive node-count premise is
needed for the moment compactness and closed-domain bounds; positive node
count and independence enter only the coefficient-compactness wrapper.

The module compiles with the pinned toolchain under `--trust=0`, without
warnings, admitted proofs, additional axioms, or native decision procedures.
