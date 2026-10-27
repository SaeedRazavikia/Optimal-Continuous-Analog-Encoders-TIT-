# Completion separation and heterogeneous differential rigidity

This update addresses the analytic separation argument in the
[paper](https://arxiv.org/abs/2610.21536v1), Appendix A, Step 1, and derives the independent distinct-node
anchors used in the differential conclusion. All statements use the pinned
Lean 4.24.0/mathlib environment. Final aggregate kernel evidence is recorded
in the project-level verification report.

## New complete analytic chain

`Analog/LocalPexider.lean` proves the continuous rectangular Pexider theorem.
If `L(x+y)=H(x)+Q(y)` on a nondegenerate rectangle, then H and Q are affine
with one common slope, including endpoints. Only continuity on the relevant
intervals is assumed. The proof averages in one variable and uses the
fundamental theorem of calculus; this derives differentiability instead of
assuming it. It replaces the manuscript's rational-subdivision argument with
an equivalent rigorous proof.

`Analog/CompletionSeparation.lean` then proves:

1. A mixed rank-one determinant identity and nonzero row/column witnesses
   force every relevant entry to be nonzero.
2. The manuscript's no-zero-on-an-open-interval property supplies those
   witnesses on the actual feature coordinate ranges. Nonvanishing on the
   full interval of sums is derived, not assumed in the final argument.
3. Taking real logarithms produces rectangular Pexider identities. Real
   logarithms handle either sign; continuity and the intermediate value
   theorem subsequently exclude a sign switch.
4. Functional independence of the two completion-feature coordinates forces
   both Pexider slopes to vanish. Rank zero on a rectangle therefore makes
   both receiver derivatives constant on nonempty translated intervals.
5. If at least one receiver derivative is nowhere locally constant, every
   rectangle contains a separating pair of completions.
6. `separatingLocus_dense` proves the actual closure/density statement, and
   `separatingLocus_open` proves openness relative to the open moment rectangle.
7. `noConstant_derivative_of_noAffine` and
   `receiver_derivative_noZeroInterval` derive the derivative conditions from
   the manuscript's receiver alternatives. The nonconstant affine branch
   carries its nonzero slope; `receiverAlternative_of_nonconstant` derives
   that slope condition from nonconstancy and an affine representation.
8. `dense_open_separation_of_receiver_alternatives` assembles the dense-open
   conclusion without assuming either separation or derivative nonvanishing.

The feature-range assumptions are also derived:
`independent_coordinate_ranges` supplies actual nondegenerate compact interval
images from continuity and functional independence on a closed source interval.
`independent_div` proves invariance under the common K normalization. These
are actual attained coordinate ranges, not convex-hull substitutions.

The dense-open theorem is expressed in normalized coordinates
`A(ξ+x(t))`, `B(η+y(t))`, exactly the coordinate form used in the manuscript's
Step 1. It does not add a C² hypothesis: the receiver derivative functions
need only be continuous. Source coordinates need not be invertible.

## Derived heterogeneous derivative conclusion

`Analog/HeterogeneousSeparation.lean` proves
`independent_tangents_across_nodes` for four separate scalar feature functions.
Continuous closed-interval features, interior differentiability, and separate
functional independence produce tangent columns at different nodes with a
nonzero determinant.

`common_derivatives_of_independence` uses four distinct nodes and derives all
independent anchors and common derivative coefficients. It needs triple
encoder/feature determinant identities only where the last two feature
columns are independent; it imposes no identity at a degenerate pair.

`affine_of_independence_and_triple_determinants` chooses four nodes from `K≥4`
and integrates through both endpoints, producing common feature coefficients
and a separate offset at each node. Encoder differentiability and regular
triple determinant identities remain explicit premises here. They are the
output expected from the heterogeneous local-chart/regularization chain.

## Actual finite-node completion and domain assembly

`Analog/HeterogeneousCompletion.lean` now connects the normalized analytic
argument to the physical finite-node computation. It constructs actual source
tuples with three varying nodes, a fourth completion node, and every other
node fixed at a valid value. Finite-sum identities retain all background
contributions and the true factor `1/K`. Exact computation therefore preserves
each completion readout under partial encoded collisions.

The actual paired readout is locally injective whenever its two gradient rows
have nonzero determinant. This is proved with the strict inverse-function
theorem; the determinant's `1/K²` scaling is explicit. The identifying locus
is defined through those physical completion readouts, and
`identifying_collision_neighborhood` derives local moment recovery directly
from `HeterogeneousScore.ExactComputation`.

`Analog/HeterogeneousCompletionDensity.lean` completes the domain connection.
Feature lower and upper endpoints are the infimum and supremum of the actual
closed-source images. `exact_feature_ranges` proves that these endpoints are
attained and distinct from the original continuity/independence assumptions.
The affine normalization is a homeomorphism, so the dense normalized
separation result transfers back to actual partial moments.

The separate `Analog/HeterogeneousMomentRanges.lean` module proves that a
regular last pair places both partial moment coordinates strictly inside the
sum of the three selected coordinate intervals. It also bounds the actual
fixed-node background and proves that completed intervals stay inside the
full normalized receiver domain. These facts are used by
`dense_identification` to derive density at every actual regular triple. That
theorem assumes only the original feature continuity/independence, the
receiver's interior C¹ regularity, the affine-or-nowhere-affine alternatives,
and at least one nowhere-affine receiver. It assumes no identifying-density,
chart, determinant-conclusion, or encoder differentiability premise.

## Integration and verification

The new physical completion and density modules compile warning-free under
the pinned Lean 4.24.0/mathlib project. They supply the actual identifying
locus and density used by the separate topological/local-chart and full
heterogeneous rigidity modules. The final original-assumption theorem and
its endpoint/nonsingularity assembly are maintained there; project-level
audit reports record the final aggregate kernel evidence.
