# Unrestricted continuous-encoder SDP and grid scope

`Analog/HeterogeneousGlobalOptimum.lean` connects the proved full rigidity
theorem to actual robustness optimization. Its main result,
`unrestricted_sdp_attained`, exhibits the actual attained heterogeneous SDP
point and its peak-feasible encoder and proves that every continuous
peak-feasible encoder has score at most `K² * q.lam`.

Competing encoders are not assumed exact or affine. If a competitor has
positive score, `positive_score_implies_exact` gives exact computation and
the full rigidity theorem supplies its common affine columns. The already
proved coefficient-class optimizer then bounds its score. A competitor
whose score is nonpositive is bounded by the nonnegative attained SDP
objective. Thus zero optima and singular optimal Gram matrices remain
included, even though positive-score competing encoders are nonsingular.

The theorem uses the original feature regularity and independence, and the
receiver alternatives on the interior mean domains. These are derived from
the manuscript's closed-domain receiver assumptions by the proved
`receiver_alternative_of_closed` and
`noAffineInterval_of_closed_nonaffine` bridges in
`HeterogeneousFullRigidity`. It also retains the SDP theorem's actual-image
nonconstancy assumption on the target and nonnegative peak power. No
attainment, compactness, bounded coefficient set, chart, or density premise
is supplied by the user.

The helpers `received_eq_of_source_eq` and `score_eq_of_source_eq` prove that
agreement on the physical closed source intervals suffices to identify the
actual aggregate and operational infimum. This avoids demanding encoder
formulas outside the physical source domain.

For grid certification, `pointCoordinates_feasible` converts the actual
SDP point into the seven-coordinate continuum program used by
`HeterogeneousGrid.certified_discretization`, including the true common
Gram block, common objective, and all actual attainable secants.
`grid_maximum_global_bound` applies any such continuum optimizer's
maximality to this converted point. Combining it with
`unrestricted_sdp_attained` shows that the grid theorem's continuum
objective bounds every continuous peak-feasible encoder. The existing
grid rescaling and operational realization then provide the stated lower
certificate, while the sampled optimum provides the upper certificate.
The separate `scaling_gap_isBigO` result establishes the quadratic rate
using bounds derived from fixed spanning anchors.

The module contains six public theorems and one coordinate definition.
It compiles warning-free under the pinned toolchain. Final aggregate audit
records the all-theorem kernel and axiom verification.
