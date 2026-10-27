> Historical first-pass mathematical review. Completion work in version 0.4.0
> supersedes its implementation-gap descriptions. See COVERAGE.md, THEOREM_MAP.md
> and the completion notes for the current verified scope.

# Current rigidity, synthesis, and gradient proof audit

Audited source: `Main.tex`, supplied in this project, 27 October 2026.
This note distinguishes a mathematical review of the manuscript argument
from the exact scope of the Lean declarations. The supplied historical
verification report is not evidence of coverage of newly written statements.

## Findings

The current theorem `thm:rigidity` permits different preprocessing curves
and different encoders at every node. Its assumptions are C¹ regularity on
the source interior, functional independence at each node, and the condition
that each nonconstant receiver function is either affine everywhere or
nonaffine on every open subinterval. At least one receiver function must be
nonaffine. The older formalization works principally with one shared
preprocessing curve and one shared encoder. It therefore does not prove the
current statement by direct instantiation.

The current `thm:sdp` is also substantially broader than the previous
positive-optimum formal theorem. It does not assume independence of the
local preprocessing functions or Lipschitz continuity of the target. It
includes singular Gram matrices and the zero-optimum case, and establishes
positivity if and only if the target is Lipschitz on the actual attainable
set. The previous `TwoStatisticAttainment` and `TwoStatisticPositivity`
theorems impose stronger assumptions and use a shared curve.

No mathematical counterexample was found to these two current statements
in this review. This conclusion is a proof audit, not a machine proof of
the complete theorems.

## Rigidity argument: checked reasoning and remaining interfaces

1. **Dense two-completion separation.** If the gradient determinants vanish
   on an open rectangle, neither derivative can vanish at any of the
   translated arguments. The common multiplicative ratio is positive by
   continuity on the connected source interval. Taking logarithms yields a
   local additive increment identity; continuity forces linear logarithms.
   Functional independence at the fourth node then forces both exponential
   rates to vanish. This contradicts the receiver-function hypothesis.
   This current argument is not the old real-analytic sufficient condition
   listed in the historical extension scope. Its interval functional
   equation, derivative separation, and inverse-function assembly remain
   unformalized.

2. **Independent tangent columns.** Functional independence at each node
   implies that its interior tangent vectors span the plane. Hence two
   different nodes admit independent tangent columns. The existing
   `GeneralRigidity.independent_tangents` handles one curve. A formal
   heterogeneous assembly must select columns from different nodes.

3. **Reverse local factorization.** The collision implication gives moment
   recovery from the encoded sum. The manuscript correctly invokes planar
   invariance of domain to obtain the reverse local dependence. Existing
   compact-quotient recovery and open-slice fiber-constancy lemmas do not
   prove this openness theorem. The remaining topological dependency must
   not be replaced by an axiom or silently omitted.

4. **Regularization.** The convolution argument differentiates the smooth
   averaging weight, so it does not assume a differentiable decoder. The
   existing shared-curve regularization theorem supplies a useful proof
   pattern, but its written hypotheses do not directly cover three distinct
   preprocessing curves and three distinct encoders.

5. **Derivative propagation and integration.** The new
   `Analog/HeterogeneousRigidity.lean` formalizes the distinct-node algebra:
   `relation_of_two_anchors`, `common_slopes_of_four_anchors`, and
   `coefficients_exist` give common derivative coefficients from independent
   columns and the explicit three-node determinant identities.
   `integrate_common_derivatives` integrates a node-indexed family through
   both endpoints, with common coefficients and node-dependent offsets.
   These conclusions retain determinant, differentiability, and anchor
   hypotheses; they do not derive them from exact computation.

6. **Nonsingularity and operational reduction.** Local recovery on an
   attainable open neighborhood excludes a kernel direction of the common
   coefficient matrix. The current heterogeneous exactness equivalence and
   its reduction of the unrestricted optimum to coefficient encoders still
   need a single formal assembly theorem.

## Synthesis argument

The generalized Schur-complement reconstruction is mathematically valid
also when the common lower Gram block is singular: positivity forces the
off-diagonal vector into the range of that block, and the reconstructed
offset lowers only the leading diagonal entry. The original
`GramSynthesis.psd3_iff_schur` and reconstruction theorems assume a positive
determinant, so they alone do not cover this step. The new `SingularGram`
module now proves the all-rank reconstruction properties and common-column
compatibility by explicit scalar factorizations. `HeterogeneousSynthesis`
assembles the constructive operational feasible-point theorem. See the dedicated
singular-Gram audit note.

The current compactness argument correctly addresses nonidentifiable
coefficient directions by projecting onto the span of all local feature
variations and absorbing the orthogonal constant component into each node
offset. Bounds then follow from finitely many fixed variation anchors and
the peak constraint. This quotient/projection construction is essential:
the unreduced matrix feasible set need not be bounded when the local
features are dependent. Existing attainment theorems do not establish this
new reduced compactness argument.

The two Lipschitz implications have different scopes. A scaled identity
embedding gives a positive feasible score from a Lipschitz bound. Conversely,
a positive secant coefficient gives a Lipschitz bound through the finite
operator norm of the common Gram block. Neither direction requires moment
set convexity. The theorem asserts an attained optimum even when this
coefficient is zero; the old positive attainment theorem cannot supply that
case.

## Gradient sandwich

The stated upper bound follows by integration along segments in the convex
superset. The lower bound uses actual perturbations in the interior of the
attainable moment set in the direction of the inverse Gram matrix applied
to the gradient. Equality on a compact convex full-dimensional attainable
set follows from density of its interior and gradient continuity. These
arguments retain their separate geometric assumptions; an ambient gradient
bound need not be sharp on a lower-dimensional attainable set.

The example with gradient `(1-m₁²,1)` correctly attains squared norm two at
the interior attainable point `(0,1/2)` and only one at the two endpoints.
It supports the claimed robustness scores 8 and the incorrect endpoint-only
prediction 16 when K = 4 and G is the identity. The general sandwich and
this current counterexample are not supplied by the original-family endpoint
score theorem.

## Scope conclusion

The new heterogeneous algebra is a concrete part of Step 3 of the current
rigidity proof. Full coverage still requires the dense separation argument,
the planar topology bridge, heterogeneous regularization and propagation,
the singular/zero-score SDP assembly and reduced compactness argument, and
the general gradient sandwich. See the current coverage and verification
reports for compiler status; this audit note makes no independent build
claim.
