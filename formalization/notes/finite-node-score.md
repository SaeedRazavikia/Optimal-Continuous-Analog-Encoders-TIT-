# Finite-node endpoint score (Lemma 1)

`Analog/FiniteNodeScore.lean` assembles the paper label `prop:score` for the
actual `Fin K` model with arbitrary node offsets.

- `score_eq_shared_list` proves equality of the entire operational quotient
  sets after passing between indexed inputs and finite lists. Each conversion
  preserves admissibility, the desired value, and squared received distance.
  The separate offsets cancel directly in the received-distance identity.
- `lemma_one_score` gives the exact endpoint-dual formula under the paper's
  `K >= 4`, strict convexity/concavity, and C¹ assumptions. The `dual` expression
  is the quadratic form of the inverse two-by-two Gram matrix. Positive Gram
  determinant suffices because the matrix comes from actual planar columns.
- `lemma_one_sharpness` supplies, for every positive accuracy and distance
  threshold, actual admissible indexed input pairs with distinct desired
  values, received distance below the threshold, and quotient less than the
  score plus the requested accuracy. This is the precise shrinking-pair
  formulation of the infimum-approach claim.
- `finite_target_nonconstant` and `attainable_target_nonconstant` derive the
  nonconstancy required by subsequent operational comparison theorems.

The lower-level score and sharpness statements hold already for `K >= 2`.
Feature continuity at the endpoints is assumed by the manuscript but is not
needed by this proof. Endpoint readout derivatives are taken within `[-1,1]`,
so no differentiability outside the source interval is imposed. All pairs are
actual attainable inputs; no convex hull or closure replaces the moment set.
