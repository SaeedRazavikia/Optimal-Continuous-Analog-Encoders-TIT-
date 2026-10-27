# Actual matrix finite dual certificates

`Analog/HeterogeneousDualCertificate.lean` completes the finite dual-witness
argument in the [paper](https://arxiv.org/abs/2610.21536v1), Appendix “Verified Primal and Dual Bounds”, equation
`eq:general-dualwitness`.

The principal theorem is `current_program_dual_upper_bound`. It takes a feasible
point of the actual current heterogeneous secant SDP, finite source samples in
`[-1,1]`, finite pairs in the actual attainable moment set, nonnegative sample
and pair weights, and the manuscript's matrix witness conditions. It proves

```text
q.lam ≤ P * ∑ k, ∑ i, α k i.
```

Each node may have a different finite sample index type. The residuals are
actual positive semidefinite three-by-three matrices, and the equality of the
sum of the two-by-two dual blocks with the weighted secant outer products is
an actual matrix equality. The normalization is the actual weighted squared
readout-difference sum. No scalar trace inequality or shared-block trace
identity is assumed.

The proof establishes the rank-one trace formula, the lower-block embedding
trace formula, the weighted trace identity, and each node's trace inequality
from positivity of the trace of a product of positive semidefinite matrices.
It then derives the common-block identity from the matrix equation, applies
the primal sampled peak and secant inequalities, and uses normalization. The
wrapper explicitly converts the current SDP's scalar `PSD3` condition to
`Matrix.PosSemidef` and identifies its quadratic forms with the matrix forms.

There is no additional feature independence, nonsingularity, positive-power,
positive-optimum, regularity, attainment, or rigidity premise. Symmetry of the
dual blocks need not be a separate hypothesis: the stated PSD residuals are
sufficient for the proof (and imply symmetry because the weighted outer-product
matrices are symmetric).

Applying the theorem to the feasible optimizer from
`HeterogeneousAttainment.heterogeneous_sdp_attained` bounds the attained SDP
optimum. `FiniteCertificates.absolute_gap_bound` and
`FiniteCertificates.relative_loss_bound` then give the manuscript's gap
bounds once a certified primal lower bound is supplied. The upper bound alone
does not require existence of an optimizer.

As in the manuscript, this proves sufficiency of a supplied finite dual
witness. It does not assert that finite dual witnesses attain the dual optimum
or can produce arbitrarily small gaps. Nor does it identify the unrestricted
continuous-encoder optimum without the separate full rigidity theorem.

Validation: the entire new module, containing 11 public theorems, was checked
with the pinned Lean toolchain by `lake env lean
Analog/HeterogeneousDualCertificate.lean`; it compiles without warnings and
contains no `sorry`, added axioms, or `native_decide`.
