# Completed heterogeneous rigidity

The full current theorem `Main.tex` `thm:rigidity` is proved in both directions:

```text
Analog.HeterogeneousFullRigidity.heterogeneous_rigidity
```

Its hypotheses are the manuscript's original ones: K≥4; each node's two
features continuous on [-1,1] and C¹ on (-1,1); per-node linear independence of
1 and the two features; continuous encoders; receivers continuous on their
closed mean intervals and C¹ in their interiors; each receiver either affine
on its whole mean interval or nowhere affine on a nonempty open subinterval;
both receivers nonconstant; at least one receiver nonaffine.

The conclusion is an equivalence between actual finite-input exact
computation and common affine coefficients:

```text
∃ u v, ∃ c : Fin K → ℝ × ℝ,
  u.1 * v.2 - v.1 * u.2 ≠ 0 ∧
  ∀ i x ∈ [-1,1], E i x = c i + φ₁ i x • u + φ₂ i x • v.
```

The determinant is the genuine two-column determinant, equivalent to real
linear independence of the common encoder columns. Node offsets are separate,
node feature curves are separate, and the formula includes both source
endpoints. Exact computation is represented by preservation of the desired
scalar readout under every collision of valid received sums; it imposes no
continuity or differentiability on a decoder.

There are no additional density, local-chart, tangent-anchor, decoder
regularity, encoder differentiability, or topology premises. The closed mean
intervals use actual per-node feature extrema, and `exact_feature_ranges`
proves those intervals are the genuine coordinate ranges. No convexification
of the actual joint attainable set is used.

## Complete proof assembly

- `HeterogeneousSeparation` derives independent tangents at different nodes,
  propagates three-node determinant relations to common derivative
  coefficients, and integrates through the closed source endpoints.
- `LocalPexider` and `CompletionSeparation` establish the continuous local
  additive-equation argument, derivative nonvanishing, and dense open
  two-completion separation. No second receiver derivative is assumed.
- `HeterogeneousCompletion` constructs actual finite-node completions and
  proves the normalized readout formulas and local recovery of partial
  moment sums from exact computation. Its two-completion local inverse is
  a genuine inverse-function-theorem application.
- `HeterogeneousMomentRanges` and `HeterogeneousCompletionDensity` derive
  the true feature ranges, fixed-node background bounds, strict interior
  membership of regular triple statistics, completion-domain inclusion,
  and density at every actual regular triple statistic.
- `PlanarBrouwer`, `PlanarInvarianceCore`, and `PlanarInvariance` prove
  planar invariance of domain and the reverse factorization argument.
  The separately proved planar Brouwer instance discharges the generic
  core's fixed-point premise. See `completion-topology.md` for the exact
  external provenance, license, pinned-toolchain port, and independent audit.
- `HeterogeneousCoordinates` constructs the actual source coordinates
  `(x,y,z) ↦ (x, two feature sums)` by the inverse function theorem.
  `HeterogeneousLocalCharts` uses them and proved planar topology to derive
  a continuous reverse factorization on an actual source box.
- `HeterogeneousRegularity` proves automatic encoder C¹ regularity by
  convolution averaging and derives the three-node determinant identities.
  `HeterogeneousAnalyticRigidity` assembles regularity, dense propagation,
  common coefficients, and endpoint integration.
- `HeterogeneousNonsingularity` derives global injectivity of the coefficient
  map from its injectivity on a constructed nonempty planar open slice.
  `HeterogeneousFullRigidity` connects every stage, proves nonsingularity,
  and gives the converse by recovering the actual two mean statistics.

The earlier intermediate theorems with explicit dense-chart hypotheses remain
useful modular results. Their hypotheses are now discharged in the full
original-hypothesis theorem; they are not the endpoint of the formalization.

## Validation

The complete main module compiles without warnings under pinned Lean 4.24.0,
both normally and with `--trust=0`, and its `.olean` is built. The source has
no admitted proofs, added axioms, or native-decision proofs. The aggregate
verification report is the authority for final whole-project declaration
counts and all-theorem axiom checking.
