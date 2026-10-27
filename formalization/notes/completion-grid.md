# Completion of heterogeneous certified discretization

The [paper](https://arxiv.org/abs/2610.21536v1) theorem `thm:certifiedgrid` has a node-dependent peak
curve and a common lower Gram block. Its sampled program retains every
attainable-moment secant. The new development formalizes that program directly;
it does not substitute the old one-curve/two-endpoint-constraint problem.

## Exact program and attainment

`Analog/HeterogeneousGridFeasible.lean` represents a design by
`q : Fin K → (Fin 7 → ℝ)`. At node k, the first six coordinates are the six
entries of its symmetric 3×3 Gram matrix and coordinate 6 is λ. `Shared`
enforces equality across nodes of the lower 2×2 block and λ. Thus the redundant
7K-coordinate representation has precisely the common-block constraints of
the manuscript's 3K+4-variable problem.

`LocalFeasible` imposes genuine `PSD3`, peak constraints over an explicit set D,
and **all** secants from the given moment set. The continuum domain is
D_k=[−1,1]; the sampled domain is the actual finite grid T_k. The main wrapper
uses exactly `HeterogeneousScore.attainable γ`, the image of valid finite-input
tuples, without taking its convex hull or closure.

The fixed three spanning samples at every node are supplied as `Anchors` with
explicit inverse-basis coefficients. These are the same fixed spanning vectors
assumed by the manuscript theorem. `local_gram_bound` derives bounds on all
six Gram entries using only those samples. An actual unequal target pair then
bounds λ in `local_coordinate_bound`. `feasible_isCompact` and
`maximum_attained` derive compactness and attained optima for arbitrary peak
test sets containing the anchors. Neither a positive score nor an optimizer
witness is assumed; zero optimum and singular Gram blocks are included.

## C² interpolation and the current theorem

`Analog/HeterogeneousGrid.lean` defines the actual Euclidean feature vector
(1,φ₁,k(s),φ₂,k(s)). `gram_operator_peak` identifies its Euclidean-operator
quadratic form with the scalar Gram peak. `feature_norm_maxima` constructs
attained norm maxima of this vector and its first two closed-interval derivative
extensions from `ContDiffOn ℝ 2`; there are no assumed derivative remainder
bounds. The derivative norms are the manuscript's κ constants, expressed in
Euclidean vector form.

`maxCurvature` is the **maximum**, over all nodes, of
2‖H_k‖(κ₁,k²+κ₀,k κ₂,k). `c2_peak_bound` applies the previously checked sharp
1/8 interpolation bound to every node and derives the single common continuum
peak bound P+M_h h²/8. `scaled_feasible` applies one factor P/(P+M_h h²/8)
to all node matrices and λ, preserving every PSD, common-block, and secant
constraint.

The main theorem is:

```
Analog.HeterogeneousGrid.certified_discretization
```

Under the current K≥1, positive-power, C², fixed-spanning-grid, spacing, and
nonconstant-target assumptions, it constructs:

- the attained feature/derivative norm maxima;
- actual sampled and continuum maximizing Gram families;
- a continuum-feasible rescaled sampled solution;
- the bracket ρ_h λ_h ≤ λ⋆ ≤ λ_h;
- actual continuous node-indexed encoders satisfying every continuum peak
  constraint and achieving operational score at least K²ρ_h λ_h.

The wrapper permits any readout F of the moment pair, so the manuscript's
sum of two continuous receiver postprocessings is included. Its assumptions
are in fact weaker on F, because continuity of F is unnecessary for these
closed linear-inequality and nonconstancy arguments.

## Uniform quadratic convergence

`uniform_caps` derives simultaneous uniform bounds on λ and `maxCurvature`
from the fixed anchors and one unequal target pair. No matrix-norm bound and
no bounded-optimizer hypothesis is supplied. `scaling_gap_isBigO` then proves

```
(fun h => λ_h - (P / (P + M_h * h^2 / 8)) * λ_h)
  =O[𝓝[>] 0] (fun h => h^2)
```

for every family of sampled feasible designs retaining those fixed anchors,
and therefore for every choice of the attained sampled maximizers. The
normalizing κ constants are fixed independently of h.

## Scope boundary

This completes the core node-dependent discretization theorem, including
attainment, exact spectral remainder, feasible rescaling, bracket, operational
reconstruction, and the claimed O(h²) scaling loss. Its interpretation as
an optimum over **all continuous** encoders is now supplied separately by
`HeterogeneousFullRigidity.heterogeneous_rigidity` and
`HeterogeneousGlobalOptimum.unrestricted_sdp_attained`, as the manuscript
requires. The grid modules themselves do not assume or assert rigidity; the
separate theorem identifies the continuum program with unrestricted optimal
robustness under the receiver hypotheses.

The separate appendix's general finite matrix dual-witness identity is not
part of this theorem and is not newly asserted here. Existing
`FiniteCertificates` remains explicit about its own matrix-assembly boundary.

Validation: both new modules compile with the pinned Lean 4.24.0/mathlib
revision without warnings. Root `verification/report.json` records the final
aggregate build and kernel/axiom audit.
