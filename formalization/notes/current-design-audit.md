> Historical first-pass mathematical review. Completion work in version 0.4.0
> supersedes its implementation-gap descriptions. See COVERAGE.md, THEOREM_MAP.md
> and the completion notes for the current verified scope.

# Current design and certification audit

Source of truth: `../../Main.tex`, as supplied in the uploaded project.
This note records a mathematical/source comparison, not a new Lean build.
The original coverage inventory described a different split-source revision.
In particular, its references to `sections/*.tex`, `manuscript.tex`,
`thm:quartic`, `cor:quadratic-pareto`, and a 17-statement inventory must not
be treated as an inventory of the present manuscript.

## Current claims and precise formal scope

| Current source | Existing formal result | Remaining obligation |
|---|---|---|
| Lemma `prop:score` | `GeneralScore.general_operational_score` and `general_score_small_distance_sharpness` prove the actual all-input score and shrinking-distance sharpness. They require only K >= 2 and permit ordinary convex/concave readout; the current stronger hypotheses imply these. | The appended equivalence between all secant constraints and endpoint matrix constraints, including singular G at lambda = 0, still needs an assembled specialization with the exact present quantifiers. |
| Proposition `thm:parabola`, quadratic case | `GeneralQuadratic` proves the supporting inequality, sum-of-squares certificate, root, displayed closed form, and coefficient-class optimum. `PowerScaling` restores P. The variance specialization in `VarianceOptimal` connects the actual operational score. | The general-psi assembled operational theorem and enlargement from coefficient curves to all continuous, possibly node-specific encoder collections rely on the rigidity/reduction interfaces. |
| Proposition `thm:parabola`, quartic case | `Quartic` proves root existence and uniqueness, peak identity, contacts, positive multipliers, stationarity, global objective optimality and arbitrary planar coefficient reduction. `QuarticPower.quartic_optimal_all_power` restores arbitrary P. | Its stated score is a Gram objective. `GeneralScore` supplies the general operational formula separately. An assembled theorem matching all quantifiers of the proposition and its all-continuous conclusion is not supplied. |
| Theorem `thm:certifiedgrid` | `CertifiedGrid` proves the 1/8 interpolation bound from derivatives, finite grid bracketing, attained sampled/continuum optima, C2 bounds and O(h^2) scaling for a shared feature `(1,s,phi(s))` with endpoint score constraints. Its operator/finite-grid interpolation lemmas themselves are general. | The current theorem uses node-dependent `(1,phi_1,k,phi_2,k)`, a shared G, and every attainable secant constraint. The existing end-to-end `c2_grid_certificate` does not formalize that larger optimization program. Singular reconstruction and the joint-node compactness/attainment wrapper also remain to be connected. |
| General finite dual witness `eq:general-dualwitness` | New `FiniteCertificates.finite_secant_upper_bound` proves the weighted-separation/peak argument with actual finite sums, nonnegative weights, lambda >= 0 and normalization >= 1. New absolute and relative gap lemmas prove the displayed loss formula. | The scalar theorem exposes the trace inequality and common-block identity as hypotheses. New `psd_trace_product_nonnegative` proves nonnegativity of the trace pairing itself for arbitrary real PSD matrices. The residual/common-block trace identities, attainment of moment pairs, and an assembled current-SDP theorem remain to be connected. |
| Peak-rescaled primal witness | Existing `CertifiedGrid.peak_scaling` and new `FiniteCertificates.scale_all_peaks`, `scale_all_separations` verify homogeneous scaling for every node/input and arbitrary separation index families. | Concrete matrix encoding, interpolation-to-bound assembly for the present node-dependent program, and reconstruction remain separate. Scaling cannot certify any omitted separation constraint. |
| Endpoint finite dual witness `eq:dualwitness` | Its scalar weak-duality conclusion follows from the same finite certificate arithmetic once the matrix trace premises are supplied. | The PSD trace-pairing sign is proved separately, but no complete endpoint-witness specialization or Lean rational exponential enclosure is supplied. |
| Polynomial projection decoder | `StripProjection`, `GeneralDecoder` and `ExplicitVarianceDecoder` verify the actual strip minimizer, nonexpansiveness, exact recovery and sharp global constant within their stated feature-family interfaces. | The exact displayed orthogonal polynomial coordinate formula still needs a named specialization if it is to be advertised individually. |
| Output clipping | `Decoder.clip_uniform` and the Gaussian clipping results preserve the appropriate bounds when the true target lies in the clipping interval/interior. | Jensen containment for every p in {2,4} and the source-distribution almost-sure interior hypotheses are not automatically established by a generic clipping lemma. |
| K = 4 attainable variance moment region | No matching end-to-end theorem found. | Convex-polytope extreme-point reduction, the one-free-coordinate description, and intermediate attainability along the constant-mean line segment remain unformalized. |
| Empirical performance and prior-aware tuning | Quadratic/frontier and small-noise modules supply many structural ingredients. | Monte Carlo values and confidence intervals are numerical claims, not Lean theorems; prior-distribution moment substitutions and general polynomial source specializations require explicit wrappers. |

## Mathematical review

No algebraic error was found in the current quadratic certificate, quartic
factorization, KKT certificate, interpolation/scaling argument, or finite
dual weak-duality argument. In particular:

- The quartic root lies in `(0,1/3)` because the positive left side is strictly
  increasing while the right side strictly decreases for M > 0. Evenness and
  strict convexity/concavity of psi imply the required M = |psi'(1)| > 0.
- The quadratic parameter identities and the quartic multipliers agree with
  the existing formal development.
- The general dual proof needs lambda >= 0 when it uses a normalization
  greater than or equal to one. The current primal program imposes this,
  and the new finite-sum theorem retains that hypothesis explicitly.
- The relative-loss certificate uses `(upper - lower) / upper`. For
  `0 < lower <= optimum <= upper`, this does bound
  `1 - lower / optimum`; the denominator must not be changed to the lower
  certificate when quoting this particular guarantee.
- The current certified-grid theorem correctly retains *all* secant
  constraints. A finite peak grid alone does not provide a numerical
  algorithm for checking an arbitrary nonlinear readout's infinitely many
  secants. The manuscript explicitly warns of this limitation.
- The moment-region boundary for K = 4 is mathematically consistent: on each
  slab `|4m_1-j| <= 1`, three signs sum to j in {-3,-1,1,3}, and the fourth
  input is `4m_1-j`. The upper curves match at the slab boundaries.

## Rechecked numerical certificate

The command

```sh
python code/certified_synthesis.py --verify-only
```

passes against the supplied rational witness. The independently recomputed
bounds are

- lower = `209834839284/500029296947`
  = approximately `0.41964508992808314`;
- upper = `104917556109394155472367/250000000000000000000000`
  = approximately `0.4196702244375766`;
- certified relative gap = approximately `5.989109550760389e-05`.

The manuscript's displayed bounds `0.419645089928` and `0.419670224438`
round outward and are therefore consistent with the exact certificate.
The detailed result, command, exit status and relevant source hashes are in
`../verification/numerical-certificate-check.json`. This is exact rational
verification in Python, not a Lean/kernel check of the arithmetic engine,
Taylor remainder theorem, or all-continuous encoder reduction.

## New proof source

`../Analog/FiniteCertificates.lean` adds seven named results: PSD trace-product
nonnegativity, weighted peak bounds, finite secant weak duality, all-constraint separation scaling,
all-node peak scaling, absolute-gap control, and relative-loss control.
Its module header and hypotheses identify exactly what is still required
for an end-to-end matrix certificate. This module compiled without warnings under the pinned Lean 4.24.0 toolchain
and mathlib revision. Full-project and axiom-audit status belongs to the
project's current verification report.
