# Continuous-encoder formalization: remaining scope

Status: **incomplete for unrestricted continuous encoders**. The formalization proves selected manuscript results, including complete coefficient-class design and the analytic rigidity chain from local continuous factorizations. It does not establish the unrestricted continuous-encoder classification or formalize every proof in the paper.

## Completed rigidity analysis

`GeneralRigidity.lean` and `EncoderRegularity.lean` treat arbitrary prescribed γ=(φ₁,φ₂). They now prove:

- Independent interior tangent anchors from functional independence, genuine local pair-statistic inverses, and witnesses that regular triple statistics are actual valid input sums.
- Automatic C¹ regularity of an encoder from a local continuous triple factorization. The proof extends the chart receiver from a smaller closed ball using Tietze, constructs a smooth compact averaging kernel of integral one, and differentiates the resulting convolution. It assumes neither a smooth receiver nor encoder differentiability.
- Selection of identifying anchors for every first input by the local submersion and density on the regular triple image.
- Propagation of derivative determinant identities from identifying triples to fixed regular anchors, constant affine coefficients, and integration through both endpoints.

The combined theorem is:

```lean
Analog.EncoderRegularity.planar_affine_of_dense_charts
```

Its conclusion is `E s = c + φ₁ s • u + φ₂ s • v` throughout [-1,1]. Its remaining structural hypothesis, `DensePlanarCharts`, supplies continuous source-box factorizations only at regular triples whose statistic lies in the dense identifying set. It does not assume factorization at every regular triple or assume the derivative conclusions.

`RigidityAnalysis` and `RigidityCompletion` retain the earlier original-family results, including the final coefficient-independence argument for affine-feature encoders. `PlanarTopology` additionally verifies compact-quotient recovery, endpoint-inclusive injectivity of exact original-family encoders, and continuous recovery of the actual triple moments. Recovery of moments from encoded sums does not itself establish the reverse local factorization required by `DensePlanarCharts`.

## The remaining topological interface

The unproved step is to derive the local continuous factorizations from continuity, exactness, and common-completion identification. The manuscript uses planar invariance of domain: a continuous injection on an open subset of the real plane has open image. The required statement can be specified as:

```lean
∀ (B : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → (ℝ × ℝ)),
  IsOpen B → ContinuousOn f B → Set.InjOn f B →
  IsOpen (f '' B)
```

This specification is not a theorem proved by the artifact. Applied to every open subset of the domain, it supplies the open-map hypothesis in `Analog.open_slice_fiber_constancy`. That checked lemma does not derive openness from continuity and injectivity, and its recovery map need not be continuous.

No applicable invariance-of-domain theorem was found in the inspected pinned mathlib source. Open-map results for linear maps and results that already assume a local homeomorphism do not provide the required nonlinear continuous-injection theorem. This observation does not rule out a suitable formalization elsewhere.

Thus the topological production of `DensePlanarCharts` is the remaining interface in the affine-representation converse. Smoothing and dense propagation are no longer outstanding. The full extended exactness equivalence still requires final nonsingularity/operational assembly for arbitrary continuous F; the positive-score design statements already derive positive definiteness from identification.

## What this means for optimal encoder design

`TwoStatisticAttainment` constructs spanning anchors and positive feasible designs and proves compactness and maximum attainment for the general pair-constrained SDP. `TwoStatisticPositivity` derives positive definiteness from the manuscript's common-completion condition and realizes the attained optimum as a continuous exact peak-admissible planar encoder. Its operational score is exactly K² times the SDP optimum, and it is optimal over every affine coefficient curve, including singular competitors.

Enlarging that competitor class to all continuous encoders requires the remaining continuous rigidity reduction. The same distinction applies to the previously verified operational variance optimum over quadratic coefficient curves. Positive coefficient-class optimality does not by itself prove unrestricted continuous optimality.

The real-analytic identification criterion and the general endpoint-gradient specialization are separate unverified extension results; see `EXTENSION_SCOPE.md`. Other manuscript results have their own scope and are tracked in `COVERAGE.md` and `THEOREM_MAP.md`. Completing the topological bridge would not alone justify a claim that every proof in the paper is formalized.

## Reproducible dependencies

The artifact uses Lean 4.24.0 and [mathlib commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7). The completed analysis uses its inverse-function theorem, convolution, finite-dimensional smooth-kernel, Tietze-extension, and mean-value results. `python3 verify.py` compiles the project and audits the advertised declarations; `verification/report.json` records a successful run and its source hashes.
