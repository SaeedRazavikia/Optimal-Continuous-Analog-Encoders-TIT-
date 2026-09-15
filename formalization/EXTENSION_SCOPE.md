# Unified two-statistic extension: verification scope

This document covers Theorem 4 (`thm:extension`, legacy alias `thm:polynomial`) and Appendix F of **Geometric Optimization of Continuous Encoders for Moment-Based Computation**. The prescribed curve is γ(s)=(φ₁(s),φ₂(s)), the desired function is real-valued F(μγ), and every source input lies in [-1,1].

The extension remains **partially formalized**. The general SDP and its operational optimum over all affine coefficient curves are proved. The analytic rigidity argument, including actual smoothing and propagation from the dense identifying set, is proved from local continuous factorizations. Producing those factorizations from exactness and common-completion identification still requires the unformalized planar topological argument.

The formal `F : ℝ × ℝ → ℝ` is total, but the score and design results use its values and Lipschitz assumption only on the actual attainable set. No convex hull or sampled grid replaces that set.

## Verified statements and their hypotheses

| Paper argument | Principal Lean declaration | Scope |
|---|---|---|
| Affine received sum and K² distance normalization | `Analog.AdditiveStatistics.received_encoder_mean`, `received_squaredDistance` | Arbitrary prescribed planar γ and actual valid K-input lists, K>0. |
| Exact computation by invertible affine encoders | `Analog.AdditiveStatistics.exact_computation_of_det` | Arbitrary real-valued F; nonsingular coefficient matrix. |
| Exact attainable-pair score and equivalent inequalities | `Analog.TwoStatisticDesign.affine_operational_score`, `affine_score_bound_iff` | Nonconstant F on the actual attainable set; includes singular coefficient curves. |
| Positive score implies exact computation | `Analog.TwoStatisticDesign.positive_score_implies_exact` | Arbitrary encoder; nonconstant desired function. |
| Common-completion collision implication | `Analog.CompletionIdentification.triple_collision_preserves_statistics` | K≥4, exactness, identification on B, actual valid triples, and common fillers. |
| Independent interior tangents and actual regular triple statistics | `Analog.GeneralRigidity.independent_tangents`, `regularTripleImage_nonempty`, `regularTripleImage_valid` | Continuity on the closed interval, interior differentiability, and functional independence. |
| Local inverse-function sections and differential kernels | `Analog.GeneralRigidity.pairStatistic_local_section`, `determinant_of_local_fibers` | Genuine independent tangent anchors and actual local statistic-fiber constancy. |
| Automatic encoder regularity from a local continuous factorization | `Analog.EncoderRegularity.contDiffAt_of_triple_factorization` | Source-box factorization; receiver continuous only on its local chart; prescribed curve C¹ at the relevant inputs. The proof constructs the local extension and normalized convolution kernel. |
| Dense identification through endpoint-inclusive affine representation | `Analog.EncoderRegularity.planar_affine_of_dense_charts` | The stated curve and encoder regularity, independence, and density on the actual regular triple image. Continuous local factorizations are assumed only at identifying triples. Encoder differentiability and propagation of derivative identities are derived. |
| Spanning anchors, compact feasible set, and positive attained SDP maximum | `Analog.TwoStatisticAttainment.attained_statistic_maximum` | Continuous independent γ, P>0, and nonconstant Lipschitz F on the attainable set. Anchors, bounds, and positive feasibility are constructed. |
| Positive definiteness from identification | `Analog.TwoStatisticPositivity.positive_feasible_gram`, `localIdentification_of_commonCompletion` | Positive feasible score and the common-completion condition; positive definiteness is no longer an additional design hypothesis. |
| Exact operational realization of an attained SDP optimum | `Analog.TwoStatisticPositivity.general_sdp_operational_attainment` | K≥4 and the preceding design/identification assumptions. Produces a continuous exact peak-admissible planar encoder with score exactly K² times the SDP optimum. |
| Operational optimality over all coefficient curves | `Analog.TwoStatisticPositivity.general_operational_maximum_attained` | All affine coefficient curves are competitors, including singular ones. The theorem does not yet quantify over all continuous encoders. |

`Analog.Operational.quotients_stat_image` and `AttainableScore.lean` establish reindexing of the original pairwise infimum. `GramSynthesis` provides the Schur-complement and planar reconstruction identities. The dense propagation in `GeneralRigidity` uses the local submersion and continuity of derivatives; it does not replace the manuscript's dense condition by identification everywhere.

## Remaining obligations

1. Derive `DensePlanarCharts` from continuity, exact computation, and common-completion identification using planar invariance of domain. This is the remaining interface in the affine-representation converse. The full classification still needs its final nonsingularity/operational assembly for arbitrary continuous F, and the resulting reduction must enlarge the verified coefficient-class optimum to all continuous encoders.
2. Prove the real-analytic sufficient condition for identification and its polynomial characterization.
3. Prove the general endpoint-gradient score specialization, its actual attainable perturbation witnesses, and the connections to the polynomial and nonpolynomial examples. Existing original-family score and quadratic optimization theorems retain their stated scope.

These obligations are not supplied as axioms or silently absorbed into the verified statements. `CONTINUOUS_SCOPE.md` details the topological interface; `COVERAGE.md` records the broader manuscript inventory.

## Reproduce

From `formalization/`:

```sh
lake exe cache get
python3 verify.py
```

The artifact pins Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. A successful run writes declaration dependencies and source hashes to `verification/report.json`. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; unfinished proofs or additional axioms fail verification.
