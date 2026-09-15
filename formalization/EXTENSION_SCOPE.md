# Unified two-statistic extension: formal verification scope

This update accompanies **Geometric Optimization of Continuous Encoders for Moment-Based Computation**, Theorem 4 (`thm:extension`, with legacy alias `thm:polynomial`) and Appendix F. The prescribed curve is γ(s)=(φ₁(s),φ₂(s)), the desired function is real-valued F(μγ), and the source inputs lie in [-1,1].

The formal `F : ℝ × ℝ → ℝ` is a total function whose values are used only on the actual attainable set. A function originally given on that set can be extended arbitrarily outside it; no outside regularity enters these results.

The extension is **partially formalized**. The audit certifies the Lean statements below, including their explicit hypotheses. It does not certify all of Theorem 4.

## New formal statements

| Paper argument | Principal Lean declaration | Exact scope |
|---|---|---|
| Affine received sum | `Analog.AdditiveStatistics.received_encoder_mean` | Arbitrary prescribed planar γ; actual valid K-input lists; K>0. |
| Exactness of invertible affine encoders | `Analog.AdditiveStatistics.exact_computation_of_det` and `exact_computation_of_gram` | Arbitrary real-valued F; nonsingular coefficient matrix. |
| Cancellation of the offset and K² normalization | `Analog.AdditiveStatistics.received_squaredDistance` | Actual channel squared distance equals the coefficient Gram form of empirical-statistic differences times K². |
| Positive score implies exactness | `Analog.TwoStatisticDesign.positive_score_implies_exact` | Arbitrary encoder; nonconstant desired function on the actual attainable set. |
| Common-completion collision implication | `Analog.CompletionIdentification.triple_collision_preserves_statistics` | K≥4, exact computation, and the stated identification condition on B; actual valid triples whose prescribed sums lie in B, and common fillers. |
| Injective scalar transformations preserve identification | `Analog.CompletionIdentification.identifiesOn_postcomp_iff` | Injectivity is an explicit hypothesis; no analytic identification criterion is assumed proved. |
| Exact attainable-pair infimum | `Analog.TwoStatisticDesign.affine_operational_score` | K>0 and nonconstant F on the actual finite-K attainable set; includes degenerate coefficient matrices. |
| Threshold equals all attained-pair inequalities | `Analog.TwoStatisticDesign.affine_score_bound_iff` | K>0 and nonconstant F on the attainable set; all and only attainable pairs, including equal-function-value pairs. |
| Planar peak-feasible reconstruction | `Analog.TwoStatisticDesign.planar_synthesis` | Genuine 3×3 Gram positivity, an explicitly positive-definite lower 2×2 block, and every continuum peak constraint. |
| Operational realization of the reconstructed design | `Analog.TwoStatisticDesign.positive_definite_operational_synthesis` | K>0, continuous γ, nonconstant F on the attainable set, H≽0, explicitly positive-definite lower Gram block, and all peak/pair constraints. Produces a continuous exact encoder and the actual score bound. |

`Analog.Operational.quotients_stat_image` proves equality of the defining quotient sets under attainable-image reindexing. The corresponding score and lower-bound lemmas are in `AttainableScore.lean`. The attainable set is the image of the actual valid K-input configurations under `meanStatistic`; no convex hull, asymptotic moment region, or sampled grid replaces it.

The existing `GramSynthesis` module supplies the Schur-complement and Cholesky identities. The new design module applies those identities to both arbitrary coordinates of γ. It does not infer positive definiteness of G merely from feasibility: that implication is one of the outstanding steps below.

## Remaining obligations

1. Derive the dense local identification hypothesis from the stated real-analytic criterion and its polynomial specialization.
2. Prove local topological factorization using invariance of domain, regularize the continuous encoder, extend derivative relations from the dense identifying set, and integrate to constant affine coefficients for general γ.
3. Prove coefficient nonsingularity, and positive definiteness of every positive feasible Gram block, from local identification.
4. Derive general spanning anchors and positive feasibility, establish compactness of the new pair-constrained feasible set, and prove attained optimality over all continuous encoders.
5. Verify the general endpoint-gradient score reduction and its attainable perturbation witnesses, then connect the existing quadratic coefficient optimizer to the polynomial and nonpolynomial examples.

The original-family score, reconstruction, and attainment results retain their original assumptions. They are not silently promoted to the arbitrary-γ arbitrary-F extension. No missing theorem is supplied as an axiom or an assumed conclusion.

## Reproduce

From `formalization/`:

```sh
lake exe cache get
python3 verify.py
```

The project retains Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. `verification/report.json` records the complete declaration audit and source hashes. The allowed logical dependencies remain `propext`, `Classical.choice`, and `Quot.sound`; unfinished proofs and additional axioms fail verification.
