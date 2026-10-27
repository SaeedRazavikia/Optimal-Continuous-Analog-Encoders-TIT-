# Node-dependent operational score audit

The current `Main.tex` uses separate preprocessing functions and offsets at
each node, with shared encoder columns. The archived `AdditiveStatistics.lean`
and `TwoStatisticDesign.lean` instead use one preprocessing curve and one
encoder on lists of inputs. Their source statements do not directly formalize
the current heterogeneous model.

`Analog/HeterogeneousScore.lean` now defines actual source tuples
`Fin K → ℝ`, the admissible cube, node-dependent feature curves
`γ : Fin K → ℝ → ℝ × ℝ`, distinct offsets `c`, their empirical means, and the
actual multiple-access received sum. Its attainable set is exactly the image
of the admissible cube. No closure or convex hull replaces this set.

The module reuses the four column coordinates of `GramSynthesis.Planar`.
Its two constant offset coordinates are unused; the separately supplied `c`
contains every node's offset.

| Declaration in `Analog.HeterogeneousScore` | Statement and hypotheses |
|---|---|
| `meanStatistic_mem_attainable` | Every admissible tuple gives an attainable moment vector. |
| `received_encoder` | Expands the actual finite received sum into the sum of the distinct offsets and the shared columns times the unnormalized statistic sums. |
| `received_encoder_mean` | Derives the manuscript's normalized aggregate formula when `0 < K`. |
| `received_squaredDistance` | Derives the exact `K²` Gram-distance formula when `0 < K`; singular common columns are permitted. |
| `collision_preserves_mean` | Nonzero common-column determinant makes received collisions preserve both moments. |
| `exact_computation_of_det` | An invertible common-column matrix permits exact computation of every readout of the two moments. This is the sufficient encoding direction. |
| `encoder_continuousOn` | Each continuous local preprocessing curve gives a continuous local encoder. |
| `affine_operational_score` | For `0 < K` and a nonconstant readout on the actual attainable set, the true input-pair infimum is `K²` times the true attainable-pair Gram infimum. |
| `affine_score_bound_iff` | Under the same hypotheses, the exact score threshold is equivalent to all attained-pair inequalities in the current program. |
| `positive_score_implies_exact` | For arbitrary heterogeneous encoders and a nonconstant readout, positive actual score implies exact computation. |

The nonconstancy hypothesis ensures that the quotient set defining the real
infimum is nonempty. The algebraic score and collision arguments require no
continuity, differentiability, or local functional independence. The readout
may be any function of the two prescribed means, so the manuscript's sum of
two receiver postprocessing functions is included.

These statements supply the heterogeneous operational score bridge used in
the current SDP proof. They do **not** establish the following remaining
steps of the current theorems:

- the necessity of the heterogeneous affine encoder representation;
- attained-optimum SDP assembly (separate `SingularGram` and
  `HeterogeneousSynthesis` modules now prove all-rank reconstruction and
  constructive synthesis from every feasible point);
- compactness or attainment with dependent preprocessing functions;
- the equivalence between positive optimum and Lipschitz readout;
- global optimality over all continuous encoder collections.

Validation status is recorded in the project-level verification report.
This note does not independently certify compilation or kernel checking.
