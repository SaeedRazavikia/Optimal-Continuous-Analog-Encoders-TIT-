# Lean proofs for analog moment computation

This artifact accompanies *Optimal Continuous Analog Encoders for Moment-Based Computation*. It contains checked complete results and intermediate results. **The entire manuscript is not yet formalized.** The remaining unrestricted rigidity argument prevents a claim of optimality over every continuous encoder.

The supplied audit records **405 declarations across 29 modules**. All 37
recorded source and configuration hashes match that audit. This count measures
the checked development; it does not mean that all manuscript claims are
covered. See [the theorem map](THEOREM_MAP.md) for the main results,
[the statement inventory](COVERAGE.md) for the manuscript correspondence, and
[the continuous-encoder scope](CONTINUOUS_SCOPE.md) for the open obligations.

## Completed scope

| Component | Checked scope |
|---|---|
| General collision | Actual arbitrary-encoder collision lemma, K≥4, strictly convex or concave mean-dependent term; no differentiability of that term. |
| General operational score | Exact infimum over actual admissible input pairs and shrinking-pair sharpness, for nondegenerate two-feature curves and K≥2. Uses one-sided endpoint derivatives. |
| Actual input paths | Two moving transmitter inputs realize every first-order moment direction at every interior empirical mean. |
| Variance optimization | Complete score including degenerate curves and actual all-quadratic operational optimum for every P>0, K≥2. |
| Quadratic and quartic coefficients | Complete Gram-objective optima for every M>0, P>0, with continuum peak certificates and all coefficient competitors. |
| General operational design | Positive feasible SDP points yield continuous exact peak-feasible encoders with actual score≥K²λ; endpoint independence is derived. |
| SDP attainment | Spanning anchors and a positive feasible point derived from the feature hypotheses; compact continuum feasible set and actual operational maximum over all affine-feature coefficient curves, including degenerate competitors. |
| Rigidity analysis | Native local moment inverses, actual moment neighborhoods, fiber-to-kernel differentiation, endpoint integration, and independence from exactness. Final necessity still assumes local fiber constancy and interior encoder differentiability. |
| Decoding and implementation | Sharp global scalar amplification and zero-score impossibility; actual Euclidean complex variance decoder; coherent mismatch and peak-safe quantization. |
| Small-noise limits | Actual derivative limit, integrable domination, and dominated convergence in noise-power coordinates; actual variance-decoder differentiability and MSE limit; independent isotropic covariance evaluation. |
| Gram frontier | Actual feasible-infimum convexity/monotonicity and strict inverse-risk convexity; attained optimum at every feasible floor including zero, unique optimal Gram, and plateau/activity results with their optimizer witnesses. |

The general score is `Analog.GeneralScore.score`, defined using the paper's actual finite-input channel and target. It is not a stipulated matrix objective. `general_operational_score` identifies it with the endpoint Gram expression, and `general_score_small_distance_sharpness` constructs the required operational witnesses.

`Analog.quadratic_variance_operational_optimal` compares the explicit variance optimizer with every peak-feasible planar quadratic curve. `Curve.PeakFeasibleAt P` quantifies over every real input in `[-1,1]`, not a sample grid. Coefficient-class theorems do not by themselves classify arbitrary continuous competitors.

The probabilistic development proves the real integrated small-noise limit. It does not identify simulation outcomes with kernel-checked theorems, assume a desired limit, or silently replace a general decoder with the variance specialization. See the complete statement inventory in `COVERAGE.md` and the main declarations in `THEOREM_MAP.md`.

No unproved manuscript theorem is introduced as an axiom. The unrestricted continuous reduction still needs topological local factorization and automatic differentiability; `CONTINUOUS_SCOPE.md` describes these obligations. The general decoder-to-trace formula, complete inverse-form frontier, certified-grid theorem, and remaining appendices also need further work.

## Reproduce

Install Lean using its [official instructions](https://lean-lang.org/install/),
then run from this directory:

```sh
lake exe cache get
python3 verify.py
```

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and transitive dependencies through
`lake-manifest.json`. Internet access is needed to obtain the compiler and
those dependencies. Toolchain binaries and third-party source trees are not
bundled. Python requires only its standard library.

`verify.py` builds all imported modules, runs the explicit declaration audit
with `lean --trust=0`, rejects warnings and unexpected axioms, and records the
source hashes. Reports are saved in `verification/`. Its allowlist consists
only of `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` and additional
axioms are rejected. The project does not use `native_decide` or a numerical
oracle to prove the advertised results.

For direct inspection:

```sh
lake build
lake env lean --trust=0 Audit.lean
```

To inspect one result, create `Inspect.lean` in the project root:

```lean
import Analog

#check Analog.quadratic_variance_operational_optimal
#print Analog.GeneralScore.general_operational_score
#print axioms Analog.GeneralScore.general_operational_score
```

Then run `lake env lean Inspect.lean`. `#check` shows the statement and all its
hypotheses; `#print` also shows its definition or proof, and `#print axioms`
shows its logical dependencies. GitHub displays these source files; Lean checks
them locally or in the included continuous-integration workflow. A theorem name
by itself is not a remotely hosted proof-checking service.

The workflow in `.github/workflows/verify.yml` uses the project toolchain and
dependency pins and runs `python3 verify.py`. It is prepared for a new repository;
no successful GitHub run is claimed by the supplied local audit. The optional
`runtime/` files document the environment of that recorded audit and are not
needed for an ordinary Lean installation. Publication steps are in
[PUBLISH.md](PUBLISH.md).

The source-to-manuscript map is as important as successful compilation: Lean
checks the formal statements actually written. Conditional statements and
specializations do not certify the broader original theorem. At zero score,
reciprocal expressions in real-valued definitions use Lean's total division;
the zero-score impossibility theorem supplies the intended infinite-
amplification interpretation, rather than treating that raw value as an
attainable constant.
