# Lean proofs for analog moment computation

This artifact accompanies *Geometric Optimization of Continuous Encoders for Moment-Based Computation*. It contains checked complete results and intermediate results. **The entire manuscript is not yet formalized.** The remaining unrestricted rigidity argument prevents a claim of optimality over every continuous encoder.

The supplied audit verifies **442 declarations across 33 modules**, including
37 declarations in the four new extension modules. All 41 recorded
source/configuration hashes match the audited files in `verification/report.json`.
These counts measure the checked development; they do not mean that all manuscript claims are
covered. See [the theorem map](THEOREM_MAP.md) for the main results,
[the statement inventory](COVERAGE.md) for the manuscript correspondence, and
[the continuous-encoder scope](CONTINUOUS_SCOPE.md) for the open obligations.

## Scope of the unified extension

The manuscript now states Theorem 4 for arbitrary prescribed additive statistics
`γ = (φ₁, φ₂)` and a real-valued postprocessing function `F`. The new modules are
`AdditiveStatistics`, `AttainableScore`, `CompletionIdentification`, and
`TwoStatisticDesign`. They cover affine-channel identities and exactness,
reindexing the operational score over the actual finite-`K` attainable set,
the common-completion collision implication under its stated identification
hypothesis, and constructive peak-constrained design with an explicitly
positive-definite lower Gram block. `EXTENSION_SCOPE.md` maps each step to its
formal declaration and lists the remaining obligations.

These results do not complete the generalized continuous-encoder converse,
derive positive definiteness from local identification, establish the new
compactness/attainment argument, or verify the real-analytic and endpoint-gradient
specializations. The original two-moment score and design theorems below retain
their original hypotheses.

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

This revision extends repository commit
`7a513ed38147a73f109f9b184dafba59c17ee89b`. Use the proof sources and recorded
hashes from the same revision to reproduce the audit. `PUBLISH.md` describes
version identity and the distinction between the local audit and GitHub CI.

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

The proof sources for this revision are in [Analog/](Analog/) and [Analog.lean](Analog.lean).
Run the commands above from its `formalization/` directory. The repository-level
[verification workflow](../.github/workflows/verify-lean.yml) uses the pinned
Lean toolchain and mathlib revision and runs `python3 verify.py` on relevant
pushes and pull requests. The nested `.github/workflows/verify.yml` is the
standalone-project template supplied with the archive. The recorded local audit
and a GitHub run are separate verification records; see the repository's
[Actions page](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml) for remote status.
The optional `runtime/` files document the environment of the recorded local
audit and are not needed for an ordinary Lean installation. Citation and
reproduction guidance is in [PUBLISH.md](PUBLISH.md).

The source-to-manuscript map is as important as successful compilation: Lean
checks the formal statements actually written. Conditional statements and
specializations do not certify the broader original theorem. At zero score,
reciprocal expressions in real-valued definitions use Lean's total division;
the zero-score impossibility theorem supplies the intended infinite-
amplification interpretation, rather than treating that raw value as an
attainable constant.

