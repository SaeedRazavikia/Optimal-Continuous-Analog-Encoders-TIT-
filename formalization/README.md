# Lean proofs for moment-based computation

This artifact accompanies *Geometric Optimization of Continuous Encoders for Moment-Based Computation*. It contains complete formal results and explicitly conditional steps. **The entire manuscript is not yet formalized.** In particular, the unrestricted continuous-encoder converse still needs a planar topological argument.

The [coverage inventory](COVERAGE.md) records all 17 numbered manuscript statements and additional claims, with their precise formal scope. The [theorem map](THEOREM_MAP.md) identifies principal declarations. See [EXTENSION_SCOPE.md](EXTENSION_SCOPE.md) for the two-statistic extension and [CONTINUOUS_SCOPE.md](CONTINUOUS_SCOPE.md) for the remaining converse dependency.

The supplied full build and kernel audit passed for **673 public declarations in 47 proof modules**, including 231 additions in 14 modules. All 55 recorded source/configuration hashes match the audited files. Counts measure the checked development, not complete coverage of the paper.

## Checked development

| Component | Formal scope |
|---|---|
| Operational computation | Actual finite-input channel, common-completion collision lemmas, attainable-pair score identity, endpoint formula, and shrinking input pairs. |
| General two-statistic design | Functional independence gives anchors; continuity and Lipschitz postprocessing give positive feasibility; common-completion identification gives positive definiteness; compactness gives attained positive operational optimum over all coefficient curves. The actual finite-K attainable set is retained. |
| Rigidity analysis | Actual inverse-function sections, continuous recovery on the compact received set, convolution smoothing with local continuous extension, propagation from the dense identifying set, and integration through endpoints. Local continuous factorizations remain a hypothesis in the final converse component. |
| Explicit coefficient optima | All-quadratic operational variance optimum, general-parameter quadratic and quartic Gram optima, and the quadratic clipped frontier at every positive power and every feasible robustness floor. |
| Decoding and small noise | Actual general corrected strip decoder, exactness, global sharp amplification, derivative and integrated trace formula, a constructed circular Gaussian law, and permitted output clipping. |
| Convex probabilistic design | Attainment, uniqueness, convexity, monotonicity, plateau and activity, continuity at both endpoints, and constructive enclosing-ellipse equivalence. |
| Grid certification | Sharp interpolation bound, actual finite-grid bracketing, sampled and continuum attainment, C² derivative/norm bounds, peak-restoring Gram scaling, and O(h²) scaling loss under fixed anchors. |
| Transfer and approximation | Dissimilarity transfer from actual shrinking pairs; coherent implementation bounds; actual Arzelà–Ascoli compactness and a constructed vanishing approximation modulus, conditional only on exact-class identification for its structural conclusion. |

The general decoder, score and design results concern the actual operational definitions, rather than a matrix objective stipulated to equal them. Coefficient-class optimality does not itself classify all continuous competitors. The unrestricted converse, the extension's analytic identification criterion and general endpoint-gradient specializations, and further claims listed in COVERAGE.md remain unfinished. No missing result is introduced as an axiom.

## Reproduce the audit

Install the pinned Lean toolchain, then run from this directory:

```sh
lake exe cache get
python3 verify.py
```

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and transitive dependencies through `lake-manifest.json`. The compiler and dependency caches are not bundled. Python requires only its standard library.

`verify.py` builds every imported module with warnings rejected, runs the declaration audit with `lean --trust=0`, checks the complete explicit theorem inventory, and records exact source/configuration hashes in `verification/report.json`. Its only permitted logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Unfinished proofs and additional axioms fail verification; no numerical oracle or `native_decide` supplies the advertised results.

For individual inspection:

```lean
import Analog
#check Analog.TwoStatisticPositivity.general_sdp_operational_attainment
#print axioms Analog.EncoderRegularity.planar_affine_of_dense_charts
```

Save these commands to a temporary Lean file and run `lake env lean --trust=0` on it. Inspect the full theorem type, including every hypothesis: successful compilation certifies the written formal statement, not a broader prose claim. At zero separation, Lean's total real division is not an attainable finite amplification; the zero-score impossibility theorem supplies the intended interpretation.

The repository-level verification workflow runs the same audit on relevant pushes and pull requests. Its live [Actions record](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml) is separate from the supplied local audit. The nested workflow is a standalone-project template. The optional runtime directory documents the recorded local environment and is not needed with an ordinary Lean installation. See [PUBLISH.md](PUBLISH.md) for version identity.
