# Lean proofs for the current moment-based encoder manuscript

This folder accompanies the supplied **Main.tex**, *Geometric Optimization of
Continuous Encoders for Moment-Based Computation*. The manuscript now allows
node-dependent preprocessing and offsets and includes new bounded-noise and
Gaussian minimax results. **The whole manuscript is not yet formalized.**

The current [coverage inventory](COVERAGE.md) tracks all **10** numbered
statements and identifies exact formal scope. The exact statement text and
source fingerprint are in [manuscript_targets.json](manuscript_targets.json).
The original source files and their prior audit were checked for consistency;
old coverage/report files are retained in [historical/v0.2.0](historical/v0.2.0).
They do not describe the current manuscript's theorem coverage.

## What this update adds

- `HeterogeneousScore.lean`: actual finite node-indexed inputs, distinct local
  features and offsets, aggregate and Gram-distance identities, operational
  score equivalence, and sufficient exactness. Singular columns are allowed
  in the score theorems.
- `SingularGram.lean`: planar reconstruction for every positive-semidefinite
  block, including singular lower blocks, preserving distances and decreasing
  transmitted power. It uses explicit scalar factorizations.
- `HeterogeneousSynthesis.lean`: assembles feasible common-Gram SDP points into
  actual continuous node encoders with the operational score guarantee, including
  singular Gram blocks and zero score.
- `HeterogeneousRigidity.lean`: distinct-node derivative algebra and integration
  with common coefficients and separate offsets, under explicit derivative
  identities and anchor hypotheses.
- `RadiusMinimax.lean`: a consistency-midpoint decoder and exact bounded-noise
  minimax error against all decoders, including zero radius, with maximum
  attainment and a Borel-measurable decoder for compact continuous input models.
- `FiniteCertificates.lean`: PSD trace-product nonnegativity, finite weighted
  dual bounds, scaling, and certificate gaps, with unassembled matrix identities
  kept explicit.

The full current rigidity converse, general heterogeneous SDP attainment, and
Gaussian minimax/Bayes lower bounds remain incomplete. Existing small-noise
achievability theorems do not prove an infimum over arbitrary decoders.
See [UPDATE_SUMMARY.md](UPDATE_SUMMARY.md), [THEOREM_MAP.md](THEOREM_MAP.md),
and the individual audit notes.

The completed full build and `--trust=0` axiom audit passed for **722 public
declarations in 53 modules**, including **49 new declarations in six modules**.
Only `propext`, `Classical.choice`, and `Quot.sound` occur as logical dependencies.

## Reproduce verification

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and all transitive revisions
through `lake-manifest.json`. With this toolchain installed, run:

```sh
lake exe cache get
python3 check_manuscript.py
python3 update_audit.py --check
python3 verify.py
```

`verify.py` builds every imported module with warnings rejected, invokes
`lean --trust=0 Audit.lean`, checks the exact declaration manifest, and permits
only `propext`, `Classical.choice`, and `Quot.sound`. Its current result and exact
source hashes are in `verification/report.json`; failed runs record failure
rather than leaving a stale passing report. Successful compilation certifies
the written Lean statements, including all their hypotheses.

After intentional proof changes, run `python3 update_audit.py` before verifying.
After a manuscript revision, review the changed mathematics and coverage first,
then run `python3 check_manuscript.py --update`. That command records source
correspondence; it does not prove the new statements.

The rational numerical certificate has its own reproducible command:

```sh
python3 ../code/certified_synthesis.py --verify-only
```

The toolchain and dependency caches are not bundled. The optional `runtime/`
directory documents the executable-path compatibility adapter used in the
managed verification environment; ordinary Linux installations do not need it.
