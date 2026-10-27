# Lean proofs for the current moment-based encoder manuscript

This folder accompanies the supplied **Main.tex**, *Geometric Optimization of
Continuous Encoders for Moment-Based Computation*. Version 0.4.0 extends the
formalization for node-dependent preprocessing, arbitrary continuous encoders,
general SDP design, Gaussian estimation and certified discretization.

The [coverage inventory](COVERAGE.md) tracks the current **10** numbered
statements, including remaining formula-level specialization wrappers.
[THEOREM_MAP.md](THEOREM_MAP.md) lists the principal declarations and proof
chains. Exact manuscript statements and the source fingerprint are recorded
in [manuscript_targets.json](manuscript_targets.json).

## Main proof developments

- **Heterogeneous rigidity:** the original-hypothesis equivalence, including
  nonsingular common columns and separate offsets, with physical completion
  density, automatic regularity and a proved planar topology argument.
- **General SDP attainment:** dependent feature families, singular feasible
  Gram blocks and zero optimum; positivity iff Euclidean Lipschitz readout;
  global continuous-encoder optimality under rigidity.
- **Gaussian estimation:** genuine nonnegative risks over all Borel decoders,
  local-prior information bounds, smooth-test variational completeness,
  changing-design and singular-limit converses, endpoint-decoder achievability,
  and actual Gaussian-law/model/coefficient identification.
- **General grid certification:** node-dependent continuum/sample programs,
  attained optima, C2 scaling certificates, quadratic mesh gaps and actual
  finite PSD matrix dual witnesses.

The earlier bounded-noise minimax theorem, all-rank reconstruction, operational
scores and explicit-design proofs are retained. [UPDATE_SUMMARY.md](UPDATE_SUMMARY.md)
records the completion status and verification totals. Historical evidence is
preserved in `historical/v0.2.0/` and `historical/v0.3.0/`; those inventories do
not describe current coverage.

The full warning-free build and `--trust=0` audit passed for **1,198 public
proof declarations in 100 modules**, including **476 new declarations in
47 new modules** in this completion update. The only logical axioms are
`propext`, `Classical.choice` and `Quot.sound`; there are no admitted proofs.

## Reproduce verification

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and transitive revisions through
`lake-manifest.json`. From the repository root, with this toolchain installed, run:

```sh
cd formalization
lake exe cache get
python3 check_manuscript.py
python3 update_audit.py --check
python3 verify.py
```

`verify.py` builds every imported module with warnings rejected, invokes
`lean --trust=0 Audit.lean`, checks the exact declaration inventory and permits
only `propext`, `Classical.choice` and `Quot.sound`. The result, declaration
count and exact proof-source hashes are in `verification/report.json`.
Failed runs record failure rather than retaining a stale passing status.
Successful verification certifies the Lean statements with their hypotheses.

After proof changes, run `python3 update_audit.py` before verifying. After a
manuscript revision, review the mathematics and coverage before running
`python3 check_manuscript.py --update`; recording correspondence is not a proof.

The unchanged exact rational numerical certificate has its own check:

```sh
python3 ../code/certified_synthesis.py --verify-only
```

Compiler and dependency caches are not bundled. The optional `runtime/`
directory describes the executable-path adapter used in the managed checking
environment; ordinary Linux installations do not need it. The ported planar
topology sources include their license and precise external provenance.
