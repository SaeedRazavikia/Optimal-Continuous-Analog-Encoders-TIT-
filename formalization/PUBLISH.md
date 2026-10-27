# Proof version and provenance

Version 0.4.0 extends the current-manuscript update with full heterogeneous
rigidity, general SDP attainment, Gaussian statistical proofs and general
grid certification. Historical v0.2.0 and v0.3.0 audit and coverage records
are preserved separately.

Use the manuscript, proof sources, audit inventory and `verification/report.json`
from the same repository revision or archive. `manuscript_targets.json` records the exact current ten
statements and manuscript SHA-256. The verification script rejects stale
statement and declaration inventories, checks source stability during the
run, and records source hashes and logical dependencies.

Lean remains pinned to 4.24.0 and mathlib to
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Compiler and dependency caches are
not bundled. The included planar topology proof was ported from a separately
licensed source; its precise commit, adapted dependencies and license are
recorded in the provenance note and accompanying license file.

## Repository and verification

The artifact is maintained at
https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-
in `formalization/`. The repository-root `Main.tex` is the exact current
manuscript used by `check_manuscript.py`. The earlier `manuscript.tex`,
`sections/`, and compiled manuscript files retain their existing revision.

From a checkout with Lean installed, run:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The repository-level `.github/workflows/verify-lean.yml` performs these checks
on proof and `Main.tex` changes. The included `verification/report.json`
records the successful local source-hashed audit. A subsequent GitHub Actions
run has its own status and should be checked on the repository Actions page.
Normal Linux runners do not need the managed-environment runtime adapter.

`COVERAGE.md` defines the exact scope: a passed audit certifies the Lean
statements with their displayed hypotheses, not an unqualified claim that
every sentence of the manuscript has been formalized.
