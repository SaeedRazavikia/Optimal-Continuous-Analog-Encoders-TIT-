# Proof version and provenance

Version 0.3.0 updates correspondence to the supplied current Main.tex, adds
node-dependent operational results, all-rank Gram reconstruction, bounded-noise
minimax decoding, and finite certificate components, and preserves historical
v0.2.0 evidence separately.

Use the manuscript, proof sources, audit inventory, and verification/report.json
from the same archive. The current manuscript SHA-256 and exact ten statements
are in manuscript_targets.json. The verification script rejects stale statement
and declaration inventories and records source hashes and theorem dependencies.

The toolchain remains pinned to Lean 4.24.0 and mathlib
f897ebcf72cd16f89ab4577d0c826cd14afaafc7. Compiler and third-party caches are not
bundled. This archive is a local update; no remote repository commit, push, or
new GitHub Actions run is claimed. Any older manuscript/repository commit link
does not identify these newly added proofs.

COVERAGE.md defines the actual scope. A successful audit certifies all included
Lean declarations, not every theorem of the current paper. Major remaining
obligations include the full heterogeneous rigidity and attainment assemblies
and the new Gaussian statistical lower bounds.
