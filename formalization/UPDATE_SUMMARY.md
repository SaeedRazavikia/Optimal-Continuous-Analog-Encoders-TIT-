# Formalization completion update — 27 October 2026

Version 0.4.0 completes the four proof areas requested after the previous
current-manuscript update. The manuscript itself is unchanged.

## Completed proof areas

| Requested area | Final formal result |
|---|---|
| Full heterogeneous rigidity | `HeterogeneousFullRigidity.heterogeneous_rigidity`: original-hypothesis equivalence for arbitrary continuous node encoders, with common nonsingular columns and separate offsets. Actual completion density, reverse planar factorization, automatic regularity and endpoint integration are derived. |
| General SDP attainment | `HeterogeneousAttainment.heterogeneous_sdp_attained`: attained actual operational and SDP optima, including dependent features, singular feasible blocks and zero optimum. Positivity iff Euclidean Lipschitz readout and unrestricted continuous-class comparison are proved. |
| Gaussian converse proofs | Actual all-Borel fixed-prior and fixed-encoder worst-case limits, changing-Gram lower bounds, singular-limit exclusion, and the optimized identifiable-encoder limit. The constructed fixed encoder and decoder attain the optimum independently of noise power. |
| General grid certification | `HeterogeneousGrid.certified_discretization`: actual node-dependent sampled/continuum optima, derived C2 remainder constants, common scaling, certified bracket, quadratic mesh gap and operational synthesis. Finite PSD matrix dual certificates and unrestricted-class comparison are assembled. |

## Statistical and topological details

The Gaussian risks use nonnegative extended integrals, so infinite-risk Borel
decoders are included correctly. The development proves local Gaussian score
identities and integration by parts, weighted van Trees, smooth compact-test
approximation, the inverse-Gram variational optimum, exact likelihood versus
additive-noise measure identity, local-ball priors, sequential regular and
singular converses, uniform endpoint-decoder achievability, and compact outer
optimization. The physical channel includes the actual node count, giving the
required `1/(2K²)` coefficient; noise power is twice the real-coordinate variance.

The fixed-prior coefficient is identified with the actual matrix-inverse trace.
Every fixed exact globally Lipschitz decoder attains that same prior coefficient.
The optimized worst-case proof derives a nonsingular minimizer of the maximum
inverse-Gram energy and excludes singular limits of competing varying designs.

Planar invariance of domain is proved from an included, adapted no-retraction
and Brouwer proof. Its external source commit and Apache-2.0 license are retained
in `notes/completion-topology.md` and `THIRD_PARTY_LICENSES/`. It is not added as
an axiom or an unproved class premise in the final rigidity theorem.

## Verification and scope

**Passed:** the warning-free full build and `lean --trust=0 Audit.lean`
verified **1,198 public declarations in 100 modules**. This completion adds
**476 declarations in 47 new modules**. Every audited declaration depends
only on `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, new axiom
or admitted proof is present.

The definitive aggregate build, kernel audit, declaration/module totals and
source hashes are recorded in `verification/report.json`. Verification rejects
warnings, stale inventories, altered manuscript correspondence, source changes
during checking and logical dependencies outside the standard allowed axioms.

The previous version audited 722 declarations in 53 modules. Its audit and
coverage records are preserved in `historical/v0.3.0/`; the older version is in
`historical/v0.2.0/`. The original exact-rational numerical certificate remains
unchanged and its successful independent check is retained.

All 58 original files outside `formalization/` were compared byte-for-byte with
the supplied archive and are unchanged. The current ten manuscript statements
and exact manuscript hash remain bound by `manuscript_targets.json`.

This completion concerns the four requested proof areas. `COVERAGE.md` still
identifies separate representation/formula wrappers for the displayed minimum
decoder, specialized score/parabola statements, and the general gradient
sandwich, along with examples and numerical claims not individually formalized.
These are not silently promoted to completed manuscript statements.
