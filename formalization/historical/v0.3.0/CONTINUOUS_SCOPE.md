# Remaining continuous-encoder converse

The current `Main.tex` theorem `thm:rigidity` permits node-dependent feature
curves and encoders. The unrestricted necessity statement is **not yet proved
in Lean**. Older shared-curve conclusions cannot be promoted to this theorem.

New `HeterogeneousRigidity` results derive common scalar derivative coefficients
from explicit determinant relations at distinct-node anchors and integrate
node-indexed derivative identities through the closed source interval. New
`HeterogeneousScore` proves continuity and the sufficient exactness direction
when the common coefficient columns are invertible.

The complete necessity chain still needs:

1. The current dense completion-separation argument for receiver functions that
   are affine everywhere or nonaffine on every open interval.
2. Heterogeneous local inverse sections and reverse local factorization through
   planar invariance of domain. Continuous recovery in the opposite direction
   is not enough.
3. Heterogeneous regularization from those factorizations.
4. Derivation of all determinant and independent-anchor hypotheses, followed
   by nonsingularity and the final theorem assembly.

The existing shared-curve `GeneralRigidity`, `EncoderRegularity`,
`RigidityAnalysis`, `RigidityCompletion`, and `PlanarTopology` modules remain
useful and audited. They have their original formal hypotheses. None silently
provides the missing current topological or heterogeneous interfaces.

See `notes/current-rigidity-audit.md` for the mathematical review, and
`COVERAGE.md` for how this gap affects unrestricted optimality claims.
