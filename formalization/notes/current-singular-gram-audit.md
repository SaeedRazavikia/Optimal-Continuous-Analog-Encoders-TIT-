# Singular Gram reconstruction for the current manuscript

Source: `Main.tex`, proof of `thm:sdp`, Step 2 (rank-two reconstruction and zero relaxation gap).

`Analog/SingularGram.lean` proves the generalized planar reconstruction for
**every** `PSD3 h l₁ l₂ A B C`, including singular and zero lower blocks.
It uses explicit scalar Cholesky formulas and rank cases instead of a
Moore–Penrose inverse. This is a constructive alternative proof of the
reconstruction properties used in the manuscript; it does not assert equality
with the manuscript's chosen symmetric square-root realization.

The public results are:

- `Analog.SingularGram.reconstructPSD_gram`: preserves both cross entries and
  all three entries of the lower Gram block, with offset squared norm at most h.
- `Analog.SingularGram.reconstructPSD_energy_le`: the reconstructed planar
  energy is at most the original quadratic form at **every** feature vector.
  Consequently every continuum peak constraint is retained.
- `Analog.SingularGram.reconstructPSD_common_columns`: with a shared lower
  block, the two reconstructed feature columns are identical for all node
  offsets. Node-dependent translations therefore introduce no compatibility gap.

The proof derives the singular cross-term range restriction directly from
nonnegativity of the full three-variable form. It does not assume that range
restriction, a Schur bound, or a pre-existing planar realization.

This module discharges the rank-reduction portion of the generalized SDP
argument. It does **not** prove compactness after projection onto the span of
local feature variations, attainment of the heterogeneous optimum, the
Lipschitz equivalence, or unrestricted continuous-encoder rigidity.

Validation: the module compiled without warnings with the project's pinned
Lean 4.24.0 and mathlib revision. The aggregate `verification/report.json`
records the final whole-project kernel/axiom audit status.

## Assembly with the actual heterogeneous operational model

`Analog/HeterogeneousSynthesis.lean` now combines this reconstruction with
`HeterogeneousScore`.

`Analog.HeterogeneousSynthesis.feasible_operational_synthesis` takes any
node-indexed family of PSD Gram forms with a shared lower block, all original
continuum peak constraints, and all secant constraints on the **actual**
finite-node attainable set. It constructs common columns and node-specific
offsets, proves continuity of each encoder from continuity of each feature
curve, retains every peak bound, and proves actual operational score at least
K²λ. The result allows singular G and λ=0; when λ>0 it additionally derives
exact computation from the operational score. No positive-definiteness or
feature-independence hypothesis is imposed.

Together with `HeterogeneousScore.affine_score_bound_iff`, this supplies the
operational/reconstruction bridge in Steps 1–2 of the current SDP proof.
Attainment in Step 3 and the Lipschitz characterization in Step 4 are still
not established by these modules. The assembly module also compiled without
warnings with the pinned toolchain.
