# Coverage of the current manuscript

This inventory follows the attached **Main.tex**, not the older split-source
manuscript. The current source contains **10** theorem, proposition, and lemma
environments. Stable labels, exact statements, line numbers, and the manuscript
SHA-256 are recorded in `manuscript_targets.json`. Run `python3 check_manuscript.py`
to detect a later manuscript change.

**The manuscript is not fully formalized.** A successful `verification/report.json`
checks the stated Lean declarations. Conditional reductions and special cases do
not prove a more general manuscript statement. Historical v0.2.0 coverage and
its original 673-declaration audit are preserved in `historical/v0.2.0/`.

## Current statements

| Label | Formal coverage | Remaining obligations |
|---|---|---|
| `thm:rigidity` | `HeterogeneousScore` proves the sufficient invertible-coefficient direction and continuity for node-dependent features. `HeterogeneousRigidity` proves common derivative coefficients from explicit determinant identities and four-node anchors, then integrates to node-dependent offsets. Earlier modules supply shared-curve local analysis. | Dense completion separation under the current receiver assumptions, heterogeneous local charts via planar invariance of domain, heterogeneous regularization, and derivation of all derivative/anchor premises from exact computation. The unrestricted necessity theorem is not proved. |
| `thm:sdp` | `HeterogeneousScore.affine_operational_score` and `affine_score_bound_iff` prove the actual heterogeneous input-pair/attained-pair bridge, including singular columns. `SingularGram` reconstructs every PSD block. `HeterogeneousSynthesis.feasible_operational_synthesis` assembles continuous node encoders, all continuum peak bounds, actual score ≥K²λ, and exactness for λ>0, including singular G and λ=0. | Reduced compactness when local features are dependent; attainment including zero optimum; positivity iff Lipschitz; reduction to all continuous encoders through rigidity. The old shared-curve positive-attainment theorem is only a specialization. |
| `prop:amplification` | `Decoder.sharp_uniform_decoder` and `zero_score_no_finite_uniform_decoder` prove the full operational finite/zero-score alternatives for arbitrary input and received maps. No homogeneous-node restriction is needed. | Only notation-level assembly of the extended-real convention; Lean represents the zero-score case as impossibility of every finite bound. |
| `thm:decoder` | `Decoder.pairwise_exists_lipschitz` constructs a real McShane extension; `sharp_uniform_decoder` gives exactness and the optimal uniform constant. These are generic and apply to the current received map. Clipping is checked. | The exact displayed minimum over the current compact moment set is not identified with the library extension in a named theorem. General weighted convex projection is not fully assembled; the existing explicit strip decoder is a special case. |
| `prop:radius-minimax` | `RadiusMinimax.borel_radius_minimax` proves the full compact continuous-input result: a maximizing pair exists, the explicit midpoint decoder is Borel measurable, and its half-modulus error is optimal among all decoders. Radius zero and nonidentifiable encoders are included. | No remaining mathematical gap for this statement. The finite input cube/complex channel is an instance of the more general compact-input/real-normed-space theorem. |
| `thm:identifiable-minimax` | Existing Gaussian moment and pointwise/average dominated-convergence lemmas provide ingredients. | Both the fixed-encoder arbitrary-decoder converse and optimized minimax equality are unformalized. Needed steps include a uniform expansion, localized weighted van Trees bounds, variational density, exclusion of singular limits, and sequential compact optimization. This theorem is not implied by the old decoder achievability result. |
| `prop:general-small-noise` | `GeneralSmallNoise` and `GaussianNoise` prove leading risk of the particular earlier `m₂−ψ(m₁)` decoder under their explicit hypotheses. | General two-postprocessing-function achievability, weighted Gaussian score integration by parts, smooth-test-field density, and lower bound for the infimum over all Borel decoders. The current proposition is not fully formalized. |
| `prop:score` | `GeneralScore.general_operational_score`, `general_score_small_distance_sharpness`, and `MomentPaths` supply the endpoint formula and actual shrinking pairs for the shared-feature specialization, with the written regularity/shape hypotheses. | A direct wrapper from the current node-indexed definitions to the identical-node special case, including the current heterogeneous offsets, remains to be assembled. |
| `thm:parabola` | `GeneralQuadratic`, `PowerScaling`, `Quartic`, and `QuarticPower` prove all-power coefficient-Gram optima. The variance specialization has an assembled actual operational optimum. | General current heterogeneous-encoder comparison and unrestricted continuous-class optimality still require the rigidity assembly; general readout wrappers remain separate. |
| `thm:certifiedgrid` | `CertifiedGrid` proves sharp interpolation, C² estimates, and grid scaling/attainment for the earlier shared curve with two endpoint LMIs. `FiniteCertificates` proves scaling for all nodes and all separations, finite weighted weak-duality arithmetic, and actual PSD trace-product nonnegativity. | Full current node-indexed secant program, common-grid optimizer attainment under its stated assumptions, multi-node spectral remainders, and assembly of the matrix dual certificate. The old one-curve theorem does not alone prove the revised statement. |

Lean namespaces in this table are prefixed by `Analog.`. Consult theorem types,
not names alone: for example, the original `GeneralSmallNoise` name does not
mean arbitrary current two-statistic minimax estimation.

## Additional current claims

- **Gradient sandwich:** the general interior lower bound, convex-superset
  upper bound, and equality for compact convex full-dimensional moment sets
  are not assembled in Lean. The old endpoint localization is a special case.
- **General finite dual witness:** `FiniteCertificates` verifies PSD trace
  nonnegativity, nonnegative weighted inequalities, scaling, and absolute and
  relative gaps. Its scalar weak-duality theorem states the required trace
  inequality and common-block identity explicitly. It does not derive the
  entire current matrix witness from the manuscript's matrix constraints.
- **Numerical exponential certificate:** the exact rational verifier was
  rerun successfully; its command, source hashes, and exact bounds are in
  `verification/numerical-certificate-check.json`. This is independent
  rational arithmetic verification, not a Lean proof of the numerical values.
- **Moment set, output range, counterexamples, and empirical plots:** current
  scope is detailed in the audit notes; these are not all machine-formalized.
- **Older frontier, transfer, and approximate-rigidity developments:** retained
  and included in the declaration audit, but they are not additional numbered
  statements in this version of Main.tex. Their presence must not inflate the
  manuscript coverage count.

## Review conclusions and next proof work

The review did not identify a mathematical counterexample in the current
encoding, decoding, statistical, or certification proofs. This observation
is weaker than machine verification and is not a certification of the paper.
The principal discovered issue was stale correspondence: the old inventory
quoted different assumptions, different decoder formulas, and removed labels.

The remaining work is substantive. Prioritize (1) the heterogeneous SDP
assembly and reduced compactness, (2) the topological rigidity bridge and
heterogeneous regularization, and (3) weighted van Trees and the two new
statistical converse chains. No missing claim is inserted as an axiom.

Detailed audits: `notes/current-rigidity-audit.md`,
`notes/current-score-audit.md`, `notes/current-singular-gram-audit.md`,
`notes/current-gaussian-audit.md`, and `notes/current-design-audit.md`.
