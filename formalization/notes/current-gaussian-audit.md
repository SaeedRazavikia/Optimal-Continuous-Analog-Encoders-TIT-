> Historical first-pass mathematical review. Completion work in version 0.4.0
> supersedes its implementation-gap descriptions. See COVERAGE.md, THEOREM_MAP.md
> and the completion notes for the current verified scope.

# Audit of the current decoding and Gaussian estimation results

Date: 2026-10-27. Source: the attached current `Main.tex`, in particular
`prop:radius-minimax`, `thm:identifiable-minimax`, and
`prop:general-small-noise`, and their appendices.

## Change in scope

The previous `COVERAGE.md` entry for `prop:general-small-noise` quotes an
older statement. The current statement minimizes average risk over **all
Borel-measurable decoders** and treats the general target
`ψ₁(m₁) + ψ₂(m₂)`. Existing modules `GeneralSmallNoise.lean` and
`GaussianNoise.lean` establish an actual decoder's leading risk for the
special target `m₂ − ψ(m₁)`, under their displayed derivative, shape,
interiority, and integrability hypotheses. They neither establish the
current arbitrary-decoder converse nor cover every two-statistic target.
The new worst-case minimax theorem is also not a consequence of that old
achievability result.

## Radius-specific minimax result

The new `Analog/RadiusMinimax.lean` gives a stronger algebraic/operational
form of the bounded-radius result: for any bounded real target and received
map into a real normed space, an absolute-error level `e` is achievable at
radius `ρ` if and only if all received pairs within `2ρ` have target
separation at most `2e`. The constructed decoder is the midpoint of the
infimum and supremum of the consistency-fiber target values. The
`radius_minimax` theorem proves that this decoder attains half the pair
modulus and that every decoder's feasible error level is at least that
number. It includes zero radius and does not assume noiseless
identifiability.

For continuous maps on a compact nonempty input space, the module also
proves boundedness of the target, compactness of consistency-value sets
and distance-constrained pair-value sets, and attainment of the pair
modulus. Thus the manuscript's maximum is an actual maximizing pair.
`compact_radius_minimax` expresses the optimum using this pair directly.

The analytic measurability step is also formalized. Projection of a closed
constraint along a compact input coordinate is a closed map. This proves
closedness of the observation sets with a target upper/lower constraint,
from which `upperEndpoint_measurable` and `lowerEndpoint_measurable`
establish Borel measurability (including the chosen value zero at
impossible observations). Finally, `borel_radius_minimax` assembles the
Borel attaining midpoint decoder with a lower bound against every decoder.
There is no remaining proof obligation for the mathematical content of
`prop:radius-minimax` under its continuous compact-input hypotheses.

The module compiled with the pinned Lean 4.24.0 toolchain without warnings.
The final root verification report supplies the complete build and axiom
audit; this local compilation claim is not a substitute for that audit.

## Gaussian proof assessment

No mathematical counterexample to the three current statements was found
in this audit. The following points are essential to the arguments and
must remain explicit in any full formalization:

- The fixed-encoder worst-case theorem uses
  `M_K = closure (interior M_K)`. Linear independence of preprocessing
  functions alone does not imply this property; the manuscript now gives
  a valid counterexample. This assumption transfers localized lower bounds
  to every attainable moment vector.
- Average-risk achievability for a regular moment distribution only needs
  a globally Lipschitz decoder that is exact on the received set. At each
  interior moment vector its local germ agrees with the smooth target
  composed with the affine inverse. The Lipschitz bound supplies an
  integrable squared-noise dominator even near the moment-set boundary.
- The worst-case upper bound requires a uniform expansion, rather than
  merely a pointwise or prior-averaged limit. The linear endpoint extension
  of each `C¹` postprocessing function gives bounded uniformly continuous
  derivatives, making the proposed uniform remainder estimate valid.
- In the van Trees bound, compact support of the test vector field inside
  the positive-density set is essential. It removes boundary terms and
  makes the prior-score term finite without finite global prior Fisher
  information. The proof clips the decoder first, so no decoder derivative
  or unbiasedness hypothesis is required.
- The variational supremum requires density of compactly supported smooth
  vector fields in the relevant weighted `L²` space. Continuity of the
  gradient alone is sufficient after interior cutoffs and smoothing, but
  this approximation argument is not already formalized in the archive.
- Encoder optimization cannot be justified by interchanging an infimum
  and a small-noise limit. The current proof instead establishes a
  sequential lower bound and excludes singular Gram limits using a
  regular auxiliary prior with positive-definite gradient covariance.
  Both ingredients remain necessary formal obligations.
- Compactness in the optimization argument is the compactness of the
  **closed** peak-feasible coefficient class that allows singular matrices.
  The identifiable class itself is not closed; the singular-limit
  exclusion is what puts a minimizing limit back in that class.

## Remaining machine-proof obligations

A complete Lean proof of `prop:general-small-noise` still needs the general
received-set interior derivative bridge, the Gaussian weighted-score
integration-by-parts identity for arbitrary Borel decoders, the weighted
variational density theorem, and the sequential lower-bound argument.
Theorem `thm:identifiable-minimax` additionally needs the uniform
worst-case expansion, localization over interior balls and closure,
positive-definite auxiliary-law construction, singular-limit risk
blow-up, and compact encoder optimization with near-minimizing decoders.

Existing small-noise lemmas provide useful dominated-convergence and
Gaussian-moment components. They must be composed with these missing
steps; their existence does not constitute a proof of the new minimax
claims.
