# Completed planar topology and reverse factorization

The local reverse-factorization step now has a kernel-checked proof. In
particular, `Analog.PlanarInvariance.isOpen_image` proves the ordinary planar
invariance-of-domain statement:

```text
f : (ℝ × ℝ) → (ℝ × ℝ), U open,
ContinuousOn f U, InjOn f U → IsOpen (f '' U).
```

Its theorem type has no Brouwer, no-retraction, invariance-of-domain, local
chart, or other additional topological premise. The product plane uses its
ordinary product topology. The proof first establishes the theorem for the
ordinary Euclidean plane and transports it through the standard
homeomorphism to `ℝ × ℝ`.

## Provenance and retained source

The external source is
<https://github.com/mccorvie/classification-of-surfaces>, exact commit
`e3c7230fe78d7b056a415d9ecae6f77887046b32`. That source uses Lean 4.32.0 and
mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. Its Apache 2.0 license
is retained at
`THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE`.

The adapted source pieces are:

- `ClassificationOfSurfaces/Moise/NoRetraction.lean`, through
  `no_retraction_planeClosedUnitBall`. The subsequent triangle and general
  retraction results are not imported or retained.
- `ClassificationOfSurfaces/Moise/Brouwer.lean`, through
  `brouwer_fixed_point_planeClosedUnitBall`. These two pieces are retained in
  `Analog/PlanarBrouwer.lean`, preserving their contributor copyright and
  attribution.
- `ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`, through
  `invariance_of_domain_open_map`, retained in
  `Analog/PlanarInvarianceCore.lean`. The manifold-boundary and general chart
  API after that theorem is not retained. The original attribution to Steven
  Sivek and Kai Lam is preserved. The upstream file identifies Kai Lam's
  mathlib PR #36770, commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7`, as the
  source of the invariance-of-domain argument.

The original local import closure contains 12 repository modules and 14,331
source lines. Inspection found no added axioms, admitted proofs, native
decision proofs, or unsafe declarations in that closure. The retained proof
has a much smaller dependency footprint: the unrelated polygon, triangle,
triangulation, and manifold developments are excluded entirely.

## Port and proof chain

The proofs were ported to this archive's pinned Lean 4.24.0 environment,
with mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Changes to the retained arguments consist of namespace and explicit type
annotations, renamed topology/API lemmas, and replacements of newer tactic
steps by explicit inequalities, rewrites, and injectivity proofs. Examples
include `LocallyPathConnectedSpace` versus the pinned
`LocPathConnectedSpace`, `push Not` versus `push_neg`, a closed-intersection
lemma name, and explicit arguments where newer `grind` or `positivity`
behavior is unavailable. The underlying no-retraction, ray-intersection,
and perturbation proofs remain the same mathematical arguments.

One genuinely missing library result required a new direct proof:
`Analog.PlanarBrouwer.circle_exp_isCoveringMap`. Pinned mathlib proves that
the circle exponential is a local homeomorphism, but does not yet provide
its covering-map theorem. The new proof derives discreteness of the kernel
from that local homeomorphism and constructs each local trivialization
explicitly. With a local section `s` on an open set `U`, the maps are

```text
exp⁻¹(U) → U × ker(exp),  x ↦ (exp x, x − s(exp x))
U × ker(exp) → exp⁻¹(U),  (y,k) ↦ s(y) + k.
```

Both inverse identities and both continuity statements are proved. This
uses pinned mathlib directly; no newer covering-map framework is imported.
The arbitrary real lift of a circle point is supplied by `Complex.arg` and
the existing `Circle.exp_arg` theorem.

The complete topology chain is:

1. The complex closed unit disk is contractible and locally path connected.
   A hypothetical retraction onto the circle would lift through the circle
   exponential. Uniqueness of path lifts then contradicts the boundary
   loop's change of argument by `2π`.
2. The ordinary linear isometry between `EuclideanSpace ℝ (Fin 2)` and `ℂ`
   transports this no-retraction theorem to the Euclidean closed unit ball.
3. A continuous fixed-point-free self-map of that ball would give a
   retraction by following the ray from `f x` through `x` to the sphere.
   The positive quadratic root, its continuity, and the boundary identity
   are all proved, yielding the actual Brouwer fixed-point theorem.
4. The generic invariance-of-domain proof uses Tietze extension,
   differentiable approximation, and a measure-theoretic perturbation
   argument. Its generic `BrouwerFixedPoint E` class is an explicit premise
   in the generic core. The plane instance in `Analog/PlanarInvariance.lean`
   is constructed from the proved fixed-point theorem; it is not an axiom
   or an instance supplied by the user.
5. Planar invariance of domain makes the image of each continuous injective
   planar slice open. A collision implication identifying the moment
   parameter then forces the received value to be locally constant along
   the remaining connected fiber. Connectedness gives fiber constancy.
6. `local_factorization_of_coordinates` applies this argument to an actual
   open partial homeomorphism with one real fiber coordinate and two moment
   coordinates. It constructs source and moment neighborhoods and a
   continuous function `H` satisfying `R x = H (M x)` locally.

## Audit of the actual heterogeneous chart

`HeterogeneousCoordinates.coordinates_localHomeomorph` constructs the actual
coordinate map

```text
(x,y,z) ↦ (x, tripleStatistic a b c d e f (x,y,z))
```

from C¹ feature curves and the nonzero determinant of the last two feature
tangents. Its derivative is an invertible triangular continuous linear
map, and the chart comes from the inverse function theorem. It is not a
supplied chart encoding the desired conclusion.

`HeterogeneousLocalCharts.heterogeneous_local_chart` takes continuous feature
and encoder curves on the closed source intervals, C¹ feature regularity at
an interior triple, a regular last pair, and the local implication

```text
equal partial received sums → equal partial feature statistics.
```

It proves the reverse local factorization on an actual product of three
source neighborhoods, through a continuous planar `H`. It does not assume
encoder differentiability, continuity of a decoder or moment-recovery map,
injectivity of the full three-dimensional source map, or reverse
factorization itself. The collision implication is an explicit
application-specific premise, discharged separately by the actual
completion-identification results; it is not a hidden topological axiom.

`HeterogeneousNonsingularity.determinant_ne_zero_of_local_recovery` also
constructs an open moment slice of an actual chart and derives nonzero
common coefficient determinant from an affine encoder formula and the
local recovery implication.

## Kernel validation

The adapted and new modules compile under the pinned toolchain. Independent
`--trust=0` checks of the assembled wrapper, including an example with
exactly the ordinary planar open-image hypotheses above, pass.

Independent `#print axioms` checks for all of the following report only
`[propext, Classical.choice, Quot.sound]`:

- `PlanarBrouwer.circle_exp_isCoveringMap`;
- `PlanarBrouwer.no_retraction_closedUnitDisk`;
- `PlanarBrouwer.no_retraction_planeClosedUnitBall`;
- `PlanarBrouwer.brouwer_fixed_point_planeClosedUnitBall`;
- `PlanarInvariance.isOpen_image`;
- `PlanarInvariance.local_factorization_of_coordinates`;
- `HeterogeneousLocalCharts.heterogeneous_local_chart`.

The last three theorem types were also printed and inspected independently.
They contain no remaining Brouwer or invariance-of-domain class premise.
This closes the previously identified topology obstruction; the full
original-hypothesis rigidity assembly is documented by its own final
theorem and coverage entry.
