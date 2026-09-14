# Continuous-encoder formalization: remaining scope

Status: **incomplete**. This release does not establish optimality over all
continuous encoders and does not formalize every proof in the manuscript.
The theorem map and verification reports identify the declarations actually
checked in this release. The material below documents the outstanding
dependency chain; it is not an additional formal proof.

## The topological dependency

The manuscript's continuous rigidity argument uses planar invariance of
domain: a continuous injection on an open subset of the real plane has open
image. A Lean statement of the required result is:

```lean
∀ (B : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → (ℝ × ℝ)),
  IsOpen B → ContinuousOn f B → Set.InjOn f B →
  IsOpen (f '' B)
```

This is a specification of an outstanding result, not a declaration proved
by this project. Applying it to every open subset of the domain gives the
open-map property needed by `Analog.open_slice_fiber_constancy`. That theorem
states openness explicitly as a hypothesis; it does not derive openness
from continuity and injectivity. The recovery map need not be continuous.

No applicable invariance-of-domain theorem was located in the inspected
mathlib v4.24.0 source tree, pinned at
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, or in the current official mathlib
sources and documentation inspected on 2026-09-13. The inspection included
the current declaration index with 425,006 declarations and the 8,532-line
`Mathlib.lean` import index. Searches covered invariance of domain, open
injections, Borsuk–Ulam, Brouwer, Jordan curves, winding numbers, sphere
noncontractibility, and invariance of dimension. This finding does not assert
that no suitable formalization exists elsewhere or that such a proof is
impossible.

Several superficially relevant results do not supply this dependency:

- `ContinuousLinearMap.isOpen_injective` proves openness of the *set of
  injective continuous linear maps*, not openness of their images under an
  arbitrary continuous injection.
- `IsLocalHomeomorph.isOpenEmbedding_of_injective` already assumes a local
  homeomorphism.
- `IsLocallyInjective_iff_isOpenEmbedding` concerns a pullback diagonal map.
- The inspected `SmallInductiveDimension` module defines dimension and basic
  invariance properties; it does not prove the required Euclidean result.

Introducing invariance of domain as an unproved axiom would produce only a
conditional development and would not complete the claimed verification.

## Available analysis infrastructure

The pinned mathlib version contains the following building blocks:

| Step | Declarations | Module under `Mathlib/` |
|---|---|---|
| Smooth local inverse | `ContDiffAt.toOpenPartialHomeomorph`, `ContDiffAt.localInverse`, `ContDiffAt.to_localInverse` | `Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean` |
| Local moment fibers | `HasStrictFDerivAt.implicitFunction`, `HasStrictFDerivAt.map_implicitFunction_eq`, `HasStrictFDerivAt.to_implicitFunction` | `Analysis/Calculus/Implicit.lean` |
| Smooth convolution | `HasCompactSupport.contDiff_convolution_right`, `HasCompactSupport.contDiff_convolution_left` | `Analysis/Convolution.lean` |
| A smooth density of integral one | `ContDiffBump.integral_normed` | `Analysis/Calculus/BumpFunction/Normed.lean` |
| Constancy on a connected set | `IsLocallyConstant.apply_eq_of_isPreconnected` | `Topology/LocallyConstant/Basic.lean` and its imports |

The local inverse-function applications are now formalized in `RigidityCompletion`: they provide differentiable local sections and actual open neighborhoods of realizable moments. The original C1/nonaffine assumptions supply the required derivative anchors. Exactness then forces coefficient independence for affine-feature encoders.

`RigidityAnalysis` derives the differential-kernel relations from actual local moment-fiber constancy, integrates through the closed interval endpoints, and combines the representation with coefficient independence. Its main theorem `rigid_representation_of_local_fibers` retains exactly the two unfinished analytic conclusions as explicit hypotheses: interior encoder differentiability and local moment-fiber constancy.

What remains is to derive local moment factorization from continuity and exactness using planar topology, and then derive encoder differentiability by localized smoothing. In particular, the convolution identity, cutoff localization, and resulting regularization still require formal proofs. Merely having convolution and inverse-function APIs does not discharge those obligations.

## What completes the requested claim

The operational variance infimum, exact score identity, arbitrarily small
received-distance sharpness, and power/terminal-count scaling for P > 0 and K >= 2
are now checked for every planar quadratic curve. The combined theorem
`Analog.quadratic_variance_operational_optimal` gives the actual operational
optimum over that coefficient class. To extend its competitors to all
continuous encoders, the project still needs the complete rigidity reduction
and its connection to the formal channel definitions. The topological and regularization steps above remain real proof obligations;
they cannot be filled by importing the desired theorem as an assumption.

Verifying that chain would still not justify saying that *all proofs in the paper* are formalized. The full general operational score is now checked, along with constructive operational synthesis, SDP compactness/maximum attainment, the probabilistic limiting argument, and substantial Gram-frontier results. Remaining obligations include the general decoder gradient-to-trace specialization, the complete inverse-form probabilistic frontier and its continuity, numerical certification, the polynomial extension, and approximate rigidity. The complete current inventory is `COVERAGE.md`; new component results must not be mistaken for the remaining universal statements.

## Official sources inspected

- [Pinned mathlib source](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7)
- [Current import index](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib.lean)
- [Current declaration index](https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp)
- [Local homeomorphisms](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/IsLocalHomeomorph.html)
- [Separated maps and pullback diagonals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/SeparatedMap.html)
- [Small inductive dimension](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/SmallInductiveDimension.html)
- [Smooth inverse function theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.html)
- [Convolution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convolution.html)

The links to current documentation can change after the inspection date;
the reproducible artifact uses the pinned revision above.
