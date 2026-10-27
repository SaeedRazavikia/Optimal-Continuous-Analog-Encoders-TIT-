# Global C¹ endpoint extension

`Analog/EndpointExtension.lean` closes the extension step used in the
manuscript's Gaussian arguments. The construction is explicit:

- `clippedDerivative a b g x = g (max a (min b x))`;
- `extension a b f g x = f(a) + integral from a to x of clippedDerivative`.

The required data are exactly closed-interval continuity of f and its prescribed
derivative g, with `HasDerivAt f (g x) x` only in the open interval. No derivative
of the originally supplied f outside the interval is assumed.

`extension_eq_on` proves agreement throughout the closed interval by the
fundamental theorem of calculus, including both endpoints.
`extension_hasDerivAt` identifies the derivative at every real point.
`extension_contDiff` derives global C¹ regularity.
`clippedDerivative_bounded` and `clippedDerivative_uniformContinuous` follow
from compactness of the interval and the nonexpansive clamp.

`exists_global_extension` assembles these into an existence theorem for a
nondegenerate interval. Downstream Gaussian arguments may apply it to each
receiver postprocessing function, then compose the two extensions with the
moment coordinates. The formalization does not silently replace the original
closed-interval hypotheses by a global smoothness assumption.

The module compiles without warnings with the pinned Lean/mathlib versions.
