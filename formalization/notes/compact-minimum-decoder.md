# Theorem 3: the displayed compact-moment minimum

`Analog.CompactMinimumDecoder.heterogeneous_minimum_decoder` proves the
manuscript's particular minimum formula, rather than only existence of some
Lipschitz extension. `momentDecoder` is the infimum over the actual finite-node
attainable set of the target plus the sharp constant times the Euclidean
distance to the affine received point. Compactness and continuity give an
attaining moment for every observation.

The generic `compactMinimum_lipschitz` compares the minimum at two observations
using a minimizing moment at the second observation and the distance triangle
inequality. `compactMinimum_exact` uses the operational pairwise bound and the
candidate supplied by the true moment to prove equality on every noiseless
received point. `compactMinimum_sharp` then applies the already verified
reciprocal-root score theorem to prove optimality against all competing decoders.

The finite-node wrapper proves that the moment-channel quotient set equals the
physical input-pair quotient set. The channel retains the sum of the individual
offsets and the factor `K` multiplying the normalized moment map. Distances are
computed in the complex plane, so they are exactly Euclidean distances, not the
default maximum metric on pairs of reals. No determinant, inverse-channel,
injectivity, or differentiability hypothesis is used: singular coefficient
matrices are included whenever their actual operational score is positive.

`momentConstant_eq` identifies the constant with the reciprocal square root of
the heterogeneous operational score. The terminal theorem proves attainment,
global Lipschitz continuity, the all-input/all-complex-noise error inequality,
and minimality over every decoder with a finite uniform error constant.
