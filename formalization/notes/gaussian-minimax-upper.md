# Actual Gaussian minimax upper bound

`Analog/GaussianMinimaxUpper.lean` connects the previously proved uniform
Gaussian asymptotics to `GaussianWorstCase.minimaxRisk`, the actual infimum
over all Borel decoders of the nonnegative worst-case conditional risks.

`pointRisk_constructed` proves equality of the actual likelihood-based
conditional ENNReal risk and the endpoint decoder's additive-Gaussian real
risk. Its finiteness is derived from the decoder Lipschitz bound and Gaussian
second moment. The conditional measure identity is supplied by
`GaussianLawBridge`, not assumed.

`fixed_minimax_upper` proves that, for every compact nonempty real moment set
and every invertible channel, every number strictly greater than the supremum
of the inverse-channel gradient coefficient eventually bounds normalized
minimax risk. It works along every positive vanishing coordinate-variance
sequence and normalizes by total complex power `2v`. The decoder is fixed
independently of noise power.

`fixed_minimax_upper_prescribed` states the same result for the original
readouts and prescribed slopes whenever the moment set lies in their closed
coordinate intervals. Exact target agreement on the moment set transfers the
actual minimax risk, not merely its formal leading coefficient.
