# Gaussian coefficient design and physical channel

`GaussianDesignCompactness` derives compactness of the actual peak-feasible
coefficient parameters from functional independence. It uses the inverse of
the injective coefficient map onto the finite-dimensional space of encoder
functions. Singular parameters remain in this compact set. A small positive
multiple of the identity channel is constructed and proved peak feasible.

`GaussianDesignAttainment.inverse_gram_design_minimum` proves attainment of
the minimum of the maximum inverse-Gram gradient energy. Both the moment
maximum and encoder minimum are attained. Its proof minimizes the exact
quadratic epigraph on a compact set; gradient spanning forces every finite
epigraph point to have nonzero determinant. Thus neither compactness nor
divergence at singular matrices is assumed.

`GaussianParameterChannel` constructs the actual invertible channel `K U`
from the finite-node coefficients, proves equality with the physical received
sum and likelihood rows, and derives the exact `1/K²` coefficient factor.
It also supplies continuity of the rows, offsets and directional energies
for changing-design limits.

`GaussianGramCoefficient` identifies the inverse-adjoint energy from the
statistical converse with the directional derivative energy from Gaussian
achievability, the explicit inverse-Gram quadratic form, and the trace of
the actual gradient second-moment matrix times the actual matrix inverse.

These are design and model-identification results. The final statistical
optimization additionally uses the genuine sequential converse, singular
exclusion and fixed-decoder upper bound in the Gaussian assembly modules.
