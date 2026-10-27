# Completed fixed-encoder Gaussian minimax theorem

`Analog/GaussianFixedMinimax.lean` supplies the terminal fixed-encoder theorem
`fixed_encoder_minimax`, combining the actual localized converse and the
proved uniform endpoint-decoder upper bound.

For a nonempty compact moment set M equal to the closure of its interior,
contained in the prescribed closed readout rectangle, and an invertible real
complex-plane channel T, it constructs an attained maximizing moment mstar
and proves all of the following:

- every moment's prescribed inverse-channel coefficient is at most that of mstar;
- the explicit endpoint-extension decoder is Borel measurable;
- this one fixed decoder has finite genuine worst-case ENNReal risk for every
  positive Gaussian variance;
- the genuine all-Borel minimax risk, normalized by total complex power 2v,
  converges to the coefficient at mstar as v tends to zero from above;
- the genuine worst-case risk of the same noise-independent constructed decoder
  has exactly the same normalized limit.

No lower-limit statement, upper-limit statement, Taylor expansion, conditional
law identity, score identity, or optimizer witness occurs as a final premise.
The original readout, rather than its extension, appears in both risk limits.
`fixed_minimax_limit` and `fixed_minimax_sequential_limit` also expose the
corresponding supremum-coefficient versions.

The channel T includes K, and its offset c includes the encoder-sum offset.
The coefficient is the half inverse-channel directional energy; the verified
`GaussianGramCoefficient` identifies it with wᵀG⁻¹w/(2K²).
