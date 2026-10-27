# Proposition 4: global quadratic and quartic optima

The terminal results are
`Analog.PolynomialGlobalOptima.quadratic_global_optimal` and
`Analog.PolynomialGlobalOptima.quartic_global_optimal`.
They use the paper's hypotheses: `K ≥ 4`, `P > 0`, and a readout that is C¹,
even, and strictly convex or strictly concave on the closed source interval.
Their scores are the actual infima over finite-node input pairs.

The proof connects the following results:

1. `EvenReadout.endpoint_magnitude_pos` derives `M = |ψ′(1)| > 0`.
   `endpoint_slopes_opposite` proves the endpoint sign relation, and
   `endpoint_score_eq_gramScore` reduces the endpoint formula to the
   quadratic/quartic Gram objective. Endpoint derivatives are derivatives
   within the closed interval, so no differentiability outside it is assumed.
2. `FiniteNodeScore.lemma_one_score` supplies the actual operational score
   with arbitrary individual node offsets.
3. `PolynomialRigidity.polynomial_positive_score_rigidity` shows that every
   continuous positive-score competitor has common nonsingular polynomial
   columns. Strict curvature rules out affine readout intervals; independence
   of the features is proved for both powers.
4. `PolynomialGlobalOptima.average_received` proves that averaging the node
   offsets preserves the received aggregate exactly, for every source tuple.
   `average_peak` proves the continuum peak constraint by a finite-sum
   Cauchy–Schwarz inequality.
5. The existing all-power quadratic and quartic certificates optimize the
   resulting coefficient objective. `unrestricted_polynomial_optimal` also
   handles competitors whose score is zero, without imposing an exact-decoding
   assumption on the competing encoder class.

Both terminal results prove feasibility, the displayed score, and domination
of every continuous peak-feasible collection. `sharedEncoder_continuous`
proves that the constructed encoders themselves are continuous. The quartic
result includes existence and uniqueness of the root in `(0,1/3)` and uses the
paper's reciprocal score expression, `K²P/(M²/aρ² + 1/bρ²)`.

The exact encoder coordinate formulas are
`PolynomialOptimizerFacts.quadratic_encoder_formula` and
`PolynomialOptimizerFacts.quartic_encoder_formula`; the existing coefficient
definitions give the stated `a`, `b`, `aρ`, `bρ`, and `cρ` formulas.
No rigidity, offset-averaging, endpoint-symmetry, or operational-score conclusion
is assumed as a premise in the terminal statements.
