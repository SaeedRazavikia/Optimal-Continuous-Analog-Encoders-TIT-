# Optimized heterogeneous Gaussian minimax theorem

`Analog/GaussianOptimizedMinimax.lean` completes the outer statistical
optimization. Its terminal theorem is
`heterogeneous_optimized_minimax_achieved`.

The theorem starts with the actual finite collection of continuous source
features, functional independence of the constant and two feature coordinates,
positive peak budget and node count, the prescribed closed-interval readouts,
the actual attainable moment set's interior-density condition, and gradient
spanning. It derives compactness and nonemptiness of the actual finite-source
moment image. No compactness assumption on that image is supplied separately.

It constructs one fixed peak-feasible identifiable coefficient design
`pstar`, proves that its maximum inverse-Gram coefficient is minimal over
every such design, and proves the full one-sided small-noise limit for the
actual risk infimum over all identifiable designs and all Borel decoders.
The risk uses genuine nonnegative Gaussian squared-error integrals, including
decoders of infinite risk. Noise normalization is by total complex power
`N₀ = 2v`.

The limiting coefficient is

`sup_m inverseCoefficient pstar (prescribedCoordinates r₁ r₂) m / (2K²)`.

It uses the original prescribed slopes and readout values, not values of an
extension outside the attainable set. The same theorem proves that the
single explicit inverse-channel/endpoint-extension decoder for this same
`pstar` attains the coefficient in its actual worst-case additive Gaussian
risk. The design and decoder are independent of noise power.

## Proved assembly

- `parameter_regular_converse` applies the full moving-Gram model converse
  to convergent actual coefficient parameters, deriving all required Gram
  convergence from polynomial coordinate formulas.
- `singular_kernel`, `interior_direction_witness`, and
  `parameter_singular_converse` find a nonzero lost channel direction, detect
  it at an actual interior moment, and invoke the constructed local-prior
  Gaussian divergence proof.
- The compact coefficient class includes singular boundary limits; the
  optimized finite-noise class contains only identifiable designs. The
  constrained compact subsequence theorem respects this distinction and
  does not assume compactness of the identifiable class.
- `optimized_minimax_sequential_limit` combines attained inverse-Gram design
  minimization, the regular and singular model converses, and one fixed
  decoder's achievable upper bound. It assumes no information inequality,
  test completeness, local-prior existence, sequential risk estimate, or
  asymptotic upper bound.
- `optimized_minimax_limit` fixes a minimizing design before the arbitrary
  noise limit. Any minimizing designs obtained along other sequences have
  the same coefficient by both minimality inequalities.
- `optimizedRisk_eq_infimum_div` proves that division by positive noise
  power commutes with the actual design infimum. Thus the final statement
  has the paper's ratio-of-infimum form, not merely a separately defined
  infimum of normalized risks.
- `constructed_decoder_attains` identifies the worst-case Gaussian limit
  of the same fixed constructed decoder with the same prescribed-slope
  inverse-Gram value.

`heterogeneous_optimized_minimax_limit` and
`heterogeneous_optimized_minimax_achieved` specialize all of this to the
actual `HeterogeneousScore.attainable γ` and compact source-feature class.
The separate heterogeneous rigidity theorems identify the coefficient
parametrization with the manuscript's original identifiable encoder class.

## Validation

The module has 17 public theorems. Ordinary Lean compilation and `--trust=0`
kernel checking pass without warnings, admitted proofs, new axioms, or native
decision shortcuts. The fixed-prior and fixed-channel minimax equality
theorems are in their companion modules; this file supplies the remaining
outer design optimization and fixed-pair attainment.
