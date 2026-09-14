# Historical comparison with the supplied draft

This comparison uses the **actual supplied source**, rather than the roadmap's intended allocation. The companion is Saeed Razavikia, *Bivariate Over-the-Air Computation With Continuous Curved Encoders*, at `sources/legacy_tcom/manuscript.tex` in the original archive. Its SHA-256 is `7d17e10c7933ec9c5ef5646eff9083d18a7670099269bb2769e54f9420fe1911`. Its README reports a draft checked on 9 September 2026. This snapshot does not establish the companion's present submission or publication status, or the contents of any later version.

The papers share the synchronized unit-gain complex additive MAC, a common encoder, a per-symbol peak limit, several background references, and parabolic feature maps. Their principal theorem chains address different optimization problems.

| Item | Supplied companion snapshot | Present TIT manuscript | Assessment |
|---|---|---|---|
| Inputs and targets | Two real inputs; continuous symmetric bivariate targets with additional corner or disagreement hypotheses | At least four terminals; prescribed moment-minus-mean targets and a restricted polynomial extension | Arity changes what two real received coordinates can identify. |
| Objective | Infimum of `exp(a d^2)/(target gap)^2`, with `a=1/(4 N0)` | Infimum of `d^2/(target gap)^2`; additional constrained leading-MSE objective | The criteria are not interchangeable: the exponential numerator is nonzero at received collisions. |
| Competitors | Arbitrary peak-admissible shared maps for the converse; continuous exactly computing constructions | All continuous exact shared planar encoders; positive squared separation implies exactness | TIT's classification supplies its global design reduction. |
| Exact representation | `prop:injectivity`: a strictly concave graph identifies an unordered pair and hence every continuous symmetric bivariate target | Necessity of the affine `(s,phi(s))` family | Construction for two inputs differs from necessity for a prescribed higher-arity target. |
| Main optimality proof | `thm:profile`, `thm:main`: extremal-pair converse, target envelopes, and positive certified power-to-noise regimes | Endpoint-gradient score, attained Gram/inverse-metric synthesis, and explicit quadratic/quartic solutions | No main theorem or proof is imported from the companion. |
| Circular geometry | `prop:geometry`, `thm:circle`, `prop:sharpreadout`, `thm:sharpgaussian`: semicircle necessity and circular thresholds | No semicircle classification or Gaussian-kernel threshold theorem | Remains a companion contribution. |
| Bayesian result | `prop:beta`: minimum Bayesian MSE decreases with imaginary amplitude within fixed `(g,alpha)` family, at every noise level | Global encoder optimization of the strip decoder's leading small-noise MSE coefficient under a separation floor | Neither result implies the other. TIT does not optimize arbitrary finite-noise Bayesian encoder/decoder pairs. |
| Figures and curves | Concave graph families, semicircles, target envelopes, bivariate objective and posterior-mean MSE | Necessary moment features, peak-optimal curves, enclosing ellipses, strip decoding, and constrained variance frontier | A parabola is shared geometry; targets, parameters, and optimality guarantees must remain explicit. |
| Numerical data | Nine source levels per terminal; 80,000 trials; bivariate product, kernel, and envelope targets | Four/sixteen terminals; continuous uniform and beta priors; 200,000 trials in the existing paired study; strip/readout decoding | TIT figures use TIT data and formulas. No companion numerical arrays or plots are reused. |
| Certified computation | Interval-validated target envelopes and numerical finite-alphabet SDP bounds | Exact-arithmetic primal/dual continuum certificate for the exponential Jensen gap | Different certified objects and guarantees. |

The supplied companion contains **no higher-arity `A+B m w` converse** and no robustness-constrained small-noise frontier. The previous allocation document inherited the former from the roadmap; this comparison removes that unsupported account of the actual snapshot.

A normalized text comparison of the supplied companion with the present section sources found shared channel-model wording but no matching prose run of ten words. This is a local editorial check, not a formal similarity determination. Mathematical and graphical overlap remains relevant even when wording differs.

## Current status

The author has confirmed that the bivariate manuscript is a draft and is not planned for submission. The current paper therefore omits its citation and the related-work paragraph; the cover letter no longer describes it as a companion submission. This historical comparison remains an internal development record. It is not a submission enclosure, and the supplied draft is excluded from the current source delivery.
