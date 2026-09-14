# Additional independent internal structural review

This note records a new adversarial reading of the current manuscript. It is an internal mathematical review, not review by an external human specialist, and does not certify historical originality. It supplements, rather than replaces, `notes/proof_review.md`.

## Exact-rigidity chain

No invalidating defect was found in the current collision-to-factorization and regularization proof under its stated assumptions.

1. **Collision completion.** A fourth free input supplies an open interval of common means. The two completed target values coincide, so their difference is constant as the added input varies. The derivative of a differentiable strictly convex or strictly concave readout is injective; equality therefore identifies the triple sum, after which the original identity identifies the feature sum. The proof requires only interior differentiability at these configurations.
2. **Topological factorization.** Each fixed-fiber slice is a continuous injection from an open subset of the two-dimensional moment space into the two-dimensional received space. Invariance of domain makes its image open. A nearby point on the same moment fiber lies in this image and must have the same preimage because the collision inverse returns the moment pair. The encoded sum is consequently locally constant in the fiber parameter. This uses no continuity of the collision inverse.
3. **Coordinate chart.** Two fixed interior anchors with unequal feature derivatives exist for every nonaffine C1 feature on a connected interval. Their derivative difference gives the nonzero Jacobian determinant even if the free input equals one of the anchors or the feature has affine subintervals.
4. **Automatic regularity.** The manuscript now chooses one common source box inside the chart and a compactly supported smooth density inside the pair-moment image of that box. Its translated support remains in the domain of one continuous factorization function as the free input varies. A cutoff and zero extension make convolution legitimate. The convolution is smooth in its two-dimensional argument; composition with the C1 feature curve gives interior C1 encoding.
5. **Global coefficients.** Constancy on the local moment fibers annihilates the corresponding differential kernel. The fixed unequal-slope anchors determine the same two derivative coefficients for every free input. Integration on the connected interior followed by endpoint continuity gives the global affine feature representation.
6. **Nondegeneracy.** The triple moment map has a local open image. Dependent feature directions would map distinct points of this open set to one received value and contradict collision preservation. Independence is therefore a proved conclusion, not a tacit regularity assumption.

The reasoning is coherent and local hypotheses are used where stated. Its unusual feature is obtaining reverse local factorization from a one-way collision implication. Whether that distinction constitutes a substantial new result relative to restricted additive functional equations requires specialist literature assessment. The proof check alone cannot answer it.

## New qualitative approximate-rigidity corollary

The optional appendix `sections/approximate_rigidity.tex` states and proves the following limited result. For a fixed target, peak bound, common encoder modulus of continuity, and common decoder Lipschitz constant, vanishing uniform computation error forces uniform distance to the nondegenerate affine-feature family to vanish.

The decisive estimate is

    |Delta f| <= 2 epsilon + L |Delta r_E|.

Only the encoders require an Arzelà–Ascoli subsequence. Passing to the limit gives an exact encoder with a Lipschitz readout, so the main rigidity theorem applies. A separate internal checker independently derived the same simpler proof. Decoder compactness and decoder anchoring are unnecessary.

For an explicit statement of the nonconstructive modulus, define d_L(E) as one half of the supremum of the positive part of |Delta f|-L|Delta r_E|. This defect is KL-Lipschitz in the uniform encoder norm. The supremum of distance to the feature family over the compact encoder class with d_L(E)<=epsilon therefore tends to zero. The convention for an empty feasible set is zero.

The independence condition makes the feature family nonclosed. This causes no proof problem: distance to any nonempty subset is 1-Lipschitz, and the exact limiting encoder itself has independent feature directions. The result does not produce an explicit convergence rate or a coefficient-conditioning bound for an arbitrary approximate encoder. It does not prove the added compactness and decoder bounds necessary. It should be described as a compactness corollary rather than as a resolution of quantitative approximate rigidity or the paper's main novelty claim.

## Inverse-metric synthesis: independent derivation

The proposed inverse-metric formulation is exact. Set g(s)=(s,phi(s))^T, X=G^{-1}, and a=-U^{-1}c. The encoder becomes U(g(s)-a), with U^T U=X^{-1}, and its peak constraint is equivalent to

    [[P, (g(s)-a)^T], [g(s)-a, X]] >= 0    for every s in I.

The Schur complement is valid in the top-left block because P>0. These constraints imply X>=0 before invertibility is known. If h lies in the null space of X, positivity forces h^T(g(s)-a)=0 at every s. A nonzero h would make phi affine, or make s constant if its second component were zero. Thus X is automatically positive definite. No explicit open definiteness constraint or rank relaxation is needed.

The normalized worst-case inverse separation is max_sigma w_sigma^T X w_sigma. Minimizing its epigraph t therefore uses six real variables: three entries of X, two coordinates of a, and t. The optimum score is K^2/t_star. This is an equivalent convex representation, not a claim that Schur-complement semidefinite modeling itself is novel.

Attainment requires checking bounds in this coordinate system because the feasible set is not globally bounded. On a finite objective sublevel, the two independent endpoint slope vectors bound X: if W has these vectors as columns, tr(W^T X W)<=2t, hence ||X||<=2t||W^{-1}||^2. A fixed peak block gives |g_i(s)-a_i|^2<=P X_ii and therefore bounds the center a. The closed constraints yield a compact sublevel. Every limit remains positive definite by the same nonaffineness argument. A sufficiently large scalar X gives a feasible point, and the attained t_star is strictly positive.

For the Pareto problem, the objective tr(Q_pi X) with Q_pi positive definite bounds tr X on sublevels. The same peak-block argument bounds a. Thus the five-variable inverse-metric problem also attains its optimum at zero robustness floor, where the endpoint constraints are omitted. Positive floors impose the linear inequalities w_sigma^T X w_sigma<=1/gamma.

## New Pareto theorem: completed proof check

The full draft in `sections/pareto.tex` was checked before and after its equivalent inverse-metric rewrite. No invalidating defect was found in the following claims.

- For the specified strip decoder, the mean lying strictly in (-1,1) almost surely makes strip projection locally inactive. Finite endpoint readout slopes give an integrable global Lipschitz bound for the squared error divided by noise variance. Dominated convergence therefore gives tr(Q_pi G^{-1})/(2K^2), even for correlated source coordinates. Any scalar clipping requires the true target to lie strictly inside its clipping interval almost surely. The result does not cover optimal arbitrary decoders or an interchange between small-noise limits and noise-dependent encoder design.
- Positive definiteness of Q_pi is equivalent to positive variance of psi'(m), since the second readout-gradient coordinate is one. It gives coercive objective sublevels in the inverse-metric formulation and excludes a singular optimum at zero floor.
- The original Gram representation makes the projected feasible set of G convex. The inverse objective is strictly convex: along a nonzero symmetric direction its second derivative is twice tr(A B^2), with A positive definite and B nonzero symmetric. Thus the optimal feature Gram matrix is unique. The linear objective in the inverse metric by itself would not prove this uniqueness.
- Convexity in the normalized separation floor gamma follows from the original Gram LMIs, which are affine jointly in G and gamma. It should not be inferred merely from the inverse formulation, whose cap is 1/gamma. Monotonicity follows from nested feasible sets. Compact objective sublevels give lower semicontinuity; finiteness, convexity, and monotonicity then give continuity including both endpoints.
- Above the actual robustness of the unique unconstrained optimum, the required floor is active. Otherwise a sufficiently small convex mixture with the unconstrained Gram matrix remains feasible and strictly lowers the objective. Uniqueness and activity imply strict increase of the frontier above its constant portion.
- For an even quadratic feature/readout setting and symmetric mean law, reflection and projection eliminate the feature correlation while preserving peak feasibility and improving both objectives. The one-parameter peak boundary A=b(2-b), B=b^2 therefore contains a global optimizer for the constrained continuous exact-encoder problem. The prior objective has its unique minimizer at b(M_eff), while worst-case feasibility clips the right end at b_+(gamma/P). The stated scalar-root formula follows, including the zero-floor convention and strict M_eff<M under the interior-mean assumption.

The final inverse-metric rewrite preserves these arguments correctly. No mathematical changes were required after this additional review. Independent numerical checking is assigned separately. External specialist review and historical-originality confirmation remain outstanding.

## Final bounded review of inverse synthesis and implementation errors

The final `sections/inverse_synthesis.tex` agrees with the independent derivation above. The nullspace argument excludes a singular X; the Schur complement and encoder reconstruction give both directions of the correspondence. The six-variable count is correct. Independent endpoint slope vectors bound X on objective sublevels, one peak block bounds the center, and closedness preserves the continuum constraints. Existence and positivity also follow directly from the already proved Gram formulation. No correction is required to these mathematical claims.

The deterministic implementation bound in `sections/implementation.tex` is correct under its two explicit implementation assumptions: a uniform distance from the ideal map and peak feasibility of the implemented map. Decomposing the observation difference as ideal additive noise plus encoder error plus residual gain times the implemented symbol yields the stated K epsilon sqrt(P) and sqrt(P) sum |d_k| terms. No missing product of epsilon and gain error occurs because the gain term is bounded directly using the implemented map's separate peak bound. The normalized bound and its coherent-error interpretation follow immediately.

The shrink-before-quantization argument is valid when 0<r<1. The quantizer error contributes at most r sqrt(P), shrinking contributes another r sqrt(P), and the shrunken symbol plus quantization error remains inside the original peak disk. For a nearest-level scalar quantizer with 2^B equally spaced endpoint-inclusive levels, the two-component radius is sqrt(2)/(2^B-1).

**Required qualification sent to the integrating author:** explicitly impose integer B>=2 for this uniform scalar quantization example. At B=1, the stated radius exceeds one, so the assumed shrink factor condition fails; endpoint quantization outputs square corners of magnitude sqrt(2P), which violate the peak constraint. With B>=2 the example and epsilon<=2r claim are valid.

The residual amplitude/phase bound is correct: writing d=alpha exp(i theta)+(exp(i theta)-1) gives |d|<=|alpha|+2 sin(|theta|/2), and the supplied phase interval makes the sine bound monotone. Finally, retaining a fraction eta>0 of optimal squared separation multiplies the uniform disturbance bound by at most eta^(-1/2); the quoted 90-percent value of approximately 5.41-percent increase is correct. No other essential correction was identified in this bounded review.
