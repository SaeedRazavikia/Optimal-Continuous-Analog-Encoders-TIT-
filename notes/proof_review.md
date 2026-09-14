# Independent internal review of the foundational theorem chain

This review checks the current manuscript directly. It is an additional internal derivation check, not external peer review and not a novelty certificate. The review covers the rigidity lemma, exact score, convex reconstruction, uniform-decoder interpretation, explicit strip projection, and fixed-radius minimax statement. It does not audit the explicit quadratic/quartic optimality proofs or claim to exhaust the functional-equation literature.

## Verdict

No invalidating mathematical defect was found in the reviewed statements under their stated assumptions. The manuscript changes below strengthen the proof exposition rather than repair an identified false theorem.

## Rigidity: individual dependencies checked

1. A differentiable strictly convex (strictly concave) function has an injective monotone derivative: equal derivatives at two distinct points would force affine behavior on the intervening interval. Collision completion therefore identifies the triple sum by varying one common fourth input. The argument requires K at least four; it says nothing conclusive about K equal to three.
2. In the topological lemma, every fixed-parameter slice is injective because the collision inverse returns its moment coordinate. Invariance of domain applies to an open subset of R² with values in R². The slice image is open, so continuity in the fiber parameter and application of the same inverse force local constancy. Connectedness of the parameter interval gives constancy. No regularity of the inverse decoder is assumed.
3. Nonaffineness of a C¹ feature on the connected interior supplies two fixed unequal-slope anchors. Their derivative difference is precisely the determinant of the local three-variable moment chart.
4. The convolution argument requires more than an unspecified local identity. The revised proof first restricts the chart to a product, then chooses one source box inside that chart, and finally chooses the pair-coordinate density inside that box's image. This makes the local factorization hold on the same support for all nearby free inputs. A compactly supported cutoff allows zero extension of the readout before convolution. Composing the smooth convolution with the C¹ feature curve gives interior C¹ encoding.
5. After the regularity step, the implicit-function theorem identifies moment-fiber tangent spaces with differential kernels. Constancy on these fibers forces each encoded derivative vector into the two-dimensional moment row span. Two fixed unequal-slope anchors determine global coefficients, as now displayed explicitly. Endpoint continuity extends the integrated identity to the closed interval.
6. The local moment image is open. A linear map with dependent feature directions cannot be injective on this image, contradicting the collision implication. Thus rank two is necessary.

## Exact score and synthesis

The gradient integral on the containing strip yields a valid bound even if the segment between two moment points is not attainable. The quadratic dual norm is convex in the mean-readout derivative; its maximum on the derivative interval is attained at an endpoint. Strict convexity/concavity of the feature provides unequal feature slopes at nonconsensus interior inputs approaching either consensus endpoint. At each such point the moment map is a submersion and has an attainable open neighborhood. Choosing a separate, sufficiently small displacement in each neighborhood yields the endpoint lower sequence. No common neighborhood radius is required.

The review also identified an unnecessary hypothesis, rather than an error: the exact-score proof does not require finite endpoint derivatives of the local feature phi. Continuity on the closed interval, C¹ regularity in the interior, and strict convexity/concavity suffice for that feature. Only the mean readout psi needs finite continuous endpoint derivatives for the endpoint dual norm. The revised theorem and assumptions table adopt this weaker feature assumption. The separate numerical theorem still uses C² feature regularity to certify interpolation errors.

The synthesis constraints are equivalent to the score bounds for positive-definite G. At positive objective the two distinct endpoint derivative vectors force G to be positive definite. Reducing the translation diagonal to its Schur complement preserves G, reduces all peak quadratic forms by one nonnegative constant, and produces a rank-two Gram matrix. Three spanning feature samples bound the positive-semidefinite Gram matrix, while lambda <= G22 bounds the objective. Closedness and a positive feasible point give attainment. These arguments are sound; numerical treatment of continuum constraints is a separate requirement.

## Decoder checks

The scalar extension equality follows by placing one noiseless received point at another configuration's observation for necessity and using the classical McShane construction for sufficiency. The strip projection is Euclidean projection after the channel-coordinate linear map. Minimizing over the feature statistic produces the stated correlation correction; substituting it leaves a positive Schur-complement coefficient and a scalar clipped mean. Nonexpansiveness and the strip's dual-gradient bound prove the uniform constant. The exact score proves its sharpness, including after clipping the scalar output to a containing target interval.

For a known disturbance radius, two closed Euclidean balls intersect whenever their centers are at most twice that radius apart. Their midpoint proves the ambiguity lower bound. The midpoint of the attainable target extremes at an observation attains the bound. Compactness and semicontinuity justify a Borel decoder. This concerns a different criterion from one uniform all-radius amplification constant.

## New proved endpoint boundary

The manuscript now includes phi(s)=s² and psi(s)=-sqrt(1-s). This pair satisfies the classification assumptions but has an unbounded endpoint readout derivative. Rigidity forces every exact continuous encoder to be quadratic in s, so comparing the two consensus inputs 1 and 1-h gives a received difference of order h and a target difference of order sqrt(h). Every encoder therefore has zero squared separation. This is a genuine assumption boundary, not merely an unexamined extension.

## Additional proved feature boundary, retained here to avoid overloading the main text

Nonaffineness of the feature alone is insufficient for the endpoint exact-score formula, even when both functions are C¹ on the closed interval. Let P=1, psi(s)=s², and phi(s)=(1-4s²)_+². The feature is nonaffine, nonnegative, C¹, and zero outside (-1/2,1/2). The exact encoder E(s)=s+i phi(s) satisfies the peak bound: for x=s² in [0,1/4], x+(1-4x)^4 is convex, so its maximum is at an endpoint and is at most one; outside that interval the squared modulus is s².

Set m=S/K and t=T/K. If t is positive, at least one input lies in (-1/2,1/2), so |m| <= b=1-1/(2K). For any pair with different feature moments, at least one t is positive; hence |m_1+m_2| <= 1+b. The identity

    Delta f = Delta t - (m_1+m_2) Delta m

and Cauchy-Schwarz give |Delta f|² <= [1+(1+b)²]((Delta m)²+(Delta t)²). For pairs with identical t, the corresponding constant is at most four. Thus

    Lambda_sq(E;f) >= K² / max{4, 1+(2-1/(2K))²} > K²/5.

The endpoint formula applied without its feature assumptions would instead give K²/5 because G is the identity and psi'(±1)=±2. This counterexample proves that some endpoint attainability condition is required; it does not prove strict convexity itself necessary. The manuscript correctly uses strict convexity/concavity as a sufficient condition.

## Remaining limits

- Correctness checks do not establish novelty. The affine-representation conclusion and its proof mechanism require comparison with the closest additive-representation and functional-equation theorems.
- The fourth-terminal argument, planar received dimension, shared encoder, pointwise power constraint, and calibrated additive channel remain the stated architecture.
- The exact score, synthesis, and decoder hypotheses are stronger than those of rigidity. The new assumptions table makes this distinction explicit.
- Full external expert review of the foundational lemma remains outstanding.

## Independent certificate check

The supplied exponential-feature certificate was rerun in verification-only mode and exited successfully. Independent algebraic review confirms q''=2A+4B exp(2s)+2 ell_2 exp(s)+2C(s+2)exp(s) and its uniform bound used by the verifier. The interpolation error M h²/8 is an upper bound on the excess over the largest endpoint sample on each mesh interval. Scaling both H and lambda by the reciprocal of the certified continuum peak preserves the score inequalities and ensures peak feasibility.

For the dual witness, nonnegative peak weights alpha_j, positive-semidefinite endpoint matrices B_sigma, and Q=sum_j alpha_j z_j z_j^T - embed(sum_sigma B_sigma) positive semidefinite imply sum_j alpha_j >= lambda sum_sigma w_sigma^T B_sigma w_sigma for P=1. The certified normalization is at least one, so the stated dual value is a valid upper bound. Rational Taylor enclosures with remainder 3/41! cover the exponential feature and endpoint slopes. Exact interval determinant lower bounds suffice for the displayed symmetric positive-definite matrices. The resulting interval [0.41964508992808314, 0.4196702244375766] implies a relative suboptimality bound of 0.00598910955%. This is a mathematical certificate for the represented rational witness; the displayed decimal encoder coefficients are approximations.

The verification-grid refinement uses a fixed candidate matrix and objective, rather than independently resolving the finite program for every grid. This distinction is explicit in the numerical section. The verifier now also checks matrix shape, symmetry, and the nonnegative objective explicitly; the supplied witness met these requirements before the additional checks.

The general finite-grid theorem was checked separately from the exponential implementation. Three fixed spanning feature vectors bound every grid-feasible H uniformly. Consequently both the derivative-remainder constant and the finite optimum U_h remain bounded as the maximum grid spacing decreases. Scaling a finite-grid optimizer by rho_h=P/(P+M_h h²/8) yields rho_h U_h <= lambda_star <= U_h, with interval width O(h²). The theorem permits nonuniform finite grids. The practical reconstruction paragraph requires a positive candidate objective so G is invertible, as in the exact synthesis theorem.

## Small-noise comparison

The small-noise MSE proposition was also checked. For a common continuous source density in (-1,1), strict convexity of s^p, p in {2,4}, gives |m|<1 and 0<f_p<1 almost surely. Both clipping operations are therefore locally inactive. The real received-coordinate derivative is (-p m^(p-1)/a, 1/b)/(K sqrt(P)). Its Gaussian quadratic mean yields the coefficient [1/b²+p² E(m^(2p-2))/a²]/(2K²P). The global decoder bound dominates the squared error divided by N0 by an integrable multiple of |Z|², so dominated convergence remains valid even for the simulated endpoint-Beta density. The statement correctly gives a limit rather than an unproved O(N0²) error term near clipping boundaries. Replacing the worst-case slope by M_eff=p sqrt(E(m^(2p-2))) in the existing quadratic/quartic minimization gives the prior-aware optimum within the stated orthogonal family; it does not establish finite-noise Bayesian optimality.
