# Robustness-constrained small-noise design: derivation and claim boundary

The new section `sections/pareto.tex` derives an encoder-design frontier for the **implemented strip projection/readout decoder**, with optional target clipping only if it is locally inactive almost surely. It does not assert finite-noise Bayesian optimality, minimize over arbitrary decoders, or interchange minimization with the small-noise limit.

## General result

Assume the manuscript's global synthesis hypotheses: K>=4, continuous shared planar encoding, pointwise peak P, phi continuous on the closed interval and C1 in its interior and strictly convex/concave, and psi C1 on the closed interval and strictly convex/concave. The input vector may have any joint prior with |m|<1 almost surely. Set w(m)=(-psi'(m),1) and Q=E[ww^T]. Require Q positive definite, equivalent to Var(psi'(m))>0.

For an exact encoder, rigidity gives E=c+U(s,phi(s)), invertible U, G=U^TU. Under N~CN(0,N0), local differentiation of the strip decoder and dominated convergence using its global Lipschitz constant give

    lim MSE/N0 = tr(Q G^-1)/(2K^2).

Only local inactivity at almost every noiseless source point is needed; no uniform distance from clipping boundaries is assumed. Q depends only on the prior of the mean, not independence of the input coordinates. The phi geometry enters through the feasible peak set.

For a floor gamma=Lambda_min/K² in [0,lambda_star], the displayed program uses X=G^-1 and a=-U^-1 c, with five scalar variables. The peak constraint is exactly

    [[P, (g(s)-a)^T], [g(s)-a, X]] PSD for every s,

where g(s)=(s,phi(s)). The objective tr(QX)/(2K²) and two endpoint budgets w_endpoint^T X w_endpoint <= 1/gamma are linear. At gamma=0, omit those budgets. A null vector of X would force the nonaffine curve g(s) into an affine line; therefore X is positive definite even without imposing a strict open constraint. Q positive definite bounds X on finite objective sublevels, and the block constraint gives |g(s)-a|² <= P tr(X), hence bounds a. Closed compact sublevels establish attainment even at gamma=0. Reconstruct U^TU=X^-1 and E=U(g-a).

The equivalent Gram formulation constrains G>=gamma w_endpoint w_endpoint^T and the existing peak Gram inequalities. It can express the inverse objective with W=Q^.5 and [[G,W],[W,T]] PSD, minimizing tr(T)/(2K²), but this larger epigraph is not needed computationally. The Gram formulation is useful to prove convexity in gamma (the simpler X formulation is immediately convex in the reciprocal budget, which alone would not prove the gamma claim). Reducing the translation diagonal of H to its Schur complement preserves G and all scores and decreases every peak norm, so rank-two planar reconstruction remains exact.

The statement is global over all continuous exact encoders in this architecture by the rigidity theorem. It is not a restriction to initially assumed feature curves.

## Value and uniqueness

The value is finite, nondecreasing, convex, and continuous on [0,lambda_star]. The matrix objective is strictly convex in G for Q positive definite:

    d² tr(QG^-1)[D,D] = 2 tr(A B²)>0,
    A=G^-1/2 Q G^-1/2, B=G^-1/2 D G^-1/2.

Thus the optimum has unique feature Gram G, even if translation and received-plane orientation are nonunique. Let gamma_c be the actual robustness of the zero-floor optimizer G0. The value is constant on [0,gamma_c], strictly increases after gamma_c if the remaining interval is nonempty, and the floor is active there. For activity, a slack optimum mixed slightly with G0 remains feasible but improves the objective. Equality of values at two distinct increasing-branch floors contradicts unique G and activity. No global strict increase is claimed. Strict convexity of the increasing branch can also be derived from uniqueness/activity and strict matrix convexity, but the paper does not need that stronger statement.

## Quadratic specialization

For phi=s², even psi, and symmetric mean law, Q=diag(M_eff²,1), M_eff²=E[psi'(m)²] and M=|psi'(1)|. The strict interior-mean hypothesis and strict convexity/concavity give 0<M_eff<M. The reflection/projection reduction improves both tr(QG^-1) and worst-case separation; it hence remains valid under a robustness floor. The full continuous exact class reduces to

    E_b=√P [√(b(2-b)) s + i(bs²−1)], 1<=b<2.

The normalized robustness is R_M(b)=[M²/(b(2-b))+1/b²]^-1. The normalized small-noise objective uses M_eff in the same denominator. The b(x) minimizer is defined by x² b(b−1)=(2−b)², or the explicit formula in the paper. It decreases with x. Thus b_eff>b_M. The floor-feasible b set is an interval containing b_M. The optimal b is min(b_eff,b_plus(gamma/P)), where b_plus is the decreasing-score branch root. The plateau threshold is gamma_c=P R_M(b_eff).

For uniform independent sources, E[m²]=1/(3K), so variance has M_eff=2/sqrt(3K). For centered symmetric Beta(a,a) sources, Var(s)=1/(2a+1), E[m²]=1/[K(2a+1)], and M_eff=2/sqrt(K(2a+1)).

## Limits and integration advice

- Q positive definite is essential to the stated uniqueness and zero-floor coercivity/attainment argument. Degenerate mean laws require separate treatment; they are not covered by silently taking Q semidefinite.
- Optional clipping at a boundary with positive prior mass can change the derivative and small-noise coefficient. Use the unclipped strip readout or state interior-target almost surely.
- The general program remains semi-infinite. Its exact formulation alone is not a computational certificate.
- The existing orthogonal small-noise proposition in `finite_noise.tex` is a specialization of Proposition `prop:general-small-noise`. It may be shortened to an equation and a reference when integrating the new section, or retained explicitly as a specialization.
- Place the new section after decoding and before empirical evidence. Its equations refer to already defined rigidity, score, synthesis, and decoder results. Update abstract/contribution list/assumptions table to say exact robustness-constrained **small-noise** encoder design; avoid unqualified optimal-MSE language.
- Independent internal review is requested. This derivation is not an external specialist or historical novelty review.

## Independent internal review outcome

A separate structural-review agent read the final inverse-metric section line by line and reported no invalidating defect in the nullspace exclusion, compactness, Gram strict-convexity argument, convexity and endpoint continuity in the robustness floor, active-branch argument, or global quadratic reduction. This is an independent internal mathematical check within the writing workflow, not external peer review or a confirmation of historical originality.
