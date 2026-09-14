# Adversarial novelty challenge and synthesis interpretation

Date: 13 September 2026. This is a bounded internal literature challenge, not external peer review or a historical-priority certificate. It supplements `novelty_review.md` and does not supersede the full assumption comparisons there.

## 1. Classification: a real distinction, but uncertain contribution weight

**Assessment.** Retain the self-contained necessity theorem, but do not argue that nonidentical hypotheses establish substantial originality. The manuscript's topology lemma is a short consequence of invariance of domain. A specialist could reasonably view the classification as a useful application of established local additive rigidity after that reduction. The contributions should therefore emphasize the complete necessity–conditioning–peak-design theorem and its explicit consequences.

**Inspected primary loci.** Charalambides, [Theorem 1.6 and Section 5, equations (5.1)–(5.5)](https://arxiv.org/html/1203.5370v2), gives affine additive summands on suitable smooth curves. The proof selects an invertible sum chart, integrates to obtain regularity, and differentiates. These are close antecedents of the manuscript's last two steps. Theorems 1.3–1.4 also treat approximate restricted equations, but for a different hypersurface setting.

**Applicability judgment.** Our initial encoded-collision implication has the opposite information direction from an assumed factorization through moment sums. The manuscript repairs that difference locally. This is a mathematically meaningful reduction; it does not establish that the reduction is historically new or sufficiently deep by itself. Features with affine subintervals enlarge the theorem's scope, but our optimization examples lie in a smoother strictly convex subclass. The weaker feature hypothesis should not carry the introduction's principal novelty claim.

Wagstaff et al., [Lemma 17 and the proof of Theorem 14, pp. 12–13](https://jmlr.org/papers/volume23/21-0730/21-0730.pdf), already use fixed-cardinality exact computation to force aggregate injectivity and then invoke topology. The target and conclusion differ, but the collision/topology mechanism needs credit. No further matching theorem was identified in bounded searches for scalar exact shared-sum computation, local one-way collisions, and continuous Freiman maps. This search outcome is not evidence of priority.

## 2. Tradeoff: identify the computation-specific result

**Inspected primary loci.** Papp, [Example 6 and Theorem 9](https://arxiv.org/html/1009.1444v2), gives the Schur-complement representation of inverse-trace optimality and semidefinite computation of optimal designs over intervals for rational regression functions. Sagnol, [Section 4.1, equation (12), Theorem 4.1, and Section 4.2](https://arxiv.org/pdf/0912.5467), treats A-optimal estimation of a subsystem and conic formulations with resource constraints. These establish that matrix inverse criteria, directional estimation costs, conic epigraphs, and constraints added to design problems are standard methods.

For Q positive semidefinite, tr(Q G^{-1}) is a weighted A-optimal-type criterion: write Q=CC^T and obtain tr(C^T G^{-1} C). Likewise, w^T G^{-1}w is a directional variance criterion. This algebraic connection does not identify our feasible G with the convex hull of Fisher information matrices in an experiment-design problem. In our problem, a translated feature curve must fit into a peak disk. Do not claim a new generic convex optimization principle or an established exact experimental-design duality without deriving it.

The defensible new result to pursue is: **the exact computation classification makes the constrained small-noise risk design globally valid over every continuous encoder in the stated class; the variance specialization yields an explicit frontier and its phase transition.** A numerical Pareto curve alone has weaker contribution weight. The decoder and prior assumptions remain part of that statement; this is not global finite-noise Bayesian optimality over arbitrary encoders and decoders.

## 3. Useful equivalent enclosing-ellipse formulation

The following derivation is our inference from the manuscript's formulas, not a theorem imported from the sources.

Let gamma(s)=(s,phi(s))^T and write an exact encoder as E(s)=U(gamma(s)-a), where U=[u v] is invertible and a=-U^{-1}c. Set X=(U^T U)^{-1}. The peak condition is equivalent to

$$
\begin{pmatrix}P&(\gamma(s)-a)^T\\\gamma(s)-a&X\end{pmatrix}\succeq0
\quad\text{for every }s\in[-1,1].
$$

This follows by a Schur complement. Consequently, the separation optimum equals K^2/t_* where t_* solves

$$
\min_{X\in\mathbb S^2,\ a\in\mathbb R^2,\ t\in\mathbb R} t,
\qquad w_\pm^T Xw_\pm\le t,
$$

subject to the peak LMIs above. There are **six scalar variables**, and every constraint is affine in them. Nonaffineness of gamma forces X positive definite: if v is a null vector, positive semidefiniteness of each block forces v^T(gamma(s)-a)=0 for every s, placing the entire feature graph in an affine line. Reconstruct with U=X^{-1/2} and c=-Ua. A bounded t bounds X because w_-,w_+ span R^2; the peak LMIs then bound a. This also yields attainment directly.

A required score K^2 eta adds the two linear inequalities w_±^T Xw_±<=1/eta. Minimizing the small-noise coefficient then becomes the **linear objective tr(QX)** over X,a under the same peak LMIs. The tradeoff program has five scalar variables for a fixed eta. This parameterization clarifies that the design chooses an enclosing ellipse of the feature graph while limiting its widths in target-sensitive directions.

Boyd and Vandenberghe's [author-hosted slides, Chapter 8, slide 8.2, PDF p. 245](https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf), give the classical convex enclosing-ellipsoid framework; Chapter 7's experiment-design slides explain boundary contacts through complementary slackness. Our objective is not ellipsoid volume, so do not call the present optimizer a Löwner–John ellipse. The shape parameterization and Schur complement should be credited as standard convex geometry. The computation-specific input is the forced feature curve and the exact sensitivity criterion.

This equivalent form can be added as a short corollary while retaining the existing seven-variable Gram implementation and its certificates. It need not trigger a rewrite of the working numerical solver.

## 4. Approximate rigidity: avoid promoting compactness to a quantitative theorem

A uniform peak bound, a common encoder modulus of continuity, and a uniform decoder Lipschitz bound can support a subsequence argument: approximate computation errors tend to zero; uniform limits compute exactly; rigidity identifies the limit; contradiction proves qualitative proximity to the moment-feature family. This is useful, but its mechanism is ordinary compactness and closure. It supplies neither a rate nor useful constants. It should be labeled a qualitative consequence and placed after the main theorem or in an appendix.

Check that decoder control applies on a common received domain and that additive offsets are bounded or normalized. Without a common continuity modulus for encoders, compactness fails. Without decoder control, taking limits need not preserve exactness. Do not state that small computation error alone forces proximity. A stronger primary contribution would derive an explicit modulus with dependence on feature curvature, chart conditioning, and decoder regularity; that has not been obtained in this review.

## 5. Concrete questions for an external specialist

1. Does an existing local restricted additive equation theorem, combined with invariance of domain, imply our full continuous one-way-collision lemma under the stated feature assumptions?
2. If not, is the missing reduction a substantive theorem or a short application that should be presented as a lemma supporting the design result?
3. Can the affine-subinterval case be reduced to standard local results by fixed-anchor propagation, as the proof suggests?
4. Does any known stability theorem yield a quantitative estimate for our scalar-exactness premise, rather than an already factored additive equation?

These questions can be included in an unsent review brief. Nothing in this note represents a specialist's assessment or authorization to contact a researcher.

## 6. Source verification and limits

- Charalambides: full author manuscript inspected at the theorem and proof loci above; publication metadata already verified in the earlier review.
- Wagstaff et al.: full JMLR PDF inspected at the named lemma and topology proof.
- Papp: full arXiv HTML inspected, including the stated examples and theorem. Verified author and arXiv version date (v2, 29 August 2011); no journal bibliographic record is asserted here.
- Sagnol: full author PDF inspected at Section 4.1 and Theorem 4.1; arXiv record verifies v3, 25 November 2010. No unverified journal metadata are supplied.
- Boyd and Vandenberghe: author-hosted slides inspected. Direct book-PDF retrieval failed; the book's full text was not represented as newly inspected.

The review supports restrained attribution and a clearer geometry. It does not settle historical originality, guarantee journal acceptance, or replace mathematical peer review.
