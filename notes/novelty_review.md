# Focused novelty review — 13 September 2026

## Finding and resulting positioning

The review found a materially closer precedent than those in the reconstructed manuscript: **Marcos Charalambides, “On restricting Cauchy–Pexider functional equations to submanifolds,” Aequationes Mathematicae, 86(3), 231–253, 2013, DOI 10.1007/s00010-012-0173-7.** The publisher verifies the bibliographic record; the full author manuscript, arXiv:1203.5370v2, was inspected, including Theorem 1.6 and Section 5.

The paper should therefore credit restricted Cauchy–Pexider rigidity explicitly. It should not market affine-feature uniqueness, or regularization by integration followed by differentiation, as new general principles. Its defensible distinction is the necessity argument starting from exact computation of one scalar target: a fourth input exposes both moments, and dimension equality converts one-way information preservation into local factorization. The subsequent optimization and explicit disturbance guarantees remain separate contributions.

## Closest theorem: exact applicability test

Let gamma(s)=(s,phi(s)) and let R_E(x,y,z)=E(x)+E(y)+E(z). The manuscript assumes

    R_E(x,y,z)=R_E(x',y',z')  =>  gamma(x)+gamma(y)+gamma(z)=gamma(x')+gamma(y')+gamma(z').

The reverse implication is initially absent. In particular, the unknown encoder need not be a function of the moment sum before the topology argument. Substituting the target function directly into an additive-representation theorem does not resolve this distinction.

| Issue | Charalambides, Theorem 1.6 | Current manuscript |
|---|---|---|
| Geometric domain | Connected smooth embedded curve in R^d; no open subset lies in an affine hyperplane | Graph of a C1 nonaffine function; affine subintervals permitted |
| Number of summands | d+1 | Three, after completion from K>=4 |
| Premise | Measurable global additive factorization through the sum of curve points, almost everywhere | Continuous planar encoder; one-way collision implication everywhere |
| Conclusion | Scalar summands are affine restrictions, almost everywhere | Encoder equals c+us+v phi(s) everywhere, with independent u,v |
| Applicable proof ingredient | Section 5: integration on a nondegenerate sum chart yields regularity, then differentiation | Local chart regularization and derivative identification follow this established strategy |

Source: [full theorem and proof](https://arxiv.org/html/1203.5370v2); [publisher record](https://link.springer.com/article/10.1007/s00010-012-0173-7).

For the manuscript's **smooth strictly convex subclass**, gamma has no affine subarc. If one additionally establishes a measurable global factorization R_E=H(sum gamma), Theorem 1.6 applies to each real component, with d=2; continuity upgrades the almost-everywhere conclusion. This conditional implication is enough to establish substantial overlap. It is not legitimate to invoke that theorem directly from the manuscript's original one-way hypothesis.

The present proof establishes factorization only on product charts near regular triples, and then uses fixed unequal-slope anchors. Do not silently replace this statement with global connectedness of all moment fibers: the manuscript has not proved that connectedness. Its self-contained argument avoids that issue and accommodates phi with affine intervals. The difference in hypotheses warrants retaining the lemma, with explicit attribution and a narrower contribution claim.

## Other theorem-level comparisons

| Primary source and inspected locus | Relevant established result | Applicability to this manuscript |
|---|---|---|
| [Wagstaff et al., ICML 2019](https://proceedings.mlr.press/v97/wagstaff19a/wagstaff19a.pdf), Theorem 4.1 and Lemma 4.2 | Exact max computation forces injectivity of the aggregate representation, leading to a topological dimension lower bound | Related collision and topology mechanism, but no affine classification of two-moment encoders. Credit conceptual precedent; do not claim they only provide constructions. |
| [Wagstaff et al., JMLR 2022](https://jmlr.org/papers/volume23/21-0730/21-0730.pdf), Theorems 14–16, Lemma 17, Section 3.3.2 | Necessary/sufficient dimensions for universal representation; fixed-cardinality max injectivity; explicit allowance for particular targets to need fewer dimensions | Does not rule out two-dimensional representations of these fixed targets and does not classify all such encoders. Lemma 17 is a more precise fixed-cardinality comparator than the earlier lemma. |
| [Matkowski and Páles](https://arxiv.org/pdf/1501.02857), Theorems A and D | Equality of scalar continuous monotone quasi-arithmetic generators gives affine equivalence, including fixed arity | Scalar invertible mean readouts and monotone generators are essential premises absent here; this is an analogy rather than a direct proof. The article recalls these equality results rather than originating all of them. |
| [Marley and Ng](https://ac.inf.elte.hu/Vol_041_2013/doi/137_41.pdf), Theorem 1.2 and Theorem 2.1 | Scalar quasi-sum uniqueness and associative m-place representation under coordinate injectivity | The readout is scalar and associative/injective assumptions differ. Theorem 1.2 traces uniqueness to Ng (1973). No direct implication for the planar one-way collision lemma was identified. |
| [Chen, Chen, and Lu](https://arxiv.org/html/2211.15958v4), Theorem 2.1, Theorem 3.1, Example 3.2 | Continuous symmetric functions factor through polynomial algebra generators; moment maps can be singular; Lipschitz targets can have non-Lipschitz moment readouts | Provides existence and warns that readout conditioning is separate. It neither minimizes latent dimension for this fixed scalar target nor supplies its peak-optimal encoder. |

## Recommended edits

1. Add Charalambides to the main related-work section and immediately before the affine lemma. State that local regularization and affine identification are related to the restricted Cauchy–Pexider method.
2. Describe the first contribution as **classification from scalar exactness under continuous encoding**, not discovery of affine uniqueness for moment generators.
3. State the information direction explicitly: encoded collisions preserve moments; equal-dimensional topology provides the reverse local factorization needed for additive rigidity.
4. Avoid claiming that the weaker C1 hypothesis alone constitutes a major novelty. The useful contribution is the complete chain from exactness to a global peak-optimal design and sharp implemented decoder.
5. Keep all global-firstness claims out of the abstract, introduction, and conclusion. A focused comparison cannot certify historical priority.

## Verified bibliography additions

    \bibitem{charalambides2013} M. Charalambides, ``On restricting Cauchy--Pexider functional equations to submanifolds,'' \emph{Aequationes Math.}, vol. 86, no. 3, pp. 231--253, 2013, doi: 10.1007/s00010-012-0173-7.

Optional background reference (not essential once Charalambides and Matkowski–Páles are cited):

    \bibitem{marley2013} A. A. J. Marley and C. T. Ng, ``Quasi-sum representation for an m-place function,'' \emph{Ann. Univ. Sci. Budapest., Sect. Comput.}, vol. 41, pp. 137--143, 2013, doi: 10.71352/ac.41.137.

## Limits of this review

This was a bounded primary-source review, not an exhaustive priority investigation or external peer review. Searches covered vector additive uniqueness, equal-weight moment sums, sufficient-statistic uniqueness, quasi-arithmetic means, and collision invariants. Restricted Cauchy–Pexider results produced the direct substantive lead. Statistical sufficient-statistic search results did not supply a checked theorem matching the fixed-three, distribution-free, one-way premise; that absence is not evidence of novelty. A new 2026 vector-mean preprint appeared in search, but full text was unavailable, so no conclusion here relies on it.

No inspected theorem directly proves the full stated lemma from its original assumptions. This means **a precise distinction has been documented**, not that originality has been proved. If a journal submission is intended, a functional-equations specialist should assess the remaining distinction and contribution weight.
