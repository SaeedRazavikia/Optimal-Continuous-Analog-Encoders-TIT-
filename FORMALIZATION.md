# Formal verification

The current Lean artifact is in [formalization/](formalization/). Use its [README](formalization/README.md), [theorem map](formalization/THEOREM_MAP.md), and [coverage inventory](formalization/COVERAGE.md) as the authoritative description of this revision.

The project now checks general two-statistic coefficient design and attainment, the general sharp decoder and Gaussian small-noise trace, the continuous attained Gram frontier and explicit quadratic frontier, enclosing-ellipse equivalence, C² grid certification, dissimilarity transfer, and approximate-computation stability conditional on exact-class identification. It also checks the continuous converse's smoothing, dense propagation, and endpoint integration components.

The full unrestricted continuous-encoder converse remains unfinished: exactness and common-completion identification must still be connected to the local continuous charts through planar invariance of domain. The analytic identification criterion, general endpoint-gradient specializations, and other obligations listed in the coverage inventory also remain unverified. Compilation certifies the formal statements written, not missing steps of the paper.

From formalization, run `lake exe cache get` followed by `python3 verify.py`. The report records the pinned versions, theorem dependencies and exact source hashes. No unfinished proof or additional mathematical axiom is accepted. The supplied local audit and the repository's GitHub Actions record are separate evidence.
