# Scope of the current two-statistic model

The manuscript uses a separate feature curve at each node, a shared pair of
encoder columns, and separate offsets. `HeterogeneousScore` models the actual
finite input tuples and attained moment set, including singular columns.
`SingularGram` and `HeterogeneousSynthesis` construct planar encoders from
every feasible PSD family without rank or positivity restrictions.

`HeterogeneousAttainment.heterogeneous_sdp_attained` proves general attainment,
including dependent feature families, singular common Gram blocks and zero
optimal score. Compactness is proved in the finite-dimensional image of actual
continuous encoder functions; coefficient independence is not imposed. The
same module proves positivity exactly when the readout is Lipschitz on the
attained moment set, with the Euclidean convention made explicit.

The general node-dependent grid assembly derives actual nodewise C2 norm
bounds, compact sampled feasible sets and attained optima, continuum scaling,
and a uniform quadratic mesh gap. `HeterogeneousDualCertificate` derives the
finite matrix trace identities and the genuine dual upper certificate.

The Gaussian development uses actual nonnegative squared-risk integrals over
all Borel decoders. Local-prior score identities, weighted van Trees, smooth
test density, inverse-Gram variational completeness, changing-Gram limits,
singular exclusion, endpoint-extension achievability and exact Gaussian-law
identifications are proved in separate modules. The final statistical
assembly and manuscript correspondence are detailed in `COVERAGE.md` and
`THEOREM_MAP.md`.

Historical inventories are retained in `historical/v0.2.0/` and
`historical/v0.3.0/`; they describe those earlier versions only.
