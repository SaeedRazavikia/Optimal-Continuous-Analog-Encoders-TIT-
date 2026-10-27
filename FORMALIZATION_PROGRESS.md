# Formalization completion — version 0.4.0

The current update completes full heterogeneous rigidity, general SDP
attainment, Gaussian converse and optimization proofs, and general grid
certification for the supplied [Main.tex](Main.tex).

The strict local verification passed **1,198 public declarations in 100
modules**. Relative to the previous current-manuscript archive, this adds
476 declarations in 47 modules. Relative to the older repository artifact,
the verified total increases from 405 declarations in 29 modules. All audited
declarations use only the three standard allowed axioms; no missing conclusion
is inserted as an axiom or admitted proof.

[UPDATE_SUMMARY.md](formalization/UPDATE_SUMMARY.md) details the completed proof
chains. [COVERAGE.md](formalization/COVERAGE.md) retains the remaining formula,
representation and example wrappers. [verification/report.json](formalization/verification/report.json)
contains the final audit and source fingerprints; earlier records are retained
under `formalization/historical/` and are not the current verification evidence.

The repository includes the exact current manuscript used by the correspondence
check as `Main.tex`, while retaining the earlier manuscript layout and source
files. The GitHub workflow runs the pinned build and audit from `formalization/`
when that folder or `Main.tex` changes. The archived local audit and a new CI run
are distinct verification records.
