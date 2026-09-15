# Repository and proof version

This revision extends the Lean project from repository commit `7a513ed38147a73f109f9b184dafba59c17ee89b` with four modules for the unified two-statistic extension. Use the proof sources, audit manifest, and verification records from the same commit. A moving branch name does not uniquely identify the audited source.

Run `lake exe cache get` and `python3 verify.py` from this revision's `formalization/` directory. The exact source/configuration hashes and theorem dependencies are recorded in `verification/report.json`. Toolchain and dependency revisions remain pinned. The supplied local audit is separate from a GitHub Actions run; the repository's verification workflow records the latter.

For an artifact citation, use a permanent link containing the reviewed commit SHA. `CITATION.cff` records software metadata. Keep the scope statements in `COVERAGE.md` and `EXTENSION_SCOPE.md`: the new common-completion and constructive design results do not complete the full extended continuous-encoder theorem.
