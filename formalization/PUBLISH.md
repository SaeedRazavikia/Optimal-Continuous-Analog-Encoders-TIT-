# Repository and proof version

The Lean project is in [`formalization/`](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/tree/main/formalization) in the paper's GitHub repository. Run `lake exe cache get` and `python3 verify.py` from that directory to reproduce the audit.

The root [GitHub Actions workflow](../.github/workflows/verify-lean.yml) builds and audits this directory on relevant pushes and pull requests. Its [Actions page](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml) provides the remote build status. The files under `verification/` preserve the supplied local build record; they do not by themselves certify a GitHub run.

For a paper citation, use a permanent GitHub link containing the commit SHA instead of only the moving `main` branch. `CITATION.cff` records software citation metadata. Keep the scope statement from `COVERAGE.md`: checked specializations and conditional results do not amount to formalization of every manuscript theorem.
