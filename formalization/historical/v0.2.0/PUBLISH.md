# Repository and proof version

Version 0.2.0 expands the unified two-statistic development and the decoder, probabilistic design, certification, and approximation proofs. It extends the project originally published at repository commit 7a513ed38147a73f109f9b184dafba59c17ee89b.

Use proof sources, audit manifest, and verification records from the same revision. The exact source/configuration hashes and theorem dependencies are in verification/report.json. Run `lake exe cache get` and `python3 verify.py` from formalization to reproduce them. The compiler and mathlib revisions remain pinned.

The manuscript cites an immutable proof commit. A moving branch does not uniquely identify an audited source. CITATION.cff records software metadata; use the desired commit SHA in a permanent artifact link. The local audit and GitHub Actions runs are separate records.

The coverage inventory and scope documents are part of the artifact. This release does not certify the complete unrestricted continuous-encoder converse or every proof in the manuscript.
