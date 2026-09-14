# Environment note

The recorded verification ran in a managed Linux workspace without the usual
/proc executable symlinks. The official Lean 4.24.0 release binary was used
without modification. A small compatibility library supplied the calling
process executable path from AT_EXECFN when the corresponding /proc readlink
was unavailable. Its source is included here. It does not alter Lean proof
checking, mathematical definitions, or filesystem access controls.

Shared-library search paths were set explicitly for this workspace. Neither
this adapter nor special paths are normally needed on a standard Linux Lean
installation; use the ordinary commands in the root README.

In addition to the reproducible build and axiom audit, the command
`lake env lean --trust=0 Audit.lean` completed successfully. Its output is in
`verification/kernel-recheck.log`. This asks Lean to type check imported
modules as well. This was a check in the same workspace, not an external
review or a separate-machine replication.

`verification/runtime-record.json` records hashes of the compiler executable,
shared library, and local adapter used for the check. Toolchain binaries and
compiled third-party dependencies are not included in the source archive.
