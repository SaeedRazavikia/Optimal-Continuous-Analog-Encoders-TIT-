# Publish the artifact

The suggested repository name is `analog-moment-lean`. This directory is ready
to upload; it does not contain a configured remote or a claimed repository URL.

1. Sign in to GitHub and create an empty repository with that name under the
   intended account. Choose **Public** if readers should inspect the proofs.
2. Upload this directory's contents at the repository root. Include `.github/`
   and `.gitignore`; exclude any `.lake/` directory or Python cache files.
3. Open the repository's **Actions** tab and inspect the **Verify Lean proofs**
   run. The workflow installs the pinned compiler, fetches the pinned mathlib
   cache, builds the project, and audits all advertised declarations.
4. After a successful run, copy the permanent link to that commit from GitHub.
   Use that link in the manuscript so readers can identify the exact proof
   version, and retain the scope statement in the paper and `COVERAGE.md`.

For a local Git upload, replace `REPOSITORY_URL` with the URL GitHub displays:

```sh
git init
git add .
git commit -m "Add audited Lean formalization"
git branch -M main
git remote add origin REPOSITORY_URL
git push -u origin main
```

The recorded verification files describe the supplied local build. The first
GitHub run provides a separate build record; uploading the source alone does
not establish that this run has succeeded.
