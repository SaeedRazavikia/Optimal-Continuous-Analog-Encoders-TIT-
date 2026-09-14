# Submission preparation

Prepared for *IEEE Transactions on Information Theory*, 13 September 2026. This revision implements the requested positioning and presentation work. It does not schedule another external review or fresh-environment reproduction.

## Prepared material

| Material | State |
|---|---|
| Scientific positioning | The introduction centers necessary features, exact peak-constrained robustness, and the global constrained small-noise frontier. Established mathematical tools receive credit. |
| Unpublished draft | The author confirmed that the bivariate draft is not planned for submission. Its citation and comparison paragraph have been removed. The historical comparison is retained only as an internal development note; the draft is excluded from the delivery. |
| Cover letter | `COVER_LETTER_DRAFT.md` provides substantive editable text. Its author-finalization note identifies facts unavailable from the files. |
| References | Sagnol and Papp now use verified journal bibliographic records. Previously inspected preprint proof loci remain in the literature notes. |
| Presentation | Native TikZ/PGFPlots figures and their data accompany the manuscript, explaining the MAC, encoder curve, peak geometry, and robustness–accuracy choices. |
| Source package | The manuscript, editable figures, numerical data, and build instructions belong together. Internal working notes need not be uploaded to the journal. |

## Author information still needed

1. Confirm the final author list, affiliations, corresponding-author details, and identifiers requested by the submission system. The draft retains Saeed Razavikia and the KTH affiliation/email supplied with the source.
2. Confirm this paper's submission history and identify any related conference versions or other submissions. The bivariate draft is not planned for submission, as confirmed by the author.
3. Supply funding acknowledgments and applicable conflict or permission information. Do not replace unknown facts with “none.” Confirm the final manuscript and substantive AI-assistance disclosure after author review.
4. Choose the publication-access option and complete the journal's declarations at submission. The package contains no invented author-approval, exclusivity, funding, or originality certification.

## Verified requirements and verification limits

IEEE directs authors to the journal's **About Journal → Publication Details** page for current instructions and routes submission through the [IEEE Publishing Portal](https://publishingportal.ieee.org/). Follow the live instructions when uploading; the source ZIP containing internal notes is not automatically the journal submission bundle. [IEEE submission-process instructions](https://journals.ieeeauthorcenter.ieee.org/submit-your-article-for-peer-review/the-ieee-article-submission-process/).

The journal-specific [TIT society page](https://www.itsoc.org/it-trans) returned HTTP 403 during this check. The indexed IEEE “Information for Authors” PDF available through search was an older record, so it was **not** used to certify current page limits, margins, fees, or portal-specific requirements. The source uses `IEEEtran` journal format. Final journal-specific formatting and fee choices require the live instructions; this is a verification limit, not evidence that the current layout violates a rule.

IEEE requires related prior publications and submissions to be disclosed and their differences explained. Its policy also requires disclosure of substantive AI-generated text, figures, and code, identifying the system, affected article parts, and extent of assistance. Routine grammar editing alone is treated differently. The present work includes substantive assistance, so the prepared acknowledgment must remain accurate to the final content. [IEEE submission, prior-publication, and AI-content policies](https://journals.ieeeauthorcenter.ieee.org/become-an-ieee-journal-author/publishing-ethics/guidelines-and-policies/submission-and-peer-review-policies/).

## Prepared AI-assistance acknowledgment

This text records work performed without asserting that author verification has already occurred:

> The author used OpenAI ChatGPT/Codex to assist with drafting and revision throughout the manuscript and appendices, mathematical derivations and proof development, literature comparison, numerical and certificate code development, and preparation of the TikZ/PGFPlots figures. The assistance included substantive content generation and language editing.

Review this statement against the final manuscript. Add an author-verification statement only after that verification has occurred.

## Submission sequence after author finalization

1. Consult the journal's current instructions, select the article type, and prepare the exact files requested by the system.
2. Upload the final manuscript and requested source/supplementary files; supply any disclosures requested by the system based on the actual publication and submission history.
3. Enter author metadata, funding, access choice, and applicable declarations. Inspect the system-generated PDF and figures.
4. The corresponding author reviews and submits the completed package. No submission or external communication has occurred here.

The verified Lean artifact is documented in `FORMALIZATION.md`; pinned dependencies, proof sources, a complete manuscript coverage inventory, and the verification report are included in `formalization/`. The expanded artifact proves operational variance optimality over all quadratic coefficient curves at every positive power, plus general collision, coefficient optimization, sharp decoding, and synthesis/implementation results. The entire manuscript and unrestricted continuous-encoder theorem remain unformalized.
