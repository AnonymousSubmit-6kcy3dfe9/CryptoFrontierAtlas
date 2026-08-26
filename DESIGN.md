# CryptoFrontierAtlas: Public Dataset and Frontend Design

## 1. Purpose

CryptoFrontierAtlas is an English-language, static atlas of public open
questions in cryptography. The current corpus is restricted to symmetric-key
cryptography. Each record describes a traceable problem statement, its formal
scope, public literature, and the publicly auditable evidence available for
its current status.

The first release is an index and presentation layer with three explicitly
cleared, scoped Lean formalizations. It is **not** a repository for private
proofs, uncleared answers, or an assertion that every manuscript in the source
directory has been independently reviewed. Other internal solutions remain
outside the public data tree until they are cleared for release.

## 2. Corpus boundary

The source directory contains multiple manuscript versions, wrappers, PDFs,
build products, and problem families. The dataset unit is an atomic
mathematical statement, not a source file. Duplicate drafts are represented by
one canonical record and a source-version relation.

### Initial audit

| Source family | Atomic records | Decision | Rationale |
| --- | ---: | --- | --- |
| Balanced 8-variable nonlinearity | 1 | Include | Public search target with a traceable literature origin. The sharp maximum 116, including the complete bridge and witness, has a repository-checked Lean formalization. |
| Carlet 13.2(3) quadratic/RM formulas | 1 | Exclude | The formulas are classical (Sloane--Berlekamp and MacWilliams); the local manuscript is a rederivation, not a current open frontier. |
| Carlet 13.3(14) affine derivatives of bent functions | 1 | Include | Explicit public book problem. |
| Carlet 13.7(7) Hamming-layer algebraic immunity | 1 | Include | Explicit public book problem; current result is only first-order/asymptotic progress. |
| Carlet--Feukoua--Salagean stability questions | 2 | Include | Two public source questions; the newer manuscript is canonical and the older OP1 manuscript is superseded. |
| Tu--Deng conjecture | 1 | Include | Public conjecture with an independent public proof claim that must be cited and priority-audited. |
| Vectorial nonlinearity | 1 | Include | Publicly discussed open optimization problem; current result is a non-tight general bound. |
| Kolsch Problem 6.5.4 | 1 | Include | Public problem; only the primitive F4/direct-XOR branch is addressed. |
| Derbez et al. GFN diffusion challenge | 1 | Include | One source-level challenge covering the 38- and 40-branch parameter instances. |
| Derbez--Euler expanded equivalence | 1 | Include | Publicly stated equivalence-class problem. |
| Tezcan--Ozbudak differential-factor conjecture | 1 | Include | Public conjecture; the unrestricted and permutation readings have different outcomes. |
| Bogdanov d+1-round active-S-box conjecture | 1 | Include | Public thesis conjecture; the source must be cited separately from the DCC 2(d+1)-round statement. |
| Kaleyski Conjecture 21 | 1 | Include | Public conjecture; only the second identity is addressed, so the record remains partial. |
| BCT maximal-table rigidity | 1 | Exclude | The manuscript explicitly identifies this as a derived theorem-level slice, not a literature-stated open question. |

This produced 13 initial public problem records. Subsequent issue ingestion
expanded the public index to 49 records; the excluded items may still be kept
in private audit notes, but must not appear in the public question index. The
24-count taxonomy table is a target inventory for the broader atlas, not a
claim about the current record count.

## 3. Public disclosure policy

Every record has an explicit disclosure field. The release may link a
reviewed, scoped artifact when its exact verification boundary is stated in
the source and metadata. It never embeds private proof text, private PDFs, or
local absolute paths. A record may state that a complete internal resolution
is withheld while exposing a partial, independently replayable artifact; the
artifact must not be presented as a complete proof.

Public artifacts must have a stable URL, a license, and a reproducible commit
or checksum. A manuscript may be listed as a source without being copied into
the repository. Repository Lean artifacts use a relative `data/lean` path,
record their toolchain and replay command, and bind both the public wrapper
and the complete Lean source tree to an immutable Git commit and SHA-256
digest.

Anonymous or unpublished internal progress is outside the public disclosure
boundary and is omitted from the public timeline. Every published timeline
event therefore has an identifiable source or public verification citation.

## 4. Status model

Status dimensions are intentionally independent:

- `source_kind`: `explicit_open_problem`, `explicit_conjecture`,
  `open_challenge`, or `public_thesis_conjecture`.
- `public_mathematical_status`: `open`, `partial_progress`, `resolved`,
  `refuted`, `corrected`, or `historically_settled`.
- `public_verification_status`: `none`, `computer_checked`,
  `externally_claimed`, `externally_reproducible`, or `repository_checked`.
- `peer_review_status`: `not_submitted`, `preprint`, `under_review`,
  `published`, or `independently_audited`.
- `disclosure`: `problem_only` or `public_progress`.

`lean.status: partial` means that the repository file proves only the named
intermediate lemmas, finite certificates, or witness properties. It does not
upgrade `public_mathematical_status` to resolved. `lean.status: complete`
records a complete formalization of the scoped theorem, while
`public_verification_status: repository_checked` records that its public source
replays in the pinned repository toolchain.

For example, the permutation reading of the Tezcan--Ozbudak statement can be
described as public progress while the unrestricted reading is refuted. The
Kaleyski record is partial because one identity remains open. A Lean claim
whose source is not vendored in this repository remains
`externally_claimed`, never `repository_checked`.

## 5. Metadata contract

The canonical machine-readable contract is
`data/schema/problem.schema.json`. Each public record contains:

- stable `id` and `group_id`;
- English `title`, concise `summary`, and a Markdown/LaTeX formal statement;
- `scope` with domains, parameters, assumptions, and unresolved remainder;
- primary and secondary taxonomy assignments plus free-form topic tags;
- `source` citations with problem kind, locator, DOI/ePrint/URL when known;
- a public literature timeline, with citations for every claim;
- independent status dimensions listed above;
- public artifact references, checksums, licenses, and version relations;
- a Lean field that can remain empty without implying absence of a proof;
- related, superseded, and superseding record identifiers.

The schema is designed for hand-audited first-party JSON. Automated extraction
from LaTeX is a suggestion generator only; it is not the publication path.

## 6. Taxonomy governance

`data/taxonomy.json` is versioned independently from individual records. The
atlas has three cryptographic areas:

1. Symmetric cryptography
2. Asymmetric cryptography
3. Others

The present release populates only symmetric cryptography. Its
`research_topic_category` hierarchy has three groups: mathematical foundations
and structural questions, design of cryptographic primitives, and
cryptanalysis. Each group exposes the complete leaf set in `data/taxonomy.json`,
including explicit fallback leaves for questions that do not fit a narrower
subcategory.

Each record has exactly one primary leaf and may have multiple secondary
leaves. Topic tags capture cross-cutting notions such as `algebraic-immunity`,
`boomerang`, `gfn-diffusion`, and `xor-complexity`; formal verification is an
evidence facet, not a cryptographic category. The frontend exposes both group
and leaf-level filtering and renders the full area/group/leaf path for every
record.

The taxonomy reserves explicit leaves for algebraic structures, Boolean and
vectorial Boolean functions, combinatorics and finite geometry, coding theory,
block ciphers, S-boxes and nonlinear components, all listed cryptanalysis
families, and the three `other` fallbacks. Existing IDs
are never renamed; deprecations use `superseded_by`.

## 7. Repository layout

```text
data/
  problems/                 # public JSON records only
  schema/problem.schema.json
  taxonomy.json
  README.md
  lean/                     # independently replayable Lean project
src/                        # static frontend (Vite + React + TypeScript)
public/                     # favicon, generated search index, static assets
docs/                       # contributor and release documentation
scripts/                    # schema, citation, and disclosure checks
```

Private proofs and uncleared answer material must live outside the repository.
The repository must not contain paths beginning with `/data_600G/`, build
debris (`.aux`, `.log`, `.fls`, `.fdb_latexmk`, `__pycache__`), or unreviewed
manuscript copies.

## 8. Frontend information architecture

The first screen is the searchable atlas, not a marketing landing page.

- **Atlas view:** searchable table/grid with title, primary category, source
  kind, public status, disclosure, and last review date.
- **Filter bar:** category, subcategory, status, source kind, verification
  status, peer-review status, and topic tags. Filters are URL-addressable.
- **Question detail:** title, compact natural-language summary, formal
  statement, assumptions, source citation, public progress timeline, scope
  limits, artifacts, and related questions.
- **Evidence panel:** distinguishes mathematical status, computation,
  external Lean claims, and repository-checked artifacts. Empty Lean data is
  rendered as unavailable, never as a broken code viewer; scoped source links
  are rendered as public artifacts.
- **Taxonomy view:** shows counts generated from JSON, with the distinction
  between primary counts and multi-label tag counts.

The site is static and deploys through GitHub Pages and GitHub Actions. KaTeX
renders formulas from sanitized record fields. No server-side search or
private endpoint is required.

## 9. Validation and release gates

Every pull request must pass:

1. JSON Schema validation for every record;
2. taxonomy ID and status enum validation;
3. citation completeness checks for every source claim;
4. URL and checksum format checks;
5. disclosure checks rejecting private absolute paths, local proof fields,
   answer-bearing artifact names, and non-English public fields in v0.1;
6. a production frontend build.

Each release is tagged with a dataset version, a taxonomy version, a changelog,
and a generated record count. Counts are computed from primary categories and
must never be hard-coded in the frontend.

## 10. Attribution and licensing

The public dataset text and metadata use CC BY 4.0. Website and validation code
use Apache-2.0. Individual external artifacts retain their original licenses
and are linked rather than silently relicensed. `CITATION.cff` must identify
the maintainers, release version, repository URL, and the preferred citation.

Before the first public push, author names, institutional affiliation,
corresponding contact, source permissions, and the status of any anonymous
manuscript must be audited manually.

## 11. Implementation phases

1. Freeze the taxonomy and schema; create the audited public records with
   problem statements and public citations only.
2. Add citation and disclosure CI, `README.md`, `CITATION.cff`, licenses, and
   contribution policy.
3. Build the static atlas and detail pages from JSON.
4. Run a source audit and a second-person metadata review.
5. Publish the GitHub Pages release with cleared public proofs, independent
   artifact checksums, explicit trust boundaries, and release notes.
