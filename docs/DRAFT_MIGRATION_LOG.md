# Draft Migration Log

This file tracks the migration from project notes into the official peer-review manuscript.

## Current migrated files

```text
paper/official_draft_v1.md
paper/main.tex
```

## Source material used

The first official draft is based on the current project route described by:

- `REPORT.md` from the formalization notes;
- `MAPA_TEOREMAS_RH_CURTO.md`;
- `MAPA_TEOREMAS_RH.md`;
- `Transfer.lean` route content;
- `Roadmap.lean` route content;
- `GenuineContinuation.lean` route content;
- `GenuineCover.lean` and `GenuineG11.lean` route content;
- `GenuineBulkConcrete.lean` terminal route content.

## Migration policy

The official manuscript should not copy internal note language directly.

Internal names are converted to review-facing terms according to:

```text
docs/FORMAL_NAMING.md
```

## Current state of the official paper

`paper/main.tex` now contains the review-facing route:

1. formal endpoint;
2. off-critical strip;
3. C2/zeta identity and transfer;
4. regional cover;
5. continuation and genuine C2 operator;
6. near-critical-zero regime;
7. middle-region non-cancellation;
8. edge-region certificate;
9. terminal certificate;
10. Lean theorem correspondence table;
11. reproducibility.

## Remaining editorial steps

1. Expand prose explanations around the C2/zeta identity if needed for readers.
2. Expand prose explanations around the regional cover if needed for readers.
3. Add bibliography entries before a submission PDF is cut.
4. Keep `paper/main.tex`, `LeanC2/PeerReview.lean`, and `docs/THEOREM_MAP_REVIEW.md` synchronized.

## Guardrail

Do not promote historical development notes into the official paper unless they are part of the current theorem map.
