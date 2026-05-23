# Draft Migration Log

This file tracks the migration from project notes into the official peer-review manuscript.

## Current migrated file

```text
paper/official_draft_v1.md
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

## Current state of the official draft

`paper/official_draft_v1.md` currently contains the route skeleton:

1. formal endpoint;
2. off-critical strip;
3. C2/zeta identity and transfer;
4. regional cover;
5. continuation and genuine C2 operator;
6. near-critical-zero regime;
7. middle-region non-cancellation;
8. edge-region certificate;
9. terminal certificate;
10. reproducibility.

## Next migration steps

1. Expand the C2/zeta identity section from the transfer and continuation files.
2. Expand the regional cover section from the roadmap interfaces.
3. Expand the near-critical-zero section from the continuation/G11 notes.
4. Expand the middle-region section using formal names only.
5. Add a theorem correspondence table matching the paper to `LeanC2/PeerReview.lean`.
6. Convert the Markdown draft into `paper/main.tex` once the structure stabilizes.

## Guardrail

Do not promote historical development notes into the official paper unless they are part of the current theorem map.
