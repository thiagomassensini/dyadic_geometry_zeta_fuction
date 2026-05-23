# Project Report

## Current status

This repository is the clean peer-review workspace for the dyadic C2 route related to the Riemann zeta function.

Current contents:

- review-facing documentation;
- public theorem naming conventions;
- theorem map for reviewers;
- reproducibility guide;
- imported Lean source tree under `LeanC2/`;
- Lean facade module at `LeanC2/PeerReview.lean`;
- Lake project files at the repository root;
- GitHub Actions workflow prepared for the Lean build.

## Formal endpoint

The intended formal endpoint is the official mathlib proposition:

```lean
RiemannHypothesis
```

The public Lean facade is expected to expose the route through:

```lean
import LeanC2.PeerReview
```

with the final public wrapper:

```lean
C2.PeerReview.RiemannHypothesis_of_terminalCertificate
```

## CI behavior

The repository root contains:

```text
lean-toolchain
lakefile.lean
lake-manifest.json
```

The workflow runs:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

## Local verification

Verified on 2026-05-23 with Lean/mathlib `v4.29.1`:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

Result:

```text
Build completed successfully (8290 jobs).
```

## Immediate next step

Keep the public facade, theorem map, paper draft, and CI build command synchronized as the formal route changes.
