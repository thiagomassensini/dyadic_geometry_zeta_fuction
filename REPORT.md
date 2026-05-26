# Project Report

## Current status

This repository is the clean peer-review workspace for the dyadic C2 route related to the Riemann zeta function.

Current contents:

- review-facing documentation;
- public theorem naming conventions;
- theorem map for reviewers;
- bounds, certificates, residual budgets, and witness inventory;
- reproducibility guide;
- imported Lean source tree under `LeanC2/`;
- Lean facade module at `LeanC2/PeerReview.lean`;
- Lake project files at the repository root;
- GitHub Actions workflow configured for the Lean build.

## Formal endpoint

The intended formal endpoint is the official mathlib proposition:

```lean
RiemannHypothesis
```

The public Lean facade exposes the route through:

```lean
import LeanC2.PeerReview
```

with the final public wrapper:

```lean
C2.PeerReview.RiemannHypothesis_of_terminalCertificate
```

The public facade also exposes review-facing names for the bound packages,
certificates, residual budgets, and oscillatory witnesses listed in
`docs/BOUNDS_CERTIFICATES_WITNESSES.md`.

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

Verified locally on 2026-05-25 with Lean/mathlib `v4.29.1`:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

Result:

```text
Build completed successfully (8290 jobs).
```

## External CI status

The latest observed GitHub Actions run on `origin/main` succeeded for commit
`abe699b06294c0082ed5270a56a8be8ceb32436b`.

After local review-facing changes are pushed, GitHub Actions should be checked
again for the new commit.
