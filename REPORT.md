# Project Report

## Current status

This repository is the clean peer-review workspace for the dyadic C2 route related to the Riemann zeta function.

Current contents:

- review-facing documentation;
- public theorem naming conventions;
- public English map of the main route;
- theorem map for reviewers;
- staged Lean module layout for the concrete bulk route;
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

The current route is summarized for reviewers in `docs/MAIN_ROUTE_MAP.md`.

The former monolithic concrete bulk implementation is split under
`LeanC2/Analytic/GenuineBulkConcrete/`. The original module
`LeanC2.Analytic.GenuineBulkConcrete` remains as a stable facade import.

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

Verified locally on 2026-05-26 with Lean/mathlib `v4.29.1`:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

Result:

```text
Build completed successfully (8297 jobs).
```

## External CI status

The latest pushed audit commit should be checked against the `Lean C2 CI`
workflow before external review. The required green job is:

```text
lake build LeanC2 peer-review route
```
