# Project Report

## Current status

This repository is the clean peer-review workspace for the dyadic C2 route related to the Riemann zeta function.

Current contents:

- review-facing documentation;
- public theorem naming conventions;
- theorem map for reviewers;
- reproducibility guide;
- Lean facade module at `LeanC2/PeerReview.lean`;
- GitHub Actions workflow prepared for the Lean build.

The full Lean source tree has not yet been imported into this repository.

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

The CI checks whether the repository root contains:

```text
lean-toolchain
lakefile.lean or lakefile.toml
```

If these files are absent, the workflow reports a warning and skips the Lean build.

After the Lean project is imported, the workflow runs:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

## Immediate next step

Import the complete Lean source tree and root Lake files into this repository, then run the CI build.
