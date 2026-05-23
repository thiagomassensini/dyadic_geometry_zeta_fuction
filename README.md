# Dyadic Geometry of the Zeta Function

This repository is the clean peer-review workspace for the C2 / dyadic-carry geometry route connected to the Riemann zeta function.

The goal is to keep the public presentation separate from historical scratch work.

## Review-facing route

The intended formal route is:

```text
C2 local certificates
  -> off-critical regional cover
  -> off-critical nonvanishing of the C2 operator
  -> C2/zeta identity on the required domain
  -> off-critical nonvanishing of riemannZeta
  -> mathlib RiemannHypothesis
```

## Repository layout

```text
docs/                    Review-facing documentation
paper/                   Paper draft and outline
LeanC2/                  Lean source tree, once imported
.github/workflows/       CI workflows
```

## Main verification command

Once the Lean project files are present at the repository root, the intended verification command is:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

Until the Lean project is imported, CI reports a warning and skips the build.

## Public naming policy

Internal discovery names are not used as theorem names in the review-facing paper.

For example:

- `anti-milagre` becomes `resolvent non-cancellation mechanism`.
- `quarteto` becomes `dominant four-level block`.
- `seed` becomes `calibrated residual seed`.

See `docs/FORMAL_NAMING.md`.

## Status

Fresh repository for the peer-review version.  Historical material should only be imported after being cleaned, renamed, and mapped to the public theorem route.
