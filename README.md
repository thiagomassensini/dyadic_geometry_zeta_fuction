# Dyadic Geometry of the Zeta Function

This repository is the peer-review workspace for the C2 / dyadic-carry geometry route connected to the Riemann zeta function.

The goal is to keep the public presentation separated from historical scratch work and to expose a stable Lean entry point for external audit.

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
LeanC2/                  Lean source tree and peer-review facade
.github/workflows/       CI workflows
```

The review-facing inventory for bounds, certificates, residual budgets, and
oscillatory witnesses is in `docs/BOUNDS_CERTIFICATES_WITNESSES.md`.

## Main verification command

The Lean project files are present at the repository root. The main verification command is:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

The repository includes `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`; CI runs the same build command.

## Public naming policy

Internal discovery names are not used as theorem names in the review-facing paper.

For example:

- the middle-region cancellation argument is exposed as a `resolvent non-cancellation mechanism`;
- the finite dyadic block is exposed as a `dominant four-level block`;
- the correction seed is exposed as a `calibrated residual seed`.

See `docs/FORMAL_NAMING.md` and
`docs/BOUNDS_CERTIFICATES_WITNESSES.md`.

## Status

The formalization has been imported into the public `LeanC2/` tree. Historical scratch material is kept outside the public route unless it is cleaned, renamed, and mapped through `docs/THEOREM_MAP_REVIEW.md`.
