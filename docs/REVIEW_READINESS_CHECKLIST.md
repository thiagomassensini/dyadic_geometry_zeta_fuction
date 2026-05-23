# Review Readiness Checklist

Use this checklist before sending the repository or paper to external reviewers.

## Repository structure

- [ ] Root contains `lean-toolchain`.
- [ ] Root contains `lakefile.lean` or `lakefile.toml`.
- [ ] Root contains `lake-manifest.json`.
- [ ] Root contains the complete `LeanC2/` source tree.
- [ ] `LeanC2/PeerReview.lean` imports the current terminal route.
- [ ] `.github/workflows/lean.yml` runs the intended build command.

## Formal build

- [ ] `lake exe cache get || true` completes or safely falls back.
- [ ] `lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2` succeeds locally.
- [ ] GitHub Actions succeeds on `main`.
- [ ] The public facade compiles.

## Theorem map

- [ ] `docs/THEOREM_MAP_REVIEW.md` lists the paper-facing theorem names.
- [ ] Each paper-facing name maps to a Lean facade declaration or an internal declaration.
- [ ] The final theorem target is mathlib `RiemannHypothesis`.
- [ ] Wrapper theorems are separated from mathematical content theorems.

## Paper

- [ ] The title is neutral.
- [ ] The abstract states the formal endpoint precisely.
- [ ] The introduction separates the C2 construction from the RH transfer.
- [ ] The middle-region theorem uses formal terminology.
- [ ] Historical/internal names are avoided in theorem statements.
- [ ] The reproducibility section points to the CI command.
- [ ] The paper states which certificates are inputs to the terminal theorem.

## Naming

- [ ] Use `resolvent non-cancellation mechanism` instead of internal mnemonic names.
- [ ] Use `dominant four-level block` instead of informal block names.
- [ ] Use `calibrated residual seed` instead of informal seed names.
- [ ] Use `off-critical regional cover` for the cover layer.
- [ ] Use `terminal certificate` for the final packaged route.

## Reviewer audit points

- [ ] Can a reviewer identify the final Lean theorem?
- [ ] Can a reviewer identify the exact build command?
- [ ] Can a reviewer see where zeta enters?
- [ ] Can a reviewer distinguish formal plumbing from analytic inputs?
- [ ] Can a reviewer reproduce the build from a clean clone?

## Ready condition

The repository is review-ready only when the paper, theorem map, facade module, and CI build all agree on the same route.
