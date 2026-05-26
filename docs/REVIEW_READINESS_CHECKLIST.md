# Review Readiness Checklist

Use this checklist before sending the repository or paper to external reviewers.

## Repository structure

- [x] Root contains `lean-toolchain`.
- [x] Root contains `lakefile.lean` or `lakefile.toml`.
- [x] Root contains `lake-manifest.json`.
- [x] Root contains the complete `LeanC2/` source tree.
- [x] `LeanC2/PeerReview.lean` imports the current terminal route.
- [x] `.github/workflows/lean.yml` runs the intended build command.

## Formal build

- [x] `lake exe cache get || true` completes or safely falls back.
- [x] `lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2` succeeds locally.
- [x] GitHub Actions succeeds on `main` for the latest pushed audit commit.
- [x] The public facade compiles.

## Theorem map

- [x] `docs/THEOREM_MAP_REVIEW.md` lists the paper-facing theorem names.
- [x] Each paper-facing name maps to a Lean facade declaration or an internal declaration.
- [x] The final theorem target is mathlib `RiemannHypothesis`.
- [x] Wrapper theorems are separated from mathematical content theorems.

## Paper

- [x] The title is neutral.
- [x] The abstract states the formal endpoint precisely.
- [x] The introduction separates the C2 construction from the RH transfer.
- [x] The middle-region theorem uses formal terminology.
- [x] Historical/internal names are avoided in theorem statements.
- [x] The reproducibility section points to the CI command.
- [x] The paper states which certificates are inputs to the terminal theorem.

## Naming

- [x] Use `resolvent non-cancellation mechanism` instead of internal mnemonic names.
- [x] Use `dominant four-level block` instead of informal block names.
- [x] Use `calibrated residual seed` instead of informal seed names.
- [x] Use `off-critical regional cover` for the cover layer.
- [x] Use `terminal certificate` for the final packaged route.

## Reviewer audit points

- [x] Can a reviewer identify the final Lean theorem?
- [x] Can a reviewer identify the exact build command?
- [x] Can a reviewer see where zeta enters?
- [x] Can a reviewer distinguish formal plumbing from analytic inputs?
- [x] Can a reviewer reproduce the build from a clean clone? Latest observed GitHub Actions run on `origin/main` succeeded.

## Ready condition

The repository is review-ready only when the paper, theorem map, facade module, and CI build all agree on the same route. After any later local change is pushed, the CI status should be refreshed for that new commit.
