# Reproducibility Guide

This guide records the commands and files needed to audit the formal side of the project.

## Required files at repository root

The Lean CI expects and this repository provides:

```text
lean-toolchain
lakefile.lean
lake-manifest.json
LeanC2/
```

The workflow runs the formal build from these root project files.

## Main Lean verification command

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

This is the command used by the GitHub Actions workflow once the Lean project is present.

The repository is pinned to Lean/mathlib `v4.29.1` through `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`.

## Expected formal endpoint

The formal endpoint is the official mathlib proposition:

```lean
RiemannHypothesis
```

The review-facing terminal theorem should be read as a route to this endpoint, not as a separate local replacement for RH.

## Main documentation files

- `README.md` — repository overview.
- `docs/FORMAL_NAMING.md` — public naming conventions.
- `docs/THEOREM_MAP_REVIEW.md` — theorem map for reviewers.
- `docs/REPRODUCIBILITY.md` — this file.
- `LeanC2/PeerReview.lean` — review-facing Lean facade, once the Lean tree is imported.
- `.github/workflows/lean.yml` — CI workflow.

## Suggested local audit sequence

After cloning the repository:

```bash
cat lean-toolchain
lake exe cache get || true
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

Then inspect the theorem map:

```bash
sed -n '1,260p' docs/THEOREM_MAP_REVIEW.md
```

## What the CI checks

When the Lean project is present, the CI checks the formal Lean build target.

It does not check prose claims in the paper, numerical experiments, generated PDFs, or external datasets unless explicit jobs are added later.

## What reviewers should verify manually

1. The paper theorem names match `docs/THEOREM_MAP_REVIEW.md`.
2. The theorem map points to public facade declarations in `LeanC2/PeerReview.lean` when available.
3. The endpoint is mathlib's `RiemannHypothesis`.
4. The build command succeeds once the Lean project files are present.
5. Any remaining mathematical hypotheses are clearly stated as inputs, not silently hidden.
6. Historical notes are not mistaken for current pending obligations.

## Historical-note policy

Some imported project files may contain words such as pending, missing, bottleneck, or next step.

For review, the normative state must be taken from the current report and the compiled Lean route. Historical development notes should be read as cumulative project history unless explicitly promoted into the review-facing theorem map.

## Minimal audit claim

The minimal reproducibility claim, after the Lean project is present, is:

```text
The command
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
checks the formal route to mathlib RiemannHypothesis through the review-facing facade.
```

Anything beyond that should be documented as an additional reproducibility layer.
