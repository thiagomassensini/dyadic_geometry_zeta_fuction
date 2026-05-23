# Lean Import Checklist

Use this checklist when importing the Lean formalization into this repository.

Status: completed for the public `LeanC2/` tree on 2026-05-23. The root project files are present and the documented build command succeeds locally.

## 1. Root project files

Add these files at repository root:

```text
lean-toolchain
lakefile.lean or lakefile.toml
lake-manifest.json
```

If the project has additional Lake configuration files, import them too.

## 2. Source tree

Import the Lean source tree:

```text
LeanC2/
```

The review facade already exists at:

```text
LeanC2/PeerReview.lean
```

If the imported tree already contains this file, merge carefully.

## 3. Required internal module

The facade currently imports:

```lean
import LeanC2.Analytic.GenuineBulkConcrete
```

Make sure this module exists after import.

## 4. Expected public facade

The public facade should expose:

```lean
C2.PeerReview.RiemannHypothesis_of_offCriticalNonvanishing
C2.PeerReview.ZetaNonvanishing_of_C2Nonvanishing
C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing
C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing_offCriticalIdentity
C2.PeerReview.OffCriticalNonvanishing_of_regionalCover
C2.PeerReview.RiemannHypothesis_of_regionalCover
C2.PeerReview.RiemannHypothesis_of_terminalCertificate
```

## 5. CI command

After import, run locally:

```bash
lake exe cache get || true
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

The same command is used by GitHub Actions.

## 6. Common failure modes

### Missing Lean project target

If Lean cannot find `LeanC2`, check the Lake configuration and the root module layout.

### Missing terminal theorem

If the facade cannot find a terminal theorem, the imported source tree may be older than the theorem map.

### Missing notation

If `ℂ` is unavailable, add the required import or replace it with `Complex`.

### CI timeout

The workflow timeout is 120 minutes. If the full build is too heavy, split the job into staged builds.

## 7. Public route policy

Do not expose historical scratch files as the public proof route unless they are cleaned and mapped in `docs/THEOREM_MAP_REVIEW.md`.
