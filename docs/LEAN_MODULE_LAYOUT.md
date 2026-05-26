# Lean Module Layout

This document records the review-facing Lean module layout after splitting the
large concrete bulk file.

The stable public import remains:

```lean
import LeanC2.Analytic.GenuineBulkConcrete
```

That module is now a facade. The implementation is staged under:

```text
LeanC2/Analytic/GenuineBulkConcrete/
```

## Concrete bulk route modules

| Module | Role |
| --- | --- |
| `LeanC2.Analytic.GenuineBulkConcrete.Base` | Concrete/genuine bulk adapters, continued balancing-seed model, pinned near/bulk/edge cover data. |
| `LeanC2.Analytic.GenuineBulkConcrete.ConcreteEstimates` | Concrete regional estimates, scalar reductions, quartet estimates, expanded exact-zeta dominance and canonical scalar constants. |
| `LeanC2.Analytic.GenuineBulkConcrete.ExpandedScalar` | Expanded scalar cover, local scalar-bulk packages, canonical expanded-scalar middle-region data. |
| `LeanC2.Analytic.GenuineBulkConcrete.ComponentRoutes` | Component truncation and resolvent-note middle-region packages. |
| `LeanC2.Analytic.GenuineBulkConcrete.Terminal` | Canonical closed/scaled middle data and the terminal certificate package ending in `RiemannHypothesis`. |
| `LeanC2.Analytic.GenuineBulkConcrete.ContinuationRoutes` | Continuation-driven middle-region constructors and genuine-central resolvent non-cancellation packages. |
| `LeanC2.Analytic.GenuineBulkConcrete.Endpoints` | Final endpoint wrappers and explicit cutoff/existence corollaries. |

The imports are sequential: each module imports the previous one. This preserves
the original declaration order and avoids introducing new proof obligations.

## Audit nucleus

The smallest staged module containing the canonical terminal certificate route
is:

```lean
import LeanC2.Analytic.GenuineBulkConcrete.Terminal
```

It contains:

```lean
C2.RiemannHypothesisTerminalData
C2.offCriticalStripNonvanishing_of_terminalData
C2.mathlibRiemannHypothesis_of_terminalData
```

External reviewers can still use the facade module if they want the complete
route:

```lean
import LeanC2.Analytic.GenuineBulkConcrete
```

## Verification

The CI command remains unchanged:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

