# Formal Naming Conventions for Peer Review

This document fixes the public naming layer for the review-facing version of the C2 formalization.

The internal development may keep mnemonic names used during discovery. The paper, theorem map, CI reports, and review documentation should use the formal names below.

## Principle

Use mathematical names that describe the role of the result in the proof architecture.

Avoid informal labels in review-facing statements, section titles, theorem names, abstracts, and captions.

## Public proof architecture

| Internal / mnemonic role | Review-facing name | Recommended phrase |
| --- | --- | --- |
| former middle-region discovery mnemonic | non-cancellation mechanism | resolvent non-cancellation mechanism |
| former seed mnemonic / balancing seed | calibrated residual seed | calibrated residual seed |
| genuine | genuine C2 operator | complete C2 operator / genuine C2 operator |
| near-axis | local zero-neighborhood regime | near-critical-zero regime |
| bulk | middle-region regime | middle-region nonvanishing regime |
| edge | exterior regime | edge-region nonvanishing regime |
| cover | regional cover | off-critical regional cover |
| transferência | transfer theorem | transfer to the mathlib Riemann Hypothesis statement |
| colagem | gluing / assembly | regional assembly |
| barreira de ramo | branch-norm barrier | branch norm barrier |
| tilt | critical-line tilt obstruction | tilt obstruction |
| former four-block mnemonic | four-level dominant block | dominant four-level block |
| cauda | tail estimate | residual/tail estimate |

## Suggested public theorem names

| Current role | Suggested public theorem/definition name |
| --- | --- |
| off-critical nonvanishing implies RH | `RiemannHypothesis_of_offCriticalNonvanishing` |
| fundamental identity on right half-plane | `C2FundamentalIdentityOnRightHalfPlane` |
| fundamental identity on off-critical strip | `C2FundamentalIdentityOnOffCriticalStrip` |
| transfer from C2 operator nonvanishing to zeta nonvanishing | `ZetaNonvanishing_of_C2Nonvanishing` |
| transfer from C2 operator nonvanishing to RH | `RiemannHypothesis_of_C2Nonvanishing` |
| cover implies off-critical nonvanishing | `OffCriticalNonvanishing_of_regionalCover` |
| near-axis certificate | `NearCriticalZeroCertificate` |
| bulk dominance certificate | `MiddleRegionDominanceCertificate` |
| edge certificate | `EdgeRegionCertificate` |
| terminal package | `RiemannHypothesisTerminalCertificate` |
| continuation data for the genuine operator | `GenuineC2ContinuationData` |
| calibrated continued bulk model | `CalibratedContinuedBulkModel` |
| quartet dominance condition | `DominantFourLevelBlockInequality` |
| residual budget condition | `ResidualBudgetDominance` |

## Review-facing module strategy

Prefer a small public facade module instead of rewriting the whole repository at once.

Suggested module:

```lean
import LeanC2.Analytic.GenuineBulkConcrete

namespace C2.PeerReview

-- Public aliases/wrappers go here.

end C2.PeerReview
```

This keeps the compiled internal route stable while giving reviewers a clean entry point.

## Paper language

Use:

> We prove an off-critical nonvanishing theorem for a C2 operator and transfer it to the official `RiemannHypothesis` statement in mathlib through a formal identity with the Riemann zeta function.

Avoid informal discovery slogans in the paper, theorem statements, section titles, abstracts, captions, public Lean declarations, and CI reports.
