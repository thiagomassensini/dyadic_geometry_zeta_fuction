# Dyadic Geometry of the Zeta Function

Official draft v1 migrated from the project notes.

## Abstract

We present a dyadic C2 operator framework for the off-critical nonvanishing problem associated with the Riemann zeta function. The construction is organized as a formal route: a C2/zeta identity, a regional cover of the off-critical strip, a near-critical-zero certificate, a middle-region dominance criterion, an edge-region certificate, and a final transfer theorem. The formal endpoint of the Lean development is the official `RiemannHypothesis` proposition in mathlib.

## 1. Introduction

The aim of this paper is to present a dyadic operator route to the Riemann zeta nonvanishing problem in the off-critical strip.

The route is:

```text
C2 local certificates
  -> off-critical regional cover
  -> off-critical nonvanishing of the C2 operator
  -> C2/zeta identity
  -> off-critical nonvanishing of riemannZeta
  -> mathlib RiemannHypothesis
```

The paper-facing names are intentionally formal. Internal discovery names are not used as theorem names in this draft. The middle-region argument is called a resolvent non-cancellation mechanism, the main finite dyadic contribution is called a dominant four-level block, and the calibrated correction is called a calibrated residual seed.

## 2. Formal endpoint

The formal endpoint is the official mathlib proposition:

```lean
RiemannHypothesis
```

The review-facing Lean facade is:

```lean
import LeanC2.PeerReview
```

The intended build command is:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

## 3. Off-critical strip

Let `s = sigma + it`. The critical line is `sigma = 1/2`. The off-critical strip is the part of the critical strip satisfying:

```text
0 < Re(s) < 1
Re(s) != 1/2
```

For a complex-valued function `F`, off-critical nonvanishing means:

```text
for every s in the off-critical strip, F(s) != 0.
```

In the public facade this is exposed as:

```lean
C2.PeerReview.OffCriticalNonvanishing
```

## 4. C2/zeta identity and transfer

The C2 route uses an operator `F` and a scalar factor `c0(s)` satisfying a C2/zeta identity of the form:

```text
F(s) = c0(s) * zeta(s)
```

The formal route has two identity interfaces:

```lean
C2.PeerReview.C2FundamentalIdentityOnRightHalfPlane
C2.PeerReview.C2FundamentalIdentityOnOffCriticalStrip
```

The transfer principle is:

```text
C2 operator nonvanishing
  + C2/zeta identity
  -> zeta nonvanishing
  -> RiemannHypothesis
```

The public wrappers are:

```lean
C2.PeerReview.ZetaNonvanishing_of_C2Nonvanishing
C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing
C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing_offCriticalIdentity
```

## 5. Regional cover

The off-critical strip is covered by three regimes:

1. near-critical-zero regime;
2. middle-region regime;
3. edge-region regime.

The public facade names are:

```lean
C2.PeerReview.NearCriticalZeroCertificate
C2.PeerReview.MiddleRegionDominanceCertificate
C2.PeerReview.MiddleRegionBoundsCertificate
C2.PeerReview.EdgeRegionCertificate
C2.PeerReview.OffCriticalRegionalCover
```

The cover theorem says:

```text
near certificate
+ middle certificate
+ edge certificate
+ cover proof
-> off-critical nonvanishing of the C2 operator
```

The review-facing wrappers are:

```lean
C2.PeerReview.OffCriticalNonvanishing_of_regionalCover
C2.PeerReview.RiemannHypothesis_of_regionalCover
```

## 6. Genuine C2 operator and continuation

The complete operator is called the genuine C2 operator. In the public facade:

```lean
C2.PeerReview.GenuineC2Operator
C2.PeerReview.GenuineC2ContinuationData
```

The continuation layer packages the comparison between the complete C2 operator and the continued central odd channel. Conceptually, it transports the identity from the absolute-convergence region to the domain needed by the off-critical route.

## 7. Near-critical-zero regime

The near-critical-zero regime is handled by local punctured nonvanishing. In the formal route, this is packaged as a near-critical-zero certificate.

The certificate is supplied either by continuation data or by a Taylor/Leibniz witness, depending on the selected route.

## 8. Middle-region non-cancellation

The middle-region proof is expressed as a dominance argument. A main dyadic block is extracted from the operator, and the remaining terms are organized into explicit residual budgets.

Review-facing names:

```text
ResolventNonCancellationCriterion
DominantFourLevelBlockInequality
ResidualBudgetDominance
CalibratedResidualSeed
```

The criterion has the form:

```text
main dyadic block > residual budget
-> C2 operator nonvanishing in the middle region
```

This avoids using internal discovery names in the paper.

## 9. Edge-region regime

The edge-region certificate covers any remaining part of the off-critical strip not covered by the near-critical-zero and middle-region regimes.

In the selected continued model, the edge may be represented by an empty edge package if the other regions cover the needed domain. In the formal route this is still represented as certificate data.

## 10. Terminal certificate

The terminal package assembles the continuation, near-critical-zero, middle-region, edge, and cover data into a single route.

Public facade names:

```lean
C2.PeerReview.RiemannHypothesisTerminalCertificate
C2.PeerReview.RiemannHypothesis_of_terminalCertificate
```

The terminal theorem is:

```text
terminal C2 certificate
-> mathlib RiemannHypothesis
```

## 11. Reproducibility

The reproducibility guide is maintained in:

```text
docs/REPRODUCIBILITY.md
```

The theorem map is maintained in:

```text
docs/THEOREM_MAP_REVIEW.md
```

A reviewer should be able to identify:

1. the final Lean theorem;
2. the exact build command;
3. where the C2/zeta identity enters;
4. which regional certificates are used;
5. which theorem concludes mathlib `RiemannHypothesis`.

## 12. Discussion

The construction separates the C2-native nonvanishing problem from the final transfer to the classical zeta statement. This separation is important for auditability: the regional cover and middle-region non-cancellation mechanism are C2-side statements, while the final step is a transfer through the C2/zeta identity.

The endpoint is not a local replacement for RH. The endpoint is the official mathlib `RiemannHypothesis` proposition.
