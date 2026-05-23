# Review-Facing Theorem Map

This document gives the public theorem map for the peer-review version of the C2 route.

It intentionally separates four layers:

1. Mathematical architecture.
2. Review-facing theorem names.
3. Public Lean facade names in `LeanC2/PeerReview.lean`.
4. Existing internal Lean declaration names.

The paper and review guide should use the public facade where possible.

## 0. Public facade module

```lean
import LeanC2.PeerReview
```

Namespace:

```lean
namespace C2.PeerReview
```

`LeanC2/PeerReview.lean` is the paper-facing entry point. It imports the concrete route and provides stable public aliases/wrappers without renaming the internal development.

## 1. Canonical endpoint

### Public facade name

`C2.PeerReview.RiemannHypothesis_of_offCriticalNonvanishing`

### Internal Lean declaration

`C2.mathlibRiemannHypothesis_of_offCriticalStripNonvanishing`

### Role

Converts nonvanishing of `riemannZeta` on the off-critical open strip into the official `RiemannHypothesis` proposition from mathlib.

```text
offCriticalStripNonvanishing riemannZeta
  -> RiemannHypothesis
```

## 2. Abstract transfer layer

### Public facade names

- `C2.PeerReview.C2FundamentalIdentityOnRightHalfPlane`
- `C2.PeerReview.C2FundamentalIdentityOnOffCriticalStrip`
- `C2.PeerReview.ZetaNonvanishing_of_C2Nonvanishing`
- `C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing`
- `C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing_offCriticalIdentity`

### Internal Lean declarations

- `FundamentalIdentityOnRightHalfPlane`
- `FundamentalIdentityOnOffCriticalStrip`
- `FundamentalIdentityOnRightHalfPlane.toOffCriticalStrip`
- `F_nonzero_iff_zeta_nonzero_of_identity`
- `zeta_nonzero_of_F_nonzero`
- `offCriticalStrip_zeta_nonvanishing_of_F_nonvanishing`
- `mathlibRiemannHypothesis_of_F_nonvanishing`
- `mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity`

### Role

Transfers off-critical nonvanishing from a C2 numerator/operator `F` to `riemannZeta`, using the identity

```text
F(s) = c0(s) * riemannZeta(s)
```

on the required domain.

## 3. Regional cover layer

### Public facade names

- `C2.PeerReview.NearCriticalZeroCertificate`
- `C2.PeerReview.MiddleRegionDominanceCertificate`
- `C2.PeerReview.MiddleRegionBoundsCertificate`
- `C2.PeerReview.EdgeRegionCertificate`
- `C2.PeerReview.OffCriticalRegionalCover`
- `C2.PeerReview.OffCriticalNonvanishing_of_regionalCover`
- `C2.PeerReview.RiemannHypothesis_of_regionalCover`

### Internal Lean declarations

- `NearAxisRouteData`
- `RegionalVerticalBulkRouteData`
- `RegionalVerticalBulkBoundsData`
- `EdgeRouteData`
- `OffCriticalCoverData`
- `offCriticalStripNonvanishing_of_coverData`
- `mathlibRiemannHypothesis_of_coverData_offCriticalIdentity`

### Role

Assembles local nonvanishing certificates over a cover of the off-critical strip.

```text
near-critical-zero regime
  ∪ middle-region regime
  ∪ edge-region regime
  covers offCriticalStrip
```

## 4. Continuation layer

### Public facade names

- `C2.PeerReview.GenuineC2ContinuationData`
- `C2.PeerReview.GenuineC2Operator`

### Internal Lean declarations

- `GenuineFInfiniteContinuationData`
- `GenuineFInfiniteContinuationData.fundamentalIdentity`
- `GenuineFInfiniteContinuationData.analyticOnNhd_punctured`
- `GenuineFInfiniteContinuationData.eq_continuedCentralOddChannel_on_punctured`
- `mathlibRiemannHypothesis_of_genuineFInfiniteContinuation`
- `mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_cover`

### Role

Packages the analytic continuation and identity bridge for the complete/genuine C2 operator.

## 5. Near-critical-zero layer

### Public names

- `NearCriticalZeroNonvanishing`
- `NearCriticalZeroCertificate.ofContinuation`
- `NearCriticalZeroCertificate.ofLeibnizJet`

### Internal Lean declarations

- `eventually_ne_zero_of_continuation`
- `GenuineFInfiniteNearAxisData.of_continuation`
- `NearAxisCertificate.of_eventually_ne_zero`
- `NearAxisCertificate.of_leibnizJet_c0`
- `leibnizJet_ne_zero_of_c0_of_re_pos`
- `eventually_ne_zero_of_leibnizJet_c0_of_re_pos`

### Role

Provides local punctured nonvanishing near zeros on the critical line.

## 6. Middle-region non-cancellation layer

### Public facade names

- `C2.PeerReview.MiddleRegionDominanceCertificate`
- `C2.PeerReview.MiddleRegionBoundsCertificate`
- `C2.PeerReview.CalibratedContinuedBulkModel`
- `C2.PeerReview.DominantFourLevelBlockInequality`
- `C2.PeerReview.ResidualBudgetDominance`
- `C2.PeerReview.CalibratedResidualSeed`
- `C2.PeerReview.ResolventNonCancellationCriterion_of_budgetBounds`
- `C2.PeerReview.AdjustedResolventNonCancellationCriterion_of_residualBudgetBounds`
- `C2.PeerReview.FiniteResolventNonCancellationCriterion_of_splitBounds`
- `C2.PeerReview.AdjustedResolventNonCancellationCriterion_of_adjustedBlockBounds`

### Public exposition names

- `ResolventNonCancellationCriterion`
- `DominantFourLevelBlockInequality`
- `ResidualBudgetDominance`
- `CalibratedResidualSeed`

### Deprecated discovery labels

The public tree should expose this layer as resolvent non-cancellation, dominant four-level blocks, and calibrated residual budgets. Historical mnemonic labels are not part of the review-facing API.

### Representative internal endpoint declarations

- `mathlibRiemannHypothesis_of_expandedScalarMiddleRegion`
- `mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegionWithBounds`
- `mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteCover`
- `c2ResolventNonCancellationFiniteCriterion_of_budgetBounds`
- `c2ResolventNonCancellationAdjustedCriterion_of_residualBudgetBounds`
- `c2ResolventNonCancellationFiniteCriterion_of_splitBounds`
- `c2ResolventNonCancellationAdjustedCriterion_of_adjustedQuartetBounds`
- `mathlibRiemannHypothesis_of_continuationAndExplicitScalarExactZetaMiddleRegion`
- `mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds`
- `mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualPointwiseBounds`
- `mathlibRiemannHypothesis_of_canonicalClosedScaledResidualBudgetMiddleRegionData`

### Role

This layer proves nonvanishing in the middle region through an explicit dominance inequality: a main resolvent/four-level block dominates the residual budgets.

## 7. Terminal package

### Public facade names

- `C2.PeerReview.RiemannHypothesisTerminalCertificate`
- `C2.PeerReview.RiemannHypothesis_of_terminalCertificate`

### Internal Lean declarations

- `RiemannHypothesisTerminalData`
- `offCriticalStripNonvanishing_of_terminalData`
- `mathlibRiemannHypothesis_of_terminalData`
- `RiemannHypothesisTerminalData.ofExplicitScalarExactZetaMiddleRegion`
- `RiemannHypothesisTerminalData.ofContinuationAndExplicitScalarExactZetaMiddleRegion`
- `mathlibRiemannHypothesis_of_genuineFInfiniteNearAxisAndExplicitScalarExactZetaMiddleRegion`
- `mathlibRiemannHypothesis_of_continuationAndExplicitScalarExactZetaMiddleRegion`

### Role

Final packaged route: continuation + near-critical-zero data + middle-region data + edge handling imply the official mathlib `RiemannHypothesis`.

## 8. Recommended paper theorem order

1. Definition of the C2 operator and the off-critical strip.
2. Fundamental C2/zeta identity.
3. Regional cover theorem.
4. Near-critical-zero nonvanishing theorem.
5. Middle-region resolvent non-cancellation theorem.
6. Edge-region theorem.
7. Off-critical C2 nonvanishing theorem.
8. Transfer theorem to `riemannZeta`.
9. Formal endpoint theorem: `RiemannHypothesis`.

## 9. Reviewer warning label

The review-facing theorem map should not claim that every internal helper lemma is conceptually independent.

Some declarations are packaging, wrappers, aliases, or route specializations. The paper should distinguish conceptual theorems, interfaces, transport lemmas, wrapper corollaries, and concrete bound obligations.
