# Bounds, Certificates, and Witness Inventory

This file records the review-facing inventory for the bound packages,
certificates, residual budgets, and oscillatory witnesses exposed through:

```lean
import LeanC2.PeerReview
```

All names below live in:

```lean
namespace C2.PeerReview
```

The facade names are aliases or thin wrappers over the existing Lean
formalization. They do not introduce new proof obligations; they make the
objects easier to cite in the paper and easier to inspect during external
review.

## Source status

The public `LeanC2/` tree has been compared against `local/LeanC2/` after
normalizing the historical rename from the informal non-cancellation label to
the review-facing resolvent non-cancellation terminology.

No Lean source family for bounds, certificates, or witnesses remains local-only.
The main public entry point for this inventory is `LeanC2/PeerReview.lean`.
The concrete bulk implementation is split into staged modules documented in
`docs/LEAN_MODULE_LAYOUT.md`.

## Near-critical-zero certificates

| Public facade name | Internal declaration |
| --- | --- |
| `GenuineNearCriticalZeroData` | `GenuineFInfiniteNearAxisData` |
| `GenuineTaylorBoundsFamilyData` | `GenuineFInfiniteTaylorBoundsFamilyData` |
| `GenuineLeibnizTaylorBoundsFamilyData` | `GenuineFInfiniteLeibnizTaylorBoundsFamilyData` |
| `GenuineRectangularCentralBoundsData` | `GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData` |

Role: certificates for local punctured nonvanishing near the critical axis,
including Taylor/Leibniz families used by the genuine operator route.

## Continued bulk and regional certificates

| Public facade name | Internal declaration |
| --- | --- |
| `ContinuedBulkNearCriticalZeroData` | `C2OddTailContinuedBalancingSeedBulkModelNearAxisData` |
| `ContinuedBulkMiddleRegionRouteData` | `C2OddTailContinuedBalancingSeedBulkModelBulkRouteData` |
| `ContinuedBulkMiddleRegionBoundsData` | `C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData` |
| `ContinuedBulkMiddleRegionData` | `C2OddTailContinuedBalancingSeedBulkModelBulkRegionData` |
| `ContinuedBulkDominantBlockRouteData` | `C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData` |
| `ContinuedBulkDominantBlockBoundsData` | `C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData` |
| `ContinuedBulkEdgeRegionData` | `C2OddTailContinuedBalancingSeedBulkModelEdgeData` |
| `ContinuedBulkNearMiddleEdgeData` | `C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData` |
| `ContinuedBulkNearMiddleBoundsEdgeData` | `C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData` |
| `ContinuedBulkRegionalRouteData` | `C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData` |
| `ContinuedBulkRegionalBoundsData` | `C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData` |

Role: packages the near-axis, middle-region, dominant-block, and edge-region
pieces used to assemble the off-critical regional cover.

## Expanded scalar and canonical certificates

| Public facade name | Internal declaration |
| --- | --- |
| `ExpandedScalarCoverCertificate` | `C2ExpandedScalarCoverData` |
| `ExpandedScalarScaleBounds` | `C2ExpandedScalarScaleData` |
| `ExpandedScalarHorizontalBudget` | `C2ExpandedHorizontalLayerBudget` |
| `ExpandedScalarOddTruncationBudget` | `C2ExpandedOddTruncationBudget` |
| `ExpandedScalarMainInequalities` | `C2ExpandedScalarMainInequalities` |
| `ExpandedScalarLocalBulkCertificate` | `C2ExpandedScalarLocalBulkData` |
| `ExpandedScalarChoiceRegions` | `C2ExpandedScalarChoiceRegions` |
| `ExpandedScalarCanonicalCoverCertificate` | `C2ExpandedScalarCanonicalCoverData` |
| `ExpandedScalarMiddleRegionCertificate` | `C2ExpandedScalarMiddleRegionData` |
| `ExplicitScalarExactZetaMiddleRegionCertificate` | `C2ExplicitScalarExactZetaMiddleRegionData` |
| `ExpandedExactZetaMiddleRegionCertificate` | `C2ExpandedExactZetaMiddleRegionData` |

Role: scalarized middle-region data, cover data, and exact-zeta variants that
feed the terminal route.

## Component, resolvent-note, and residual-budget certificates

| Public facade name | Internal declaration |
| --- | --- |
| `ComponentTruncationLocalCertificate` | `C2QuartetComponentTruncationLocalData` |
| `ComponentTruncationMiddleRegionCertificate` | `C2QuartetComponentTruncationMiddleRegionData` |
| `ResolventNoteLocalCertificate` | `C2QuartetComponentResolventNoteLocalData` |
| `ResolventNoteMiddleRegionCertificate` | `C2QuartetComponentResolventNoteMiddleRegionData` |
| `CanonicalClosedScaledMiddleCoverCertificate` | `C2CanonicalClosedScaledMiddleCoverData` |
| `CanonicalClosedScaledCoverCertificate` | `C2CanonicalClosedScaledCoverData` |
| `CanonicalClosedScaledMiddleRegionCertificate` | `C2CanonicalClosedScaledMiddleRegionData` |
| `CanonicalClosedScaledLocalCertificate` | `C2CanonicalClosedScaledLocalData` |
| `CanonicalClosedScaledVerticalBudgetLocalData` | `C2CanonicalClosedScaledVerticalBudgetLocalData` |
| `CanonicalClosedScaledVerticalBudgetMiddleRegionData` | `C2CanonicalClosedScaledVerticalBudgetMiddleRegionData` |
| `CanonicalClosedScaledVerticalTruncationLocalData` | `C2CanonicalClosedScaledVerticalTruncationLocalData` |
| `CanonicalClosedScaledVerticalTruncationMiddleRegionData` | `C2CanonicalClosedScaledVerticalTruncationMiddleRegionData` |
| `CanonicalClosedScaledResidualBudgetLocalData` | `C2CanonicalClosedScaledResidualBudgetLocalData` |
| `CanonicalClosedScaledResidualBudgetMiddleRegionData` | `C2CanonicalClosedScaledResidualBudgetMiddleRegionData` |
| `CanonicalClosedScaledMiddleLocalData` | `C2CanonicalClosedScaledMiddleLocalData` |

Role: decomposes the dominant block, truncation error, vertical budgets, and
residual budgets used by the resolvent non-cancellation criterion.

## Genuine-central resolvent non-cancellation certificates

| Public facade name | Internal declaration |
| --- | --- |
| `ResolventNonCancellationGenuineCentralLocalCertificate` | `C2ResolventNonCancellationGenuineCentralLocalData` |
| `ResolventNonCancellationGenuineCentralMiddleRegionCertificate` | `C2ResolventNonCancellationGenuineCentralMiddleRegionData` |
| `ResolventNonCancellationExactGenuineCentralLocalCertificate` | `C2ResolventNonCancellationExactGenuineCentralLocalData` |
| `ResolventNonCancellationExactGenuineCentralMiddleRegionCertificate` | `C2ResolventNonCancellationExactGenuineCentralMiddleRegionData` |

Role: review-facing names for the genuine-central middle-region
non-cancellation packages.

## Bound estimate packages

| Public facade name | Internal declaration |
| --- | --- |
| `ContinuedBulkConcreteEstimates` | `C2OddTailContinuedBalancingSeedBulkConcreteEstimates` |
| `ContinuedBulkDominantBlockConcreteEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetConcreteEstimates` |
| `ContinuedBulkComponentEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates` |
| `ContinuedBulkExactEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetExactEstimates` |
| `ContinuedBulkTriangleEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetTriangleEstimates` |
| `ContinuedBulkClosedEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetClosedEstimates` |
| `ContinuedBulkCanonicalClosedEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedEstimates` |
| `ContinuedBulkZetaDepthCoreEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreEstimates` |
| `BalancingSeedConcreteEstimates` | `C2OddTailBalancingSeedConcreteEstimates` |
| `BalancingSeedRefinedConcreteEstimates` | `C2OddTailBalancingSeedRefinedConcreteEstimates` |
| `BalancingSeedExplicitAnchorEstimates` | `C2OddTailBalancingSeedExplicitAnchorEstimates` |
| `ContinuedBulkExplicitFiniteCoreEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreEstimates` |
| `ContinuedBulkExplicitScalarEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarEstimates` |
| `ContinuedBulkExplicitScalarExactZetaEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaEstimates` |
| `ContinuedBulkExpandedExactZetaEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaEstimates` |
| `ExpandedExactZetaDominanceEstimates` | `C2ExpandedExactZetaDominanceEstimates` |
| `ContinuedBulkCanonicalClosedScaledEstimates` | `C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates` |
| `ExpandedExactZetaScalarEstimates` | `C2ExpandedExactZetaScalarEstimates` |
| `BalancingSeedExplicitCutoffEstimates` | `C2OddTailBalancingSeedExplicitCutoffEstimates` |
| `BalancingSeedExplicitCutoffOneLtEstimates` | `C2OddTailBalancingSeedExplicitCutoffOneLtEstimates` |

Role: explicit estimate bundles for the concrete, exact, triangle, closed,
canonical, expanded, exact-zeta, and cutoff-bound stages.

## Oscillatory witnesses

| Public facade name | Internal declaration |
| --- | --- |
| `PointwiseOscillatoryWitnessMain` | `c2ConcreteResolventNonCancellationPointwiseOscillatoryMain` |
| `PointwiseOscillatoryResidualUpper` | `c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper` |
| `AdjustedPointwiseOscillatoryMargin` | `c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin` |
| `AdjustedExponentialPointwiseOscillatoryMargin` | `c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin` |
| `ExponentialPointwiseOscillatoryWitnessMain` | `c2ExponentialPointwiseOscillatoryMain` |
| `ExponentialPointwiseOscillatoryRemainderTerm` | `c2ExponentialPointwiseOscillatoryRemainderTerm` |
| `ExponentialPointwiseOscillatoryRemainderUpper` | `c2ExponentialPointwiseOscillatoryRemainderUpper` |
| `ExponentialPointwiseOscillatoryResidualUpper` | `c2ExponentialCutoffErrorPointwiseOscillatoryUpper` |
| `RectangularExponentialPointwiseOscillatoryMain` | `rectangularExponentialPointwiseOscillatoryMain` |
| `RectangularExponentialPointwiseOscillatoryExactUpper` | `rectangularExponentialPointwiseOscillatoryExactUpper` |
| `RectangularExponentialPointwiseOscillatoryExpUpper` | `rectangularExponentialPointwiseOscillatoryExpUpper` |
| `RectangularExponentialPointwiseOscillatoryUpper` | `rectangularExponentialPointwiseOscillatoryUpper` |

The public facade also exposes the decomposition lemmas:

| Public facade name | Internal declaration |
| --- | --- |
| `PointwiseOscillatoryResidualUpper_eq_main_add_remainderUpper` | definitional equality wrapper |
| `ExponentialPointwiseOscillatoryResidualUpper_eq_main_add_remainderUpper` | `c2ExponentialCutoffErrorPointwiseOscillatoryUpper_eq_main_add_remainderUpper` |

Role: keeps the complex oscillatory main term as a witness and separates the
coarse remainder upper, matching the resolvent non-cancellation budget
inequality.

## Terminal package

| Public facade name | Internal declaration |
| --- | --- |
| `RiemannHypothesisTerminalCertificate` | `RiemannHypothesisTerminalData` |
| `RiemannHypothesis_of_terminalCertificate` | `mathlibRiemannHypothesis_of_terminalData` |

Role: final certificate route to mathlib's `RiemannHypothesis`.

## Verification command

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```
