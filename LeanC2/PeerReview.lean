import Mathlib.Analysis.Complex.SummableUniformlyOn
import LeanC2.Analytic.GenuineBulkConcrete
import LeanC2.Route.AntiMiracleClosure

/-!
# Peer-review facade for the C2 route

This module provides review-facing names for the formal route to mathlib's
`RiemannHypothesis` statement.

It is intentionally thin: it does not replace the internal development names.
It only gives the paper and theorem map a stable public namespace.
-/

namespace C2
namespace PeerReview

abbrev C2FundamentalIdentityOnRightHalfPlane :=
  C2.FundamentalIdentityOnRightHalfPlane

abbrev C2FundamentalIdentityOnOffCriticalStrip :=
  C2.FundamentalIdentityOnOffCriticalStrip

abbrev OffCriticalNonvanishing := C2.offCriticalStripNonvanishing

abbrev NearCriticalZeroCertificate := C2.NearAxisCertificate

abbrev MiddleRegionDominanceCertificate := C2.RegionalVerticalBulkRouteData

abbrev MiddleRegionBoundsCertificate := C2.RegionalVerticalBulkBoundsData

abbrev EdgeRegionCertificate := C2.EdgeRouteData

abbrev OffCriticalRegionalCover := C2.OffCriticalCoverData

abbrev GenuineC2ContinuationData := C2.GenuineFInfiniteContinuationData

noncomputable abbrev GenuineC2Operator : ℂ → ℂ := C2.genuineFInfinite

abbrev RiemannHypothesisTerminalCertificate := C2.RiemannHypothesisTerminalData

noncomputable abbrev CalibratedContinuedBulkModel
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  C2.c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

abbrev DominantFourLevelBlockInequality :=
  C2.C2ExpandedQuartetDominance

abbrev ResidualBudgetDominance :=
  C2.C2CanonicalClosedScaledResidualBudgetLocalData

abbrev CalibratedResidualSeed :=
  C2.C2BalancingSeedFactorScaledBound

/-! ## Audit-facing certificate packages -/

abbrev GenuineNearCriticalZeroData := C2.GenuineFInfiniteNearAxisData

abbrev GenuineTaylorBoundsFamilyData :=
  C2.GenuineFInfiniteTaylorBoundsFamilyData

abbrev GenuineLeibnizTaylorBoundsFamilyData :=
  C2.GenuineFInfiniteLeibnizTaylorBoundsFamilyData

abbrev GenuineRectangularCentralBoundsData :=
  C2.GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData

abbrev ContinuedBulkNearCriticalZeroData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData

abbrev ContinuedBulkMiddleRegionRouteData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelBulkRouteData

abbrev ContinuedBulkMiddleRegionBoundsData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData

abbrev ContinuedBulkMiddleRegionData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelBulkRegionData

abbrev ContinuedBulkDominantBlockRouteData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData

abbrev ContinuedBulkDominantBlockBoundsData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData

abbrev ContinuedBulkEdgeRegionData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelEdgeData

abbrev ContinuedBulkNearMiddleEdgeData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData

abbrev ContinuedBulkNearMiddleBoundsEdgeData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData

abbrev ContinuedBulkRegionalRouteData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData

abbrev ContinuedBulkRegionalBoundsData :=
  C2.C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData

abbrev ExpandedScalarCoverCertificate := C2.C2ExpandedScalarCoverData

abbrev ExpandedScalarScaleBounds := C2.C2ExpandedScalarScaleData

abbrev ExpandedScalarHorizontalBudget := C2.C2ExpandedHorizontalLayerBudget

abbrev ExpandedScalarOddTruncationBudget := C2.C2ExpandedOddTruncationBudget

abbrev ExpandedScalarMainInequalities := C2.C2ExpandedScalarMainInequalities

abbrev ExpandedScalarLocalBulkCertificate := C2.C2ExpandedScalarLocalBulkData

abbrev ExpandedScalarChoiceRegions := C2.C2ExpandedScalarChoiceRegions

abbrev ExpandedScalarCanonicalCoverCertificate :=
  C2.C2ExpandedScalarCanonicalCoverData

abbrev ExpandedScalarMiddleRegionCertificate :=
  C2.C2ExpandedScalarMiddleRegionData

abbrev ComponentTruncationLocalCertificate :=
  C2.C2QuartetComponentTruncationLocalData

abbrev ComponentTruncationMiddleRegionCertificate :=
  C2.C2QuartetComponentTruncationMiddleRegionData

abbrev ResolventNoteLocalCertificate :=
  C2.C2QuartetComponentResolventNoteLocalData

abbrev ResolventNoteMiddleRegionCertificate :=
  C2.C2QuartetComponentResolventNoteMiddleRegionData

abbrev CanonicalClosedScaledMiddleCoverCertificate :=
  C2.C2CanonicalClosedScaledMiddleCoverData

abbrev CanonicalClosedScaledCoverCertificate :=
  C2.C2CanonicalClosedScaledCoverData

abbrev CanonicalClosedScaledMiddleRegionCertificate :=
  C2.C2CanonicalClosedScaledMiddleRegionData

abbrev CanonicalClosedScaledLocalCertificate :=
  C2.C2CanonicalClosedScaledLocalData

abbrev CanonicalClosedScaledVerticalBudgetLocalData :=
  C2.C2CanonicalClosedScaledVerticalBudgetLocalData

abbrev CanonicalClosedScaledVerticalBudgetMiddleRegionData :=
  C2.C2CanonicalClosedScaledVerticalBudgetMiddleRegionData

abbrev CanonicalClosedScaledVerticalTruncationLocalData :=
  C2.C2CanonicalClosedScaledVerticalTruncationLocalData

abbrev CanonicalClosedScaledVerticalTruncationMiddleRegionData :=
  C2.C2CanonicalClosedScaledVerticalTruncationMiddleRegionData

abbrev CanonicalClosedScaledResidualBudgetLocalData :=
  C2.C2CanonicalClosedScaledResidualBudgetLocalData

abbrev CanonicalClosedScaledResidualBudgetMiddleRegionData :=
  C2.C2CanonicalClosedScaledResidualBudgetMiddleRegionData

abbrev CanonicalClosedScaledMiddleLocalData :=
  C2.C2CanonicalClosedScaledMiddleLocalData

abbrev ContinuedModelTerminalMiddleRegion :=
  C2.c2ContinuedModelTerminalMiddleRegion

abbrev ExplicitScalarExactZetaMiddleRegionCertificate :=
  C2.C2ExplicitScalarExactZetaMiddleRegionData

abbrev ExpandedExactZetaMiddleRegionCertificate :=
  C2.C2ExpandedExactZetaMiddleRegionData

abbrev ResolventNonCancellationGenuineCentralLocalCertificate :=
  C2.C2ResolventNonCancellationGenuineCentralLocalData

abbrev ResolventNonCancellationGenuineCentralMiddleRegionCertificate :=
  C2.C2ResolventNonCancellationGenuineCentralMiddleRegionData

abbrev ResolventNonCancellationExactGenuineCentralLocalCertificate :=
  C2.C2ResolventNonCancellationExactGenuineCentralLocalData

abbrev ResolventNonCancellationExactGenuineCentralMiddleRegionCertificate :=
  C2.C2ResolventNonCancellationExactGenuineCentralMiddleRegionData

/-! ## Audit-facing bound packages -/

abbrev ContinuedBulkConcreteEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkConcreteEstimates

abbrev ContinuedBulkDominantBlockConcreteEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetConcreteEstimates

abbrev ContinuedBulkComponentEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates

abbrev ContinuedBulkExactEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetExactEstimates

abbrev ContinuedBulkTriangleEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetTriangleEstimates

abbrev ContinuedBulkClosedEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetClosedEstimates

abbrev ContinuedBulkCanonicalClosedEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedEstimates

abbrev ContinuedBulkZetaDepthCoreEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreEstimates

abbrev BalancingSeedConcreteEstimates :=
  C2.C2OddTailBalancingSeedConcreteEstimates

abbrev BalancingSeedRefinedConcreteEstimates :=
  C2.C2OddTailBalancingSeedRefinedConcreteEstimates

abbrev BalancingSeedExplicitAnchorEstimates :=
  C2.C2OddTailBalancingSeedExplicitAnchorEstimates

abbrev ContinuedBulkExplicitFiniteCoreEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreEstimates

abbrev ContinuedBulkExplicitScalarEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarEstimates

abbrev ContinuedBulkExplicitScalarExactZetaEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaEstimates

abbrev ContinuedBulkExpandedExactZetaEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaEstimates

abbrev ExpandedExactZetaDominanceEstimates :=
  C2.C2ExpandedExactZetaDominanceEstimates

abbrev ContinuedBulkCanonicalClosedScaledEstimates :=
  C2.C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates

abbrev ExpandedExactZetaScalarEstimates :=
  C2.C2ExpandedExactZetaScalarEstimates

abbrev BalancingSeedExplicitCutoffEstimates :=
  C2.C2OddTailBalancingSeedExplicitCutoffEstimates

abbrev BalancingSeedExplicitCutoffOneLtEstimates :=
  C2.C2OddTailBalancingSeedExplicitCutoffOneLtEstimates

/-! ## Audit-facing oscillatory witnesses -/

noncomputable abbrev PointwiseOscillatoryWitnessMain
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ) (cutoffScale : ℂ → ℝ) :
    ℂ → ℂ :=
  C2.c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
    oscillatoryMoment J cutoffScale

noncomputable abbrev PointwiseOscillatoryResidualUpper
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ)
    (cutoffScale remainderUpper : ℂ → ℝ) : ℂ → ℝ :=
  C2.c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
    oscillatoryMoment J cutoffScale remainderUpper

noncomputable abbrev AdjustedPointwiseOscillatoryMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ)
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ) : ℂ → ℝ :=
  C2.c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
    tiltSeed coreCutoff
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale remainderUpper
    oscillatoryMoment J

noncomputable abbrev AdjustedExponentialPointwiseOscillatoryMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  C2.c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
    tiltSeed coreCutoff
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
    K M J X

noncomputable abbrev ExponentialPointwiseOscillatoryWitnessMain
    (K M J : ℕ) (X : ℝ) : ℂ → ℂ :=
  C2.c2ExponentialPointwiseOscillatoryMain K M J X

noncomputable abbrev ExponentialPointwiseOscillatoryRemainderTerm
    (K M J : ℕ) (X : ℝ) : ℂ → ℂ :=
  C2.c2ExponentialPointwiseOscillatoryRemainderTerm K M J X

noncomputable abbrev ExponentialPointwiseOscillatoryRemainderUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  C2.c2ExponentialPointwiseOscillatoryRemainderUpper K M J X

noncomputable abbrev ExponentialPointwiseOscillatoryResidualUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  C2.c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X

noncomputable abbrev RectangularExponentialPointwiseOscillatoryMain
    (s : ℂ) (K M J : ℕ) (X : ℝ) : ℂ :=
  C2.rectangularExponentialPointwiseOscillatoryMain s K M J X

noncomputable abbrev RectangularExponentialPointwiseOscillatoryExactUpper
    (s : ℂ) (K M J : ℕ) (X : ℝ) : ℝ :=
  C2.rectangularExponentialPointwiseOscillatoryExactUpper s K M J X

noncomputable abbrev RectangularExponentialPointwiseOscillatoryExpUpper
    (s : ℂ) (K M J : ℕ) (X : ℝ) : ℝ :=
  C2.rectangularExponentialPointwiseOscillatoryExpUpper s K M J X

noncomputable abbrev RectangularExponentialPointwiseOscillatoryUpper
    (s : ℂ) (K M J : ℕ) (X : ℝ) : ℝ :=
  C2.rectangularExponentialPointwiseOscillatoryUpper s K M J X

theorem PointwiseOscillatoryResidualUpper_eq_main_add_remainderUpper
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ)
    (cutoffScale remainderUpper : ℂ → ℝ) (s : ℂ) :
    PointwiseOscillatoryResidualUpper
      oscillatoryMoment J cutoffScale remainderUpper s =
      ‖PointwiseOscillatoryWitnessMain oscillatoryMoment J cutoffScale s‖ +
        remainderUpper s := by
  rfl

theorem ExponentialPointwiseOscillatoryResidualUpper_eq_main_add_remainderUpper
    (K M J : ℕ) (X : ℝ) (s : ℂ) :
    ExponentialPointwiseOscillatoryResidualUpper K M J X s =
      ‖ExponentialPointwiseOscillatoryWitnessMain K M J X s‖ +
        ExponentialPointwiseOscillatoryRemainderUpper K M J X s := by
  exact
    C2.c2ExponentialCutoffErrorPointwiseOscillatoryUpper_eq_main_add_remainderUpper
      K M J X s

theorem ResolventNonCancellationCriterion_of_budgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {dominantBlockTailBudget tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (hblockTail : C2.c2QuartetVerticalTailUpper s ≤ dominantBlockTailBudget)
    (htilt : C2.c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : C2.c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : C2.c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : dominantBlockTailBudget + tiltBudget + horizontalBudget + cutoffBudget <
      C2.c2ExpandedQuartetK2Margin s) :
    DominantFourLevelBlockInequality
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact C2.c2ResolventNonCancellationFiniteCriterion_of_budgetBounds
    hblockTail htilt hhorizontal hcutoff hdom

theorem AdjustedResolventNonCancellationCriterion_of_residualBudgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (htilt : C2.c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : C2.c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : C2.c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : tiltBudget + horizontalBudget + cutoffBudget <
      C2.c2ExpandedQuartetResidualMargin s) :
    DominantFourLevelBlockInequality
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact C2.c2ResolventNonCancellationAdjustedCriterion_of_residualBudgetBounds
    htilt hhorizontal hcutoff hdom

theorem FiniteResolventNonCancellationCriterion_of_splitBounds
    {FInfinity FX dominantBlock residual : ℂ → ℂ}
    {dominantBlockLower residualBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hsplit : FX s = dominantBlock s + residual s)
    (hblock : dominantBlockLower s ≤ ‖dominantBlock s‖)
    (hresidual : ‖residual s‖ ≤ residualBudget s)
    (hproxy : ‖FInfinity s - FX s‖ ≤ cutoffProxy s)
    (hdom : dominantBlockLower s - residualBudget s - cutoffProxy s > 0) :
    FInfinity s ≠ 0 := by
  exact C2.c2ResolventNonCancellationFiniteCriterion_of_splitBounds
    hsplit hblock hresidual hproxy hdom

theorem AdjustedResolventNonCancellationCriterion_of_adjustedBlockBounds
    {FInfinity FX dominantBlock residual : ℂ → ℂ}
    {dominantBlockMain adjustmentDefect residualBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hsplit : FX s = dominantBlock s + residual s)
    (hblock : dominantBlockMain s - adjustmentDefect s ≤ ‖dominantBlock s‖)
    (hresidual : ‖residual s‖ ≤ residualBudget s)
    (hproxy : ‖FInfinity s - FX s‖ ≤ cutoffProxy s)
    (hdom : dominantBlockMain s - adjustmentDefect s - residualBudget s - cutoffProxy s > 0) :
    FInfinity s ≠ 0 := by
  exact C2.c2ResolventNonCancellationAdjustedCriterion_of_adjustedQuartetBounds
    hsplit hblock hresidual hproxy hdom

/-! ## Canonical terminal assembly endpoints -/

noncomputable def ContinuedBulkNearCriticalZeroData_canonical
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    ContinuedBulkNearCriticalZeroData coreCutoff K M :=
  C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofContinuedModel
    coreCutoff K M

noncomputable def TerminalCertificate_of_continuedModelMiddleLocal
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ C2.c2ExpandedScalarMiddleRegion
        (C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofContinuedModel
          coreCutoff K M)
        (C2.C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      CanonicalClosedScaledLocalCertificate
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesisTerminalCertificate :=
  C2.RiemannHypothesisTerminalData.ofContinuedModelMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    hmiddle

theorem RiemannHypothesis_of_continuedModelMiddleLocal
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ C2.c2ExpandedScalarMiddleRegion
        (C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofContinuedModel
          coreCutoff K M)
        (C2.C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      CanonicalClosedScaledLocalCertificate
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_continuedModelMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    hmiddle

theorem RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddlePointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hscale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 < horizontalScale s)
    (hconstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalConstant s)
    (hratio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalRatio s)
    (hratio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      horizontalRatio s < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2QuartetBulkGUpper
          (C2.c2BulkGUpper
            (C2.c2TiltAnalyticRegularizedUpper
              (C2.c2CanonicalClosedTiltConstant
                K M horizontalConstant horizontalScale horizontalRatio)
              (fun _ => (1 : ℝ)))
            (C2.c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio)) s +
        C2.c2BulkEUpper
          (C2.c2CutoffUpperFromScale
            (C2.c2CanonicalClosedCutoffConstant K M)
            (fun _ => (1 : ℝ))) s <
          C2.c2QuartetBulkK2Lower s *
            ((1 - ‖C2.q s‖) * (1 + ‖C2.q s‖ ^ 2))) :
    RiemannHypothesis := by
  exact
    C2.mathlibRiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddlePointwiseBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
      hdominance

noncomputable def
  TerminalCertificate_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hscale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 < horizontalScale s)
    (hconstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalConstant s)
    (hratio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalRatio s)
    (hratio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      horizontalRatio s < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        C2.c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesisTerminalCertificate :=
  C2.RiemannHypothesisTerminalData.ofContinuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    hdominance

theorem RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hscale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 < horizontalScale s)
    (hconstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalConstant s)
    (hratio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalRatio s)
    (hratio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      horizontalRatio s < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        C2.c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    C2.mathlibRiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
      hdominance

theorem RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualAnalyticBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hscale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 < horizontalScale s)
    (hconstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalConstant s)
    (hratio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      0 ≤ horizontalRatio s)
    (hratio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      horizontalRatio s < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        C2.c2AnalyticBulkAllowance s - C2.c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact
    C2.mathlibRiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualAnalyticBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
      hdominance

noncomputable def TerminalCertificate_of_continuationAndMiddleLocal
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineC2ContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ C2.c2ExpandedScalarMiddleRegion
        (C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (C2.GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2.C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      CanonicalClosedScaledLocalCertificate
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesisTerminalCertificate :=
  C2.RiemannHypothesisTerminalData.ofContinuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hmiddle

theorem RiemannHypothesis_of_continuationAndMiddleLocal
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineC2ContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ C2.c2ExpandedScalarMiddleRegion
        (C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (C2.GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2.C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      CanonicalClosedScaledLocalCertificate
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hmiddle

theorem RiemannHypothesis_of_offCriticalNonvanishing
    (hζ : OffCriticalNonvanishing riemannZeta) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_offCriticalStripNonvanishing hζ

theorem ZetaNonvanishing_of_C2Nonvanishing
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnRightHalfPlane F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    OffCriticalNonvanishing riemannZeta := by
  exact C2.offCriticalStrip_zeta_nonvanishing_of_F_nonvanishing hId hF

theorem RiemannHypothesis_of_C2Nonvanishing
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnRightHalfPlane F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_F_nonvanishing hId hF

theorem RiemannHypothesis_of_C2Nonvanishing_offCriticalIdentity
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnOffCriticalStrip F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity hId hF

theorem OffCriticalNonvanishing_of_regionalCover
    (cover : OffCriticalRegionalCover) :
    OffCriticalNonvanishing cover.F := by
  exact C2.offCriticalStripNonvanishing_of_coverData cover

theorem RiemannHypothesis_of_regionalCover
    (cover : OffCriticalRegionalCover)
    (hId : C2FundamentalIdentityOnOffCriticalStrip cover.F riemannZeta) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_coverData_offCriticalIdentity cover hId

theorem RiemannHypothesis_of_terminalCertificate
    (cert : RiemannHypothesisTerminalCertificate) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_terminalData cert

/-! ### Constant scaling witnesses for the terminal middle region

Concrete `(horizontalConstant, horizontalScale, horizontalRatio)` witnesses that
make the four positivity / range hypotheses of the residual-pointwise terminal
endpoints definitional. The two remaining hypotheses are the genuine analytic
inputs (horizontal layer budget and residual dominance). -/

abbrev ConstantHorizontalConstant := C2.c2ContinuedModelConstantHorizontalConstant
abbrev ConstantHorizontalScale := C2.c2ContinuedModelConstantHorizontalScale
abbrev ConstantHorizontalRatio := C2.c2ContinuedModelConstantHorizontalRatio

theorem RiemannHypothesis_of_continuedModelConstantScaledMiddleResidualPointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {C R : ℝ}
    (hC_nonneg : 0 ≤ C) (hR_nonneg : 0 ≤ R) (hR_lt_one : R < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff
        (ConstantHorizontalConstant C)
        ConstantHorizontalScale
        (ConstantHorizontalRatio R) s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper K M
          (ConstantHorizontalConstant C)
          ConstantHorizontalScale
          (ConstantHorizontalRatio R) s <
        C2.c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_continuedModelConstantScaledMiddleResidualPointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M) (C := C) (R := R)
    hC_nonneg hR_nonneg hR_lt_one hhorizontal hdominance

theorem RiemannHypothesis_of_continuedModelConstantScaledMiddleResidualAnalyticBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {C R : ℝ}
    (hC_nonneg : 0 ≤ C) (hR_nonneg : 0 ≤ R) (hR_lt_one : R < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      ExpandedScalarHorizontalBudget
        coreCutoff
        (ConstantHorizontalConstant C)
        ConstantHorizontalScale
        (ConstantHorizontalRatio R) s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion coreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper K M
          (ConstantHorizontalConstant C)
          ConstantHorizontalScale
          (ConstantHorizontalRatio R) s <
        C2.c2AnalyticBulkAllowance s - C2.c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_continuedModelConstantScaledMiddleResidualAnalyticBounds
    (coreCutoff := coreCutoff) (K := K) (M := M) (C := C) (R := R)
    hC_nonneg hR_nonneg hR_lt_one hhorizontal hdominance

/-! ### Concrete s-dependent witnesses with the trivial odd-core cutoff

These witnesses close the horizontal layer budget concretely (as a definitional
equality) for the trivial odd-core cutoff `coreCutoff ≡ 0` and the natural
s-dependent scaling triple

  * `OddHorizontalConstant s = 2 · ‖q s‖² · ‖oddDirichletChannel s‖`,
  * `OddHorizontalScale s    = 1`,
  * `OddHorizontalRatio s    = ‖q s‖`.

Only the residual dominance on the terminal middle region remains as a
genuinely analytic obligation in the resulting RH adapters. -/

abbrev TrivialCoreCutoff := C2.c2ContinuedModelTrivialCoreCutoff
noncomputable abbrev OddHorizontalConstant := C2.c2ContinuedModelOddHorizontalConstant
noncomputable abbrev OddHorizontalScale := C2.c2ContinuedModelOddHorizontalScale
noncomputable abbrev OddHorizontalRatio := C2.c2ContinuedModelOddHorizontalRatio

theorem RiemannHypothesis_of_continuedModelOddScaledMiddleResidualPointwiseBounds
    {K M : ℕ}
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion TrivialCoreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper K M
          OddHorizontalConstant
          OddHorizontalScale
          OddHorizontalRatio s <
        C2.c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_continuedModelOddScaledMiddleResidualPointwiseBounds
    (K := K) (M := M) hdominance

theorem RiemannHypothesis_of_continuedModelOddScaledMiddleResidualAnalyticBounds
    {K M : ℕ}
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ ContinuedModelTerminalMiddleRegion TrivialCoreCutoff K M →
      C2.c2CanonicalClosedScaledResidualUpper K M
          OddHorizontalConstant
          OddHorizontalScale
          OddHorizontalRatio s <
        C2.c2AnalyticBulkAllowance s - C2.c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_continuedModelOddScaledMiddleResidualAnalyticBounds
    (K := K) (M := M) hdominance

/-! ### Anti-miracle bulk closure (vertical phase resolvent + cobertura)

The bulk anti-miracle is a **regional** non-cancellation certificate: it
provides `F s ≠ 0` on a sub-region of the off-critical strip where the
vertical-phase resolvent dominance
`‖K₂‖ / (1 + ‖q‖) > ‖G_δ‖ + ‖E_δ‖`
holds (cf. `local/notas/teorema_anti_milagre.md`).  Per the unified closure
recipe (`local/notas/c2_fechamento_unificado.md`), the route to RH composes a
bulk anti-miracle witness with a near-axis Taylor witness and an edge
witness, all aligned to the pinned numerator `genuineFInfinite`.

The adapters below mirror exactly that shape and delegate to the existing
endpoints `mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_regionalBulk*Cover`.
-/

/-- Generic (non-pinned) bulk anti-miracle data (limit-level): `F = K_δ + E_δ`,
with the resolvent split `K_δ = K_2 / (1 - q) + G_δ` at the vertical phase
scale `q(s) = ½·2^{-s}`, and the dominance inequality
`‖K_2‖ / (1 + ‖q‖) > ‖G_δ‖ + ‖E_δ‖`. -/
abbrev BulkAntiMiracleTiltData := C2.BulkResolventNonCancellationTiltData

/-- Generic (non-pinned) bulk anti-miracle data (bounds-level): same as
`BulkAntiMiracleTiltData` but with explicit scalar bounds `K2Lower, GUpper,
EUpper` certifying the dominance inequality. -/
abbrev BulkAntiMiracleTiltBoundsData := C2.BulkResolventNonCancellationTiltBoundsData

/-- Pinned bulk anti-miracle data with `F = genuineFInfinite` (limit-level):
the dominance inequality `‖K_2‖ / (1 + ‖q‖) > ‖G_δ‖ + ‖E_δ‖` holds on the
regional `bulkRegion`, certifying non-vanishing of `genuineFInfinite` there. -/
abbrev BulkAntiMiracleData := C2.GenuineFInfiniteRegionalBulkRouteData

/-- Pinned bulk anti-miracle data with `F = genuineFInfinite` (bounds-level). -/
abbrev BulkAntiMiracleBoundsData := C2.GenuineFInfiniteRegionalBulkBoundsData

/-- Near-axis Taylor witness for `genuineFInfinite`. -/
abbrev BulkAntiMiracleNearAxisData := C2.GenuineFInfiniteNearAxisData

/-- Edge witness for `genuineFInfinite` (right-side closure of the cover). -/
abbrev BulkAntiMiracleEdgeData := C2.GenuineFInfiniteEdgeData

/-- Continuation witness extending the `Re(s) > 1` identity
`genuineFInfinite = c₀ · ζ` to the open right half-plane. -/
abbrev GenuineFInfiniteContinuation := C2.GenuineFInfiniteContinuationData

/-- The complete infinite C2 genuine numerator (analytic spelling `c₀ · ζ`). -/
noncomputable abbrev genuineFInfinite : ℂ → ℂ := C2.genuineFInfinite

/--
Concrete continuation witness for `genuineFInfinite`.

Since `genuineFInfinite` is defined as the analytic spelling `c₀ · ζ`, the
C2 identity holds definitionally on every domain, so the continuation
hypothesis `oneLtHalfPlane → openRightHalfPlane` is trivial.  This populates
the previously-abstract `GenuineFInfiniteContinuation` slot of the cover
closure with a concrete witness.
-/
def genuineFInfiniteContinuation : GenuineFInfiniteContinuation :=
  C2.genuineFInfiniteContinuationData

/--
Concrete near-axis witness for `genuineFInfinite`, obtained from the
continuation witness via `C2.GenuineFInfiniteNearAxisData.of_continuation`.

This is **unconditional**: the proof uses only analyticity of
`genuineFInfinite = c₀ · ζ` on the punctured open right half-plane, the
isolation of analytic zeros, and the non-vanishing of `genuineFInfinite` at
`s = 2` (where `ζ(2) ≠ 0` by `riemannZeta_ne_zero_of_one_lt_re`).
-/
noncomputable def genuineFInfiniteNearAxis : BulkAntiMiracleNearAxisData :=
  C2.GenuineFInfiniteNearAxisData.of_continuation genuineFInfiniteContinuation

/--
Empty-edge witness: the empty region trivially satisfies the non-vanishing
clause.  Useful as a placeholder when the cover is built entirely from the
near-axis and bulk pieces (i.e. when `offCriticalStrip ⊆ near ∪ bulk`).
-/
def genuineFInfiniteEdgeEmpty : BulkAntiMiracleEdgeData where
  edgeRegion := ∅
  edge_nonvanishing := fun {_} hs => hs.elim

/--
Regional non-cancellation lemma extracted from the generic tilt data: if the
generic bulk anti-miracle witness uses `F = genuineFInfinite` and the bulk
region is exactly the off-critical strip, then `genuineFInfinite` is non-zero
on the off-critical strip.  This is a useful intermediate step but is **not**
itself a closure of RH (cf. note below). -/
theorem genuineFInfinite_nonvanishing_of_bulkAntiMiracleTilt_on_offCriticalStrip
    (data : BulkAntiMiracleTiltData)
    (hF : data.F = genuineFInfinite)
    (hRegion : ∀ ⦃s : ℂ⦄, C2.offCriticalStrip s → s ∈ data.bulkRegion) :
    C2.offCriticalStripNonvanishing genuineFInfinite :=
  C2.offCriticalStripNonvanishing_genuineFInfinite_of_bulkResolventNonCancellationTilt
    data hF hRegion

/--
**Anti-miracle + identity closure of RH** (limit-level, cover form).

This is the unified closure of the C2 route in the form prescribed by the
notes: a regional bulk anti-miracle witness `bulk` (pinned to
`genuineFInfinite`), a near-axis Taylor witness `near`, an edge witness
`edge`, a covering hypothesis `cover : offCriticalStrip ⊆ near ∪ bulk ∪ edge`,
and a continuation witness extending `genuineFInfinite = c₀ · ζ` to the open
right half-plane. -/
theorem RiemannHypothesis_of_bulkAntiMiracle
    (continuation : GenuineFInfiniteContinuation)
    (near : BulkAntiMiracleNearAxisData)
    (bulk : BulkAntiMiracleData)
    (edge : BulkAntiMiracleEdgeData)
    (cover : ∀ s : ℂ, C2.offCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_regionalBulkCover
    continuation near bulk edge cover

/--
**Anti-miracle + identity closure of RH** (bounds-level, cover form): same as
`RiemannHypothesis_of_bulkAntiMiracle` but with the bound-level scalar data
on the bulk piece. -/
theorem RiemannHypothesis_of_bulkAntiMiracleBounds
    (continuation : GenuineFInfiniteContinuation)
    (near : BulkAntiMiracleNearAxisData)
    (bulk : BulkAntiMiracleBoundsData)
    (edge : BulkAntiMiracleEdgeData)
    (cover : ∀ s : ℂ, C2.offCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_regionalBulkBoundsCover
    continuation near bulk edge cover

/--
**Reduced terminal**: closes RH from any `BulkAntiMiracleBoundsData` whose
bulk region together with the near-axis region (from
`genuineFInfiniteNearAxis`) covers the off-critical strip.

This isolates the remaining analytic obligation to exactly two inputs:
1. A `bulk : BulkAntiMiracleBoundsData` witnessing non-cancellation of the
   resolvent in some bulk region;
2. A covering hypothesis `offCriticalStrip ⊆ nearAxisRegion ∪ bulk.bulkRegion`.

All other pieces (continuation, near-axis from continuation, empty edge) are
discharged here by the concrete witnesses above.
-/
theorem RiemannHypothesis_of_offCriticalBulkCover
    (bulk : BulkAntiMiracleBoundsData)
    (cover : ∀ s : ℂ, C2.offCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        s ∈ bulk.bulkRegion) :
    RiemannHypothesis :=
  RiemannHypothesis_of_bulkAntiMiracleBounds
    genuineFInfiniteContinuation
    genuineFInfiniteNearAxis
    bulk
    genuineFInfiniteEdgeEmpty
    (fun s hs => (cover s hs).imp id Or.inl)

/-! ### Functional-equation reduction to the upper half-strip

The Riemann functional equation
`ζ(1 − s) = 2 · (2π)^{−s} · Γ(s) · cos(πs/2) · ζ(s)`
implies that `ζ` is symmetric (zero-wise) under `s ↦ 1 − s`.  In particular,
non-vanishing of `ζ` (equivalently of `genuineFInfinite = c₀ · ζ`) on the
upper half of the off-critical strip `{s | 1/2 < s.re < 1}` is enough to
conclude non-vanishing on the entire off-critical strip
`{s | 0 < s.re < 1, s.re ≠ 1/2}`.

This reduction is purely analytic and uses only Mathlib's
`riemannZeta_one_sub`, `Complex.Gamma_ne_zero`, and `Complex.cos_ne_zero_iff`.
-/

/-- The upper half of the off-critical strip: `1/2 < Re s < 1`. -/
def upperOffCriticalStrip (s : ℂ) : Prop :=
  (1 : ℝ) / 2 < s.re ∧ s.re < 1

/--
**Functional-equation reduction (for `ζ`)**: non-vanishing of `ζ` on the
upper half-strip `1/2 < Re s < 1` implies non-vanishing on the full
off-critical strip.
-/
theorem offCriticalStripNonvanishing_zeta_of_upper
    (hUpper : ∀ s : ℂ, upperOffCriticalStrip s → riemannZeta s ≠ 0) :
    C2.offCriticalStripNonvanishing riemannZeta := by
  intro s hs
  obtain ⟨hpos, hlt1, hne⟩ := hs
  rcases lt_or_gt_of_ne hne with hlow | hup
  · -- Case `0 < s.re < 1/2`: use the functional equation.
    set w : ℂ := 1 - s with hw
    have hw_re : w.re = 1 - s.re := by simp [hw]
    have hw_upper : upperOffCriticalStrip w := by
      refine ⟨?_, ?_⟩
      · rw [hw_re]; linarith
      · rw [hw_re]; linarith
    have hζw_ne : riemannZeta w ≠ 0 := hUpper w hw_upper
    -- `s ≠ -n` for any natural `n` because `s.re > 0`.
    have hs_ne_neg_nat : ∀ n : ℕ, s ≠ -n := by
      intro n hsn
      have : s.re = -(n : ℝ) := by
        simpa using congrArg Complex.re hsn
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    -- `s ≠ 1` since `s.re < 1/2 < 1`.
    have hs_ne_one : s ≠ 1 := by
      intro hs1
      have : s.re = 1 := by simpa using congrArg Complex.re hs1
      linarith
    -- Functional equation: `ζ(1 − s) = 2 (2π)^(−s) Γ(s) cos(πs/2) ζ(s)`.
    have hFE :
        riemannZeta (1 - s) =
          2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s :=
      riemannZeta_one_sub hs_ne_neg_nat hs_ne_one
    -- All factors of the right-hand side (except possibly `ζ s`) are non-zero.
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2pi)
    have hGamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs_ne_neg_nat
    have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
      rw [Complex.cos_ne_zero_iff]
      intro k hk
      -- From `π · s / 2 = (2k+1) · π / 2`, derive `s = 2k + 1`.
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h2c : (2 : ℂ) ≠ 0 := two_ne_zero
      have hs_eq : s = 2 * (k : ℂ) + 1 := by
        have h := hk
        field_simp at h
        linear_combination h
      -- Take real parts: `s.re = 2k + 1`.
      have hre : s.re = 2 * (k : ℝ) + 1 := by
        have := congrArg Complex.re hs_eq
        simpa using this
      -- `s.re ∈ (0, 1/2)` excludes any odd integer `2k+1`.
      rcases le_or_gt 0 (k : ℝ) with hk0 | hk0
      · -- `k ≥ 0` ⇒ `2k+1 ≥ 1 > 1/2 > s.re`.
        linarith
      · -- `k < 0` ⇒ `k ≤ -1` (integer) ⇒ `2k+1 ≤ -1 < 0 < s.re`.
        have hZ : (k : ℤ) < 0 := by exact_mod_cast hk0
        have hkZ : (k : ℤ) ≤ -1 := by omega
        have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hkZ
        linarith
    -- Combine: `ζ(1 − s) ≠ 0` forces `ζ s ≠ 0`.
    intro hζs
    apply hζw_ne
    show riemannZeta (1 - s) = 0
    rw [hFE, hζs]; ring
  · exact hUpper s ⟨hup, hlt1⟩

/--
**Functional-equation reduction (for `genuineFInfinite`)**: non-vanishing of
`genuineFInfinite = c₀ · ζ` on the upper half-strip implies non-vanishing on
the full off-critical strip.  Since `c₀ ≠ 0` on the open right half-plane,
this reduces to the reduction for `ζ` above.
-/
theorem offCriticalStripNonvanishing_genuineFInfinite_of_upper
    (hUpper : ∀ s : ℂ, upperOffCriticalStrip s → genuineFInfinite s ≠ 0) :
    C2.offCriticalStripNonvanishing genuineFInfinite := by
  -- First show the corresponding statement for ζ.
  have hUpperZeta : ∀ s : ℂ, upperOffCriticalStrip s → riemannZeta s ≠ 0 := by
    intro s hs
    have hpos : 0 < s.re := by linarith [hs.1]
    have hF : genuineFInfinite s = c0 s * riemannZeta s :=
      C2.genuineFInfinite_eq_c0_mul_riemannZeta s
    have hF_ne : genuineFInfinite s ≠ 0 := hUpper s hs
    intro hζ
    apply hF_ne
    rw [hF, hζ, mul_zero]
  have hζFull := offCriticalStripNonvanishing_zeta_of_upper hUpperZeta
  -- Now bridge back: `genuineFInfinite s ≠ 0` ↔ `ζ s ≠ 0` on the strip.
  intro s hs
  have hpos : 0 < s.re := hs.1
  have hF : genuineFInfinite s = c0 s * riemannZeta s :=
    C2.genuineFInfinite_eq_c0_mul_riemannZeta s
  rw [hF]
  exact mul_ne_zero (c0_ne_zero_of_re_pos hpos) (hζFull s hs)

/--
**Closure of RH from upper half-strip non-vanishing of `ζ`**: this is the
Phase-2 deliverable.  It reduces the entire off-critical task to the
upper half-strip `{s | 1/2 < Re s < 1}`.
-/
theorem RiemannHypothesis_of_upperOffCriticalStripNonvanishing_zeta
    (hUpper : ∀ s : ℂ, upperOffCriticalStrip s → riemannZeta s ≠ 0) :
    RiemannHypothesis :=
  C2.mathlibRiemannHypothesis_of_offCriticalStripNonvanishing
    (offCriticalStripNonvanishing_zeta_of_upper hUpper)

/--
Same as above but expressed for `genuineFInfinite = c₀ · ζ`.
-/
theorem RiemannHypothesis_of_upperOffCriticalStripNonvanishing_genuineFInfinite
    (hUpper : ∀ s : ℂ, upperOffCriticalStrip s → genuineFInfinite s ≠ 0) :
    RiemannHypothesis := by
  apply RiemannHypothesis_of_upperOffCriticalStripNonvanishing_zeta
  intro s hs
  have hpos : 0 < s.re := by linarith [hs.1]
  have hF : genuineFInfinite s = c0 s * riemannZeta s :=
    C2.genuineFInfinite_eq_c0_mul_riemannZeta s
  have hF_ne : genuineFInfinite s ≠ 0 := hUpper s hs
  intro hζ
  apply hF_ne
  rw [hF, hζ, mul_zero]

/--
Upper-half bulk cover closure.

This is the preferred audit target after the functional-equation reduction:
instead of covering the whole off-critical strip directly, it is enough to
cover the upper half-strip by the near-axis, resolvent bulk, and edge regions.
The lower half-strip is then supplied by the zeta functional equation.
-/
theorem RiemannHypothesis_of_upperBulkAntiMiracleBoundsCover
    (near : BulkAntiMiracleNearAxisData)
    (bulk : BulkAntiMiracleBoundsData)
    (edge : BulkAntiMiracleEdgeData)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  apply RiemannHypothesis_of_upperOffCriticalStripNonvanishing_genuineFInfinite
  intro s hs
  rcases cover s hs with hnear | hrest
  · exact near.near_axis.nonvanishing_of_mem hnear
  · rcases hrest with hbulk | hedge
    · exact C2.genuineFInfinite_nonvanishing_of_regionalBulkBoundsData bulk hbulk
    · exact edge.edge_nonvanishing hedge

/--
Reduced upper-half closure with the canonical near-axis witness and empty edge.

The remaining inputs are exactly a pinned bulk anti-miracle bounds package and
a cover of `1/2 < Re(s) < 1` by the canonical near-axis region plus that bulk
region.
-/
theorem RiemannHypothesis_of_upperOffCriticalBulkCover
    (bulk : BulkAntiMiracleBoundsData)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        s ∈ bulk.bulkRegion) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperBulkAntiMiracleBoundsCover
    genuineFInfiniteNearAxis
    bulk
    genuineFInfiniteEdgeEmpty
    (fun s hs => (cover s hs).imp id Or.inl)

/-! ### Concrete bulk anti-miracle witness (balancing seed)

This block exposes the concrete `genuineFInfinite`-pinned bulk anti-miracle
witness built from the canonical odd-tail balancing seed
(`c2OddTailBalancingSeed`).  The resulting `BulkAntiMiracleBoundsData` is
parametric in the scalar admissibility constants
`tiltConstant/Scale, horizontalConstant/Scale/Ratio, cutoffConstant/Scale`,
which are exactly the inputs of the established C2 scaled-seeded tilt model.

**Caveat (regional vacuity).**  As currently formalized, the underlying region
`c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion ...` is provably **empty**
(see `c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion_eq_empty` in
`LeanC2/Route/BulkOddTail.lean`): the underlying estimates structure requires
both `1 < s.re` and `offCriticalStrip s`, which are contradictory.  Thus the
witness exposed here is vacuous as a bulk piece of a cover of
`offCriticalStrip` — closing RH via this route requires first constructing a
strictly-off-critical analytic estimates structure (currently only the
`Re(s) > 1` variant
`c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtRegion` is non-vacuous, and
that region lies outside `offCriticalStrip`).  The abbreviation is kept for
notational stability; replace it once a non-vacuous concrete bulk witness is
available.
-/

/-- Concrete bulk anti-miracle witness using the canonical odd-tail balancing
seed.  See the caveat above: the underlying region is currently empty, so
this witness is mathematically vacuous as a bulk piece of a cover of the
off-critical strip. -/
noncomputable abbrev bulkAntiMiracleBoundsData_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    BulkAntiMiracleBoundsData :=
  C2.c2OddTailGenuineBulkBoundsData_balancingSeed
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

/-! ### Abstract off-critical bulk anti-miracle witness

This block exposes the **non-vacuous abstract** bulk anti-miracle witness for
the off-critical strip, built directly from
`C2.c2AnalyticBulkBoundsData`.  The underlying region only requires
`offCriticalStrip s` (no `1 < s.re` constraint), so the witness lives in the
genuine off-critical region.

The witness is parametric in:
- analytic remainders `Gdelta, Edelta : ℂ → ℂ` whose sum, added to the
  vertical resolvent depth-two tail, equals the genuine numerator;
- upper bounds `GUpper, EUpper : ℂ → ℝ` certifying `‖G_δ‖ ≤ GUpper` and
  `‖E_δ‖ ≤ EUpper`;
- a dominance hypothesis `GUpper + EUpper < ‖q‖² / (1 + ‖q‖)` carrying the
  positivity computation that blocks the genuine non-cancellation;
- an identity hypothesis `genuineFInfinite s = c2AnalyticBulkF G_δ E_δ s`
  pinning the abstract witness to the C2 genuine numerator on the off-critical
  region.

The dominance bound `c2AnalyticBulkAllowance s = ‖q s‖² / (1 + ‖q s‖)` is the
sharp vertical resolvent allowance derived in `Route/BulkReal.lean`.
-/

/-- Off-critical bulk region (abstract form): the set of `s` where
`offCriticalStrip s` holds, the bounds `‖G_δ‖ ≤ GUpper` and `‖E_δ‖ ≤ EUpper`
are satisfied, and the dominance `GUpper + EUpper < ‖q‖² / (1 + ‖q‖)` holds. -/
abbrev bulkAntiMiracleOffCriticalRegion
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) : Set ℂ :=
  C2.c2AnalyticBulkRegion Gdelta Edelta GUpper EUpper

/-- Concrete off-critical bulk anti-miracle witness, pinned to
`genuineFInfinite`.  This is the non-vacuous replacement for
`bulkAntiMiracleBoundsData_balancingSeed`: the underlying region only requires
`offCriticalStrip s`, so any concrete supply of `(G_δ, E_δ, GUpper, EUpper)`
satisfying the dominance and the identity `genuineFInfinite = q² + G_δ + E_δ`
yields a non-vacuous bulk piece of the cover. -/
noncomputable def bulkAntiMiracleBoundsData_offCritical
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ)
    (hF : ∀ s : ℂ,
      s ∈ bulkAntiMiracleOffCriticalRegion Gdelta Edelta GUpper EUpper →
        genuineFInfinite s = C2.c2AnalyticBulkF Gdelta Edelta s) :
    BulkAntiMiracleBoundsData :=
  C2.GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    (C2.c2AnalyticBulkBoundsData Gdelta Edelta GUpper EUpper) hF

/--
**Off-critical anti-miracle + identity closure of RH** (bounds-level, cover form).

Convenience adapter combining the abstract off-critical bulk anti-miracle
witness `bulkAntiMiracleBoundsData_offCritical` with a near-axis Taylor
witness, an edge witness, a cover, and a continuation witness.  The cover
hypothesis must use the off-critical region
`bulkAntiMiracleOffCriticalRegion G_δ E_δ GUpper EUpper` for the bulk piece. -/
theorem RiemannHypothesis_of_bulkAntiMiracleOffCritical
    (continuation : GenuineFInfiniteContinuation)
    (near : BulkAntiMiracleNearAxisData)
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ)
    (hF : ∀ s : ℂ,
      s ∈ bulkAntiMiracleOffCriticalRegion Gdelta Edelta GUpper EUpper →
        genuineFInfinite s = C2.c2AnalyticBulkF Gdelta Edelta s)
    (edge : BulkAntiMiracleEdgeData)
    (cover : ∀ s : ℂ, C2.offCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulkAntiMiracleOffCriticalRegion Gdelta Edelta GUpper EUpper ∨
          s ∈ edge.edgeRegion) :
    RiemannHypothesis :=
  RiemannHypothesis_of_bulkAntiMiracleBounds continuation near
    (bulkAntiMiracleBoundsData_offCritical Gdelta Edelta GUpper EUpper hF)
    edge cover

/--
Preferred concrete target after the upper-half reduction.

To close RH through this theorem, it is enough to provide analytic error terms
`Gdelta`, `Edelta` and scalar bounds `GUpper`, `EUpper` such that:

* `genuineFInfinite = c2AnalyticBulkF Gdelta Edelta` on the certified bulk
  region;
* the canonical near-axis region plus that bulk region covers
  `1/2 < Re(s) < 1`.

Membership in `bulkAntiMiracleOffCriticalRegion` carries the actual final
dominance inequality `GUpper s + EUpper s < c2AnalyticBulkAllowance s`.
-/
theorem RiemannHypothesis_of_upperBulkAntiMiracleOffCritical
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ)
    (hF : ∀ s : ℂ,
      s ∈ bulkAntiMiracleOffCriticalRegion Gdelta Edelta GUpper EUpper →
        genuineFInfinite s = C2.c2AnalyticBulkF Gdelta Edelta s)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        s ∈ bulkAntiMiracleOffCriticalRegion Gdelta Edelta GUpper EUpper) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOffCriticalBulkCover
    (bulkAntiMiracleBoundsData_offCritical Gdelta Edelta GUpper EUpper hF)
    cover

/-! ### Full-resolvent target after the functional-equation reduction -/

/--
The complete resolvent defect after choosing a depth-two numerator `K₂(s)`.

This is the flexible upper-half bulk target: pick a concrete nonzero main
numerator `K₂`, prove that

`genuineFInfinite s = K₂(s) / (1 - q(s)) + defect(s)`,

and dominate the defect by the corresponding resolvent allowance.
-/
noncomputable def upperFullResolventDefect (K2 : ℂ → ℂ) (s : ℂ) : ℂ :=
  genuineFInfinite s - K2 s / (1 - C2.q s)

/--
Bulk region for the full-resolvent defect target.

The field `GUpper s < K2Lower s / (1 + ‖q s‖)` is the final resolvent
dominance inequality.  The theorem below supplies the functional-equation
reduction, the near-axis piece, and the empty edge piece.
-/
def upperFullResolventDefectRegion
    (K2 : ℂ → ℂ) (K2Lower GUpper : ℂ → ℝ) : Set ℂ :=
  {s | C2.offCriticalStrip s ∧
    K2Lower s ≤ ‖K2 s‖ ∧
    ‖upperFullResolventDefect K2 s‖ ≤ GUpper s ∧
    GUpper s < K2Lower s / (1 + ‖C2.q s‖)}

noncomputable def upperFullResolventDefectBoundsData
    (K2 : ℂ → ℂ) (K2Lower GUpper : ℂ → ℝ) :
    BulkAntiMiracleBoundsData :=
  C2.GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    ({
      F := genuineFInfinite
      bulkRegion := upperFullResolventDefectRegion K2 K2Lower GUpper
      Kdelta := genuineFInfinite
      K2 := K2
      Gdelta := upperFullResolventDefect K2
      Edelta := fun _ => 0
      K2Lower := K2Lower
      GUpper := GUpper
      EUpper := fun _ => 0
      bulk_offCritical := by
        intro _s hs
        exact hs.1
      decomposition := by
        intro _s _hs
        simp
      resolvent_shape := by
        intro s _hs
        unfold upperFullResolventDefect
        ring
      K2_lower := by
        intro _s hs
        exact hs.2.1
      G_upper := by
        intro _s hs
        exact hs.2.2.1
      E_upper := by
        intro _s _hs
        simp
      dominance_bounds := by
        intro _s hs
        simpa using hs.2.2.2
    } : C2.RegionalVerticalBulkBoundsData)
    (fun _s _hs => rfl)

/--
Full-resolvent upper-half endpoint.

To close RH through this theorem, it is enough to provide a concrete numerator
`K₂`, a lower bound for `‖K₂‖`, an upper bound for the complete resolvent
defect, and a cover of `1/2 < Re(s) < 1` by the canonical near-axis region plus
the resulting full-resolvent bulk region.
-/
theorem RiemannHypothesis_of_upperFullResolventDefectBound
    (K2 : ℂ → ℂ) (K2Lower GUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        s ∈ upperFullResolventDefectRegion K2 K2Lower GUpper) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOffCriticalBulkCover
    (upperFullResolventDefectBoundsData K2 K2Lower GUpper)
    cover

/--
Sharp full-resolvent dominance endpoint.

This is the cleanest target for the final inequality after choosing a concrete
resolvent numerator `K₂`: outside the canonical near-axis region on the upper
half-strip, prove

`‖genuineFInfinite s - K₂(s)/(1-q(s))‖ < ‖K₂(s)‖/(1+‖q(s)‖)`.
-/
theorem RiemannHypothesis_of_upperFullResolventDefectDominance
    (K2 : ℂ → ℂ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperFullResolventDefect K2 s‖ <
          ‖K2 s‖ / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperFullResolventDefectBound
    K2 (fun s => ‖K2 s‖) (fun s => ‖upperFullResolventDefect K2 s‖)
    (fun s hs => by
      rcases cover s hs with hnear | hdom
      · exact Or.inl hnear
      · exact Or.inr
          ⟨⟨by linarith [hs.1], hs.2, ne_of_gt hs.1⟩,
            le_rfl, le_rfl, hdom⟩)

/-- Resolvent numerator generated by an approximate odd channel `Z`. -/
noncomputable def upperOddChannelResolventNumerator (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  (2 : ℂ) * C2.q s ^ 2 * Z s

theorem upperFullResolventDefect_oddChannelNumerator_eq
    (Z : ℂ → ℂ) {s : ℂ} (hs : upperOffCriticalStrip s) :
    upperFullResolventDefect (upperOddChannelResolventNumerator Z) s =
      (2 : ℂ) * C2.verticalDepthTailFromTwo s *
        (C2.continuedOddDirichletChannel s - Z s) := by
  have hpos : 0 < s.re := by linarith [hs.1]
  have hpunc : s ∈ C2.puncturedOpenRightHalfPlane := by
    refine ⟨hpos, ?_⟩
    intro hsone
    have : s.re = 1 := by simpa using congrArg Complex.re hsone
    linarith [hs.2]
  have hF :
      genuineFInfinite s = C2.continuedCentralOddChannel s :=
    C2.GenuineFInfiniteContinuationData.eq_continuedCentralOddChannel_on_punctured
      C2.genuineFInfiniteContinuationData s hpunc
  unfold upperFullResolventDefect upperOddChannelResolventNumerator
  rw [hF]
  unfold C2.continuedCentralOddChannel C2.centralFromOddChannel
  rw [C2.verticalDepthTailFromTwo_eq s hpos]
  unfold C2.verticalResolvent
  rw [div_eq_mul_inv]
  ring

theorem upperOddChannelResolvent_defect_norm_le_errorUpper
    (Z : ℂ → ℂ) (errorUpper : ℂ → ℝ) {s : ℂ}
    (hpos : 0 < s.re)
    (herror :
      ‖C2.continuedOddDirichletChannel s - Z s‖ ≤ errorUpper s) :
    ‖(2 : ℂ) * C2.verticalDepthTailFromTwo s *
        (C2.continuedOddDirichletChannel s - Z s)‖ ≤
      2 * C2.verticalDepthTailUpper s * errorUpper s := by
  have htail :
      ‖C2.verticalDepthTailFromTwo s‖ ≤ C2.verticalDepthTailUpper s :=
    C2.verticalDepthTailFromTwo_norm_le_upper_of_re_pos s hpos
  have htail_nonneg : 0 ≤ C2.verticalDepthTailUpper s :=
    C2.verticalDepthTailUpper_nonneg_of_re_pos s hpos
  have hmul :
      ‖C2.verticalDepthTailFromTwo s‖ *
          ‖C2.continuedOddDirichletChannel s - Z s‖ ≤
        C2.verticalDepthTailUpper s * errorUpper s :=
    mul_le_mul htail herror (norm_nonneg _) htail_nonneg
  calc
    ‖(2 : ℂ) * C2.verticalDepthTailFromTwo s *
        (C2.continuedOddDirichletChannel s - Z s)‖
        = 2 * ‖C2.verticalDepthTailFromTwo s‖ *
            ‖C2.continuedOddDirichletChannel s - Z s‖ := by
            simp
    _ = 2 * (‖C2.verticalDepthTailFromTwo s‖ *
            ‖C2.continuedOddDirichletChannel s - Z s‖) := by
            ring
    _ ≤ 2 * (C2.verticalDepthTailUpper s * errorUpper s) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = 2 * C2.verticalDepthTailUpper s * errorUpper s := by ring

/--
Odd-channel full-resolvent endpoint.

After the functional-equation reduction, it is enough to approximate the
continued odd channel by a chosen `Z` so that the induced complete-resolvent
defect is dominated by the `K₂ = 2 q² Z` allowance on the upper half-strip
outside the canonical near-axis region.
-/
theorem RiemannHypothesis_of_upperOddChannelResolventApproximation
    (Z : ℂ → ℂ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖(2 : ℂ) * C2.verticalDepthTailFromTwo s *
            (C2.continuedOddDirichletChannel s - Z s)‖ <
          ‖upperOddChannelResolventNumerator Z s‖ / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperFullResolventDefectDominance
    (upperOddChannelResolventNumerator Z)
    (fun s hs => by
      rcases cover s hs with hnear | hdom
      · exact Or.inl hnear
      · exact Or.inr (by
          rwa [upperFullResolventDefect_oddChannelNumerator_eq Z hs]))

/--
Odd-channel full-resolvent endpoint in scalar error-bound form.

This is the practical version for certificates: provide an upper bound for
`‖continuedOddDirichletChannel - Z‖`, then prove that the induced scalar error
is below the resolvent allowance of `K₂ = 2 q² Z`.
-/
theorem RiemannHypothesis_of_upperOddChannelResolventErrorBound
    (Z : ℂ → ℂ) (errorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖C2.continuedOddDirichletChannel s - Z s‖ ≤ errorUpper s ∧
          2 * C2.verticalDepthTailUpper s * errorUpper s <
            ‖upperOddChannelResolventNumerator Z s‖ /
              (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOddChannelResolventApproximation Z
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · exact Or.inr
          (lt_of_le_of_lt
            (upperOddChannelResolvent_defect_norm_le_errorUpper
              Z errorUpper (by linarith [hs.1]) hbulk.1)
            hbulk.2))

/--
Scalar cancellation for the odd-channel resolvent bound.

Because `K₂ = 2 q² Z` and `verticalDepthTailUpper = ‖q‖²/(1-‖q‖)`, the
full scalar dominance follows from the cleaner relative approximation target

`errorUpper < ‖Z‖ * (1 - ‖q‖) / (1 + ‖q‖)`.
-/
theorem upperOddChannelResolvent_dominance_of_relativeError
    (Z : ℂ → ℂ) (errorUpper : ℂ → ℝ) {s : ℂ}
    (hpos : 0 < s.re)
    (hrelative :
      errorUpper s <
        ‖Z s‖ * (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    2 * C2.verticalDepthTailUpper s * errorUpper s <
      ‖upperOddChannelResolventNumerator Z s‖ / (1 + ‖C2.q s‖) := by
  have hq_lt : ‖C2.q s‖ < 1 := C2.q_norm_lt_one_of_re_pos s hpos
  have hq_ne : C2.q s ≠ 0 := by
    simpa [C2.q, C2.verticalRatio] using C2.complexDirichletDepthRatio_ne_zero s
  have hq_pos : 0 < ‖C2.q s‖ := norm_pos_iff.mpr hq_ne
  have hden_pos : 0 < 1 - ‖C2.q s‖ := by
    linarith [norm_nonneg (C2.q s), hq_lt]
  have hplus_pos : 0 < 1 + ‖C2.q s‖ := by positivity
  have htail_pos : 0 < C2.verticalDepthTailUpper s := by
    unfold C2.verticalDepthTailUpper
    exact div_pos (pow_pos hq_pos 2) hden_pos
  have hcoef_pos : 0 < 2 * C2.verticalDepthTailUpper s := by positivity
  have hmul :
      (2 * C2.verticalDepthTailUpper s) * errorUpper s <
        (2 * C2.verticalDepthTailUpper s) *
          (‖Z s‖ * (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :=
    mul_lt_mul_of_pos_left hrelative hcoef_pos
  have hnum :
      ‖upperOddChannelResolventNumerator Z s‖ =
        2 * ‖C2.q s‖ ^ 2 * ‖Z s‖ := by
    unfold upperOddChannelResolventNumerator
    simp [norm_pow]
  have hrhs :
      (2 * C2.verticalDepthTailUpper s) *
          (‖Z s‖ * (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) =
        ‖upperOddChannelResolventNumerator Z s‖ / (1 + ‖C2.q s‖) := by
    rw [hnum]
    unfold C2.verticalDepthTailUpper
    field_simp [hden_pos.ne', hplus_pos.ne']
  calc
    2 * C2.verticalDepthTailUpper s * errorUpper s
        = (2 * C2.verticalDepthTailUpper s) * errorUpper s := by ring
    _ < (2 * C2.verticalDepthTailUpper s) *
          (‖Z s‖ * (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) := hmul
    _ = ‖upperOddChannelResolventNumerator Z s‖ / (1 + ‖C2.q s‖) := hrhs

/--
Odd-channel endpoint in the reduced relative-error form.

This is the bound shape to aim for after choosing `Z`: approximate the continued
odd channel by `Z`, then prove the relative error is below the explicit
resolvent margin.
-/
theorem RiemannHypothesis_of_upperOddChannelResolventRelativeError
    (Z : ℂ → ℂ) (errorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖C2.continuedOddDirichletChannel s - Z s‖ ≤ errorUpper s ∧
          errorUpper s <
            ‖Z s‖ * (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOddChannelResolventErrorBound Z errorUpper
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · exact Or.inr
          ⟨hbulk.1,
            upperOddChannelResolvent_dominance_of_relativeError
              Z errorUpper (by linarith [hs.1]) hbulk.2⟩)

/-! ### Eta-transported choice of `Z` for the odd-channel resolvent -/

/--
Finite alternating eta partial sum

`η_N(s) = ∑_{n=1}^N (-1)^(n-1) n^{-s}`.

This is the non-circular approximation target on the critical strip: unlike the
ordinary Dirichlet series for `ζ`, the alternating eta series is the natural
candidate below `Re(s)=1`.
-/
noncomputable def upperEtaAlternatingPartial (N : ℕ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range N)
    (fun n => (-1 : ℂ) ^ n * C2.complexDirichletCoeff s (n + 1))

/--
Transport factor from the eta channel to the continued odd channel:

`(1 - 2^{-s}) / (1 - 2^{1-s})`.

On the upper off-critical strip the denominator is the eta Euler factor and is
nonzero; the corresponding nonzero proof is a separate analytic estimate, so
this definition keeps the candidate `Z` itself total.
-/
noncomputable def upperEtaOddChannelTransportFactor (s : ℂ) : ℂ :=
  (1 - C2.complexDirichletCoeff s 2) /
    (1 - (2 : ℂ) * C2.complexDirichletCoeff s 2)

theorem upperEtaOddChannelTransportFactor_den_ne_zero_of_upperOffCriticalStrip
    {s : ℂ} (hs : upperOffCriticalStrip s) :
    1 - (2 : ℂ) * C2.complexDirichletCoeff s 2 ≠ 0 := by
  intro hzero
  have heq : (2 : ℂ) * C2.complexDirichletCoeff s 2 = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm_eq : ‖(2 : ℂ) * C2.complexDirichletCoeff s 2‖ = 1 := by
    rw [heq]
    simp
  have hcoeff_norm :
      ‖C2.complexDirichletCoeff s 2‖ = (2 : ℝ) ^ (-s.re) :=
    C2.complexDirichletCoeff_norm_eq_rpow_neg_re s (by norm_num)
  have hnorm :
      ‖(2 : ℂ) * C2.complexDirichletCoeff s 2‖ =
        (2 : ℝ) * (2 : ℝ) ^ (-s.re) := by
    rw [norm_mul, hcoeff_norm]
    norm_num
  have hpoweq :
      (2 : ℝ) * (2 : ℝ) ^ (-s.re) = (2 : ℝ) ^ (1 - s.re) := by
    calc
      (2 : ℝ) * (2 : ℝ) ^ (-s.re)
          = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s.re) := by
              rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((1 : ℝ) + (-s.re)) := by
              rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      _ = (2 : ℝ) ^ (1 - s.re) := by ring_nf
  have hexp_pos : 0 < 1 - s.re := by linarith [hs.2]
  have hpow_gt : 1 < (2 : ℝ) ^ (1 - s.re) := by
    have h :=
      Real.rpow_lt_rpow_of_exponent_lt
        (by norm_num : (1 : ℝ) < 2) hexp_pos
    simpa using h
  have hnorm_gt : 1 < ‖(2 : ℂ) * C2.complexDirichletCoeff s 2‖ := by
    rw [hnorm, hpoweq]
    exact hpow_gt
  linarith [hnorm_eq, hnorm_gt]

/--
Canonical non-circular choice of the odd-channel approximation:

`Z_N(s) = ((1 - 2^{-s}) / (1 - 2^{1-s})) η_N(s)`.
-/
noncomputable def upperEtaOddChannelApproximation (N : ℕ) : ℂ → ℂ :=
  fun s => upperEtaOddChannelTransportFactor s * upperEtaAlternatingPartial N s

/-- Analytic eta channel `(1 - 2^{1-s}) ζ(s)`. -/
noncomputable def upperEtaChannel (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) * C2.complexDirichletCoeff s 2) * riemannZeta s

/-- Transport any eta-side approximation into the continued odd channel. -/
noncomputable def upperEtaOddChannelApproximationOf
    (etaApprox : ℂ → ℂ) : ℂ → ℂ :=
  fun s => upperEtaOddChannelTransportFactor s * etaApprox s

theorem upperEtaOddChannelApproximation_eq_of_partial (N : ℕ) :
    upperEtaOddChannelApproximation N =
      upperEtaOddChannelApproximationOf (upperEtaAlternatingPartial N) := rfl

theorem continuedOddDirichletChannel_eq_transportFactor_mul_upperEtaChannel
    {s : ℂ}
    (hden :
      1 - (2 : ℂ) * C2.complexDirichletCoeff s 2 ≠ 0) :
    C2.continuedOddDirichletChannel s =
      upperEtaOddChannelTransportFactor s * upperEtaChannel s := by
  unfold C2.continuedOddDirichletChannel upperEtaOddChannelTransportFactor upperEtaChannel
  set a : ℂ := C2.complexDirichletCoeff s 2
  set z : ℂ := riemannZeta s
  change (1 - a) * z = ((1 - a) / (1 - (2 : ℂ) * a)) * ((1 - (2 : ℂ) * a) * z)
  have hdena : 1 - (2 : ℂ) * a ≠ 0 := by simpa [a] using hden
  have hcancel : (1 - (2 : ℂ) * a)⁻¹ * (1 - (2 : ℂ) * a) = 1 :=
    inv_mul_cancel₀ hdena
  rw [div_eq_mul_inv]
  calc
    (1 - a) * z
        = (1 - a) * (((1 - (2 : ℂ) * a)⁻¹ *
            (1 - (2 : ℂ) * a)) * z) := by rw [hcancel]; ring
    _ = ((1 - a) * (1 - (2 : ℂ) * a)⁻¹) *
          ((1 - (2 : ℂ) * a) * z) := by ring

theorem upperEtaOddChannelApproximationOf_error_le_transport
    (etaApprox : ℂ → ℂ) (etaErrorUpper : ℂ → ℝ) {s : ℂ}
    (hden :
      1 - (2 : ℂ) * C2.complexDirichletCoeff s 2 ≠ 0)
    (heta :
      ‖upperEtaChannel s - etaApprox s‖ ≤ etaErrorUpper s) :
    ‖C2.continuedOddDirichletChannel s -
        upperEtaOddChannelApproximationOf etaApprox s‖ ≤
      ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s := by
  have hidentity :
      C2.continuedOddDirichletChannel s =
        upperEtaOddChannelTransportFactor s * upperEtaChannel s :=
    continuedOddDirichletChannel_eq_transportFactor_mul_upperEtaChannel hden
  have hsub :
      upperEtaOddChannelTransportFactor s * upperEtaChannel s -
          upperEtaOddChannelApproximationOf etaApprox s =
        upperEtaOddChannelTransportFactor s *
          (upperEtaChannel s - etaApprox s) := by
    unfold upperEtaOddChannelApproximationOf
    ring
  calc
    ‖C2.continuedOddDirichletChannel s -
        upperEtaOddChannelApproximationOf etaApprox s‖
        = ‖upperEtaOddChannelTransportFactor s *
            (upperEtaChannel s - etaApprox s)‖ := by
            rw [hidentity, hsub]
    _ = ‖upperEtaOddChannelTransportFactor s‖ *
          ‖upperEtaChannel s - etaApprox s‖ := by
          rw [norm_mul]
    _ ≤ ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s :=
          mul_le_mul_of_nonneg_left heta (norm_nonneg _)

theorem upperEtaOddChannelApproximation_error_le_transport
    (N : ℕ) (etaErrorUpper : ℂ → ℝ) {s : ℂ}
    (hden :
      1 - (2 : ℂ) * C2.complexDirichletCoeff s 2 ≠ 0)
    (heta :
      ‖upperEtaChannel s - upperEtaAlternatingPartial N s‖ ≤ etaErrorUpper s) :
    ‖C2.continuedOddDirichletChannel s -
        upperEtaOddChannelApproximation N s‖ ≤
      ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s := by
  simpa [upperEtaOddChannelApproximation_eq_of_partial] using
    upperEtaOddChannelApproximationOf_error_le_transport
      (upperEtaAlternatingPartial N) etaErrorUpper hden heta

/--
Eta endpoint for an arbitrary eta-side approximation.

This is the preferred audit interface for the remaining approximation work: the
approximant may be an alternating partial sum, a paired/block sum, an
Euler-transformed sum, or a locally certified witness.
-/
theorem RiemannHypothesis_of_upperEtaApproximationTailRelativeBound
    (etaApprox : ℂ → ℂ) (etaErrorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperEtaChannel s - etaApprox s‖ ≤ etaErrorUpper s ∧
          ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s <
            ‖upperEtaOddChannelApproximationOf etaApprox s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOddChannelResolventRelativeError
    (upperEtaOddChannelApproximationOf etaApprox)
    (fun s => ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s)
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · exact Or.inr
          ⟨upperEtaOddChannelApproximationOf_error_le_transport
              etaApprox etaErrorUpper
              (upperEtaOddChannelTransportFactor_den_ne_zero_of_upperOffCriticalStrip hs)
              hbulk.1,
            hbulk.2⟩)

/-! #### Paired eta approximation -/

/-- One cancellation pair in the eta series:
`(2k+1)^{-s} - (2k+2)^{-s}`. -/
noncomputable def upperEtaPairedTerm (k : ℕ) (s : ℂ) : ℂ :=
  C2.complexDirichletCoeff s (2 * k + 1) -
    C2.complexDirichletCoeff s (2 * k + 2)

/-- Logarithmic step between adjacent entries in one eta cancellation pair. -/
noncomputable def upperEtaPairLogStep (k : ℕ) : ℝ :=
  Real.log (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ))

theorem upperEtaPairLogStep_pos (k : ℕ) :
    0 < upperEtaPairLogStep k := by
  unfold upperEtaPairLogStep
  have ha_pos : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  have hlt : (((2 * k + 1 : ℕ) : ℝ)) < (((2 * k + 2 : ℕ) : ℝ)) := by
    norm_num
  have hratio : 1 < (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) := by
    rw [one_lt_div ha_pos]
    exact hlt
  exact Real.log_pos hratio

theorem upperEtaPairLogStep_nonneg (k : ℕ) :
    0 ≤ upperEtaPairLogStep k :=
  le_of_lt (upperEtaPairLogStep_pos k)

theorem upperEtaPairLogStep_le_inv_odd (k : ℕ) :
    upperEtaPairLogStep k ≤ 1 / (((2 * k + 1 : ℕ) : ℝ)) := by
  unfold upperEtaPairLogStep
  have ha_pos : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  have hb_pos : 0 < (((2 * k + 2 : ℕ) : ℝ)) := by positivity
  have hratio_pos :
      0 < (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) :=
    div_pos hb_pos ha_pos
  calc
    Real.log (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ))
        ≤ ((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
    _ = 1 / (((2 * k + 1 : ℕ) : ℝ)) := by
          field_simp [ha_pos.ne']
          norm_num

theorem complexDirichletCoeff_pair_succ_eq_mul_exp_step
    (k : ℕ) (s : ℂ) :
    C2.complexDirichletCoeff s (2 * k + 2) =
      C2.complexDirichletCoeff s (2 * k + 1) *
        Complex.exp (-(s * (upperEtaPairLogStep k : ℂ))) := by
  unfold C2.complexDirichletCoeff upperEtaPairLogStep
  have ha_ne : (((2 * k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hb_ne : (((2 * k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hlog :
      Real.log ((2 * k + 2 : ℕ) : ℝ) =
        Real.log ((2 * k + 1 : ℕ) : ℝ) +
          Real.log (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hb_ne ha_ne]
    ring
  rw [← Complex.exp_add]
  congr 1
  rw [hlog]
  simp only [Complex.ofReal_add]
  ring

theorem upperEtaPairedTerm_eq_coeff_mul_exp_step (k : ℕ) (s : ℂ) :
    upperEtaPairedTerm k s =
      C2.complexDirichletCoeff s (2 * k + 1) *
        (1 - Complex.exp (-(s * (upperEtaPairLogStep k : ℂ)))) := by
  unfold upperEtaPairedTerm
  rw [complexDirichletCoeff_pair_succ_eq_mul_exp_step k s]
  ring

theorem upperEtaPairedTerm_norm_le_expStep
    (k : ℕ) (s : ℂ)
    (hsmall : ‖s * (upperEtaPairLogStep k : ℂ)‖ ≤ 1) :
    ‖upperEtaPairedTerm k s‖ ≤
      2 * ‖C2.complexDirichletCoeff s (2 * k + 1)‖ *
        ‖s * (upperEtaPairLogStep k : ℂ)‖ := by
  let x : ℂ := s * (upperEtaPairLogStep k : ℂ)
  have hsmall' : ‖-x‖ ≤ 1 := by simpa [x] using hsmall
  have hexp : ‖Complex.exp (-x) - 1‖ ≤ 2 * ‖x‖ :=
    (Complex.norm_exp_sub_one_le hsmall').trans_eq (by simp [x])
  calc
    ‖upperEtaPairedTerm k s‖
        = ‖C2.complexDirichletCoeff s (2 * k + 1) *
            (1 - Complex.exp (-x))‖ := by
            rw [upperEtaPairedTerm_eq_coeff_mul_exp_step]
    _ = ‖C2.complexDirichletCoeff s (2 * k + 1)‖ *
          ‖Complex.exp (-x) - 1‖ := by
          rw [norm_mul]
          congr 1
          rw [← norm_neg]
          ring_nf
    _ ≤ ‖C2.complexDirichletCoeff s (2 * k + 1)‖ * (2 * ‖x‖) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = 2 * ‖C2.complexDirichletCoeff s (2 * k + 1)‖ *
          ‖s * (upperEtaPairLogStep k : ℂ)‖ := by
          simp [x]
          ring

theorem upperEtaPairedTerm_norm_le_expStep_real
    (k : ℕ) (s : ℂ)
    (hsmall : ‖s * (upperEtaPairLogStep k : ℂ)‖ ≤ 1) :
    ‖upperEtaPairedTerm k s‖ ≤
      2 * ‖s‖ * upperEtaPairLogStep k *
        (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hbase := upperEtaPairedTerm_norm_le_expStep k s hsmall
  have hcoeff :
      ‖C2.complexDirichletCoeff s (2 * k + 1)‖ =
        (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) :=
    C2.complexDirichletCoeff_norm_eq_rpow_neg_re s (by omega)
  have hstep_nonneg : 0 ≤ upperEtaPairLogStep k :=
    upperEtaPairLogStep_nonneg k
  have hstep_norm :
      ‖s * (upperEtaPairLogStep k : ℂ)‖ =
        ‖s‖ * upperEtaPairLogStep k := by
    rw [norm_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg hstep_nonneg]
  calc
    ‖upperEtaPairedTerm k s‖
        ≤ 2 * ‖C2.complexDirichletCoeff s (2 * k + 1)‖ *
            ‖s * (upperEtaPairLogStep k : ℂ)‖ := hbase
    _ = 2 * ‖s‖ * upperEtaPairLogStep k *
          (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
          rw [hcoeff, hstep_norm]
          ring

theorem upperEtaPairedTerm_norm_le_invStep_real
    (k : ℕ) (s : ℂ)
    (hsmall : ‖s * (upperEtaPairLogStep k : ℂ)‖ ≤ 1) :
    ‖upperEtaPairedTerm k s‖ ≤
      2 * ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) *
        (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hterm := upperEtaPairedTerm_norm_le_expStep_real k s hsmall
  have hlog := upperEtaPairLogStep_le_inv_odd k
  calc
    ‖upperEtaPairedTerm k s‖
        ≤ 2 * ‖s‖ * upperEtaPairLogStep k *
            (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := hterm
    _ ≤ 2 * ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) *
          (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
          gcongr

theorem upperEtaPairLogStep_small_of_norm_le_odd
    (k : ℕ) (s : ℂ)
    (hsle : ‖s‖ ≤ (((2 * k + 1 : ℕ) : ℝ))) :
    ‖s * (upperEtaPairLogStep k : ℂ)‖ ≤ 1 := by
  have ha_pos : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  have hstep_nonneg : 0 ≤ upperEtaPairLogStep k :=
    upperEtaPairLogStep_nonneg k
  have hstep_norm :
      ‖s * (upperEtaPairLogStep k : ℂ)‖ =
        ‖s‖ * upperEtaPairLogStep k := by
    rw [norm_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg hstep_nonneg]
  have hlog := upperEtaPairLogStep_le_inv_odd k
  have hdiv : ‖s‖ / (((2 * k + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ ha_pos]
    simpa using hsle
  calc
    ‖s * (upperEtaPairLogStep k : ℂ)‖
        = ‖s‖ * upperEtaPairLogStep k := hstep_norm
    _ ≤ ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) := by
          gcongr
    _ = ‖s‖ / (((2 * k + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 1 := hdiv

theorem upperEtaPairedTerm_norm_le_invStep_real_of_norm_le_odd
    (k : ℕ) (s : ℂ)
    (hsle : ‖s‖ ≤ (((2 * k + 1 : ℕ) : ℝ))) :
    ‖upperEtaPairedTerm k s‖ ≤
      2 * ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) *
        (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) :=
  upperEtaPairedTerm_norm_le_invStep_real k s
    (upperEtaPairLogStep_small_of_norm_le_odd k s hsle)

/-- Real `p`-series majorant for the paired eta tail starting at pair `P`. -/
noncomputable def upperEtaPairedTailMajorant (P : ℕ) (s : ℂ) (j : ℕ) : ℝ :=
  2 * ‖s‖ * (((2 * (P + j) + 1 : ℕ) : ℝ) ^ ((-1 : ℝ) + (-s.re)))

theorem upperEtaPairedTailMajorant_eq_neg_re_add_one
    (P : ℕ) (s : ℂ) (j : ℕ) :
    upperEtaPairedTailMajorant P s j =
      2 * ‖s‖ * (((2 * (P + j) + 1 : ℕ) : ℝ) ^ (-(s.re + 1))) := by
  unfold upperEtaPairedTailMajorant
  congr 2
  ring

theorem upperEtaPairedTerm_norm_le_rpowMajorant_of_norm_le_odd
    (k : ℕ) (s : ℂ)
    (hsle : ‖s‖ ≤ (((2 * k + 1 : ℕ) : ℝ))) :
    ‖upperEtaPairedTerm k s‖ ≤
      2 * ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ ((-1 : ℝ) + (-s.re))) := by
  have hterm := upperEtaPairedTerm_norm_le_invStep_real_of_norm_le_odd k s hsle
  let a : ℝ := (((2 * k + 1 : ℕ) : ℝ))
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hcombine : (1 / a) * a ^ (-s.re) = a ^ ((-1 : ℝ) + (-s.re)) := by
    calc
      (1 / a) * a ^ (-s.re)
          = a ^ (-1 : ℝ) * a ^ (-s.re) := by
              rw [Real.rpow_neg_one, one_div]
      _ = a ^ ((-1 : ℝ) + (-s.re)) := by
              rw [← Real.rpow_add ha_pos]
  calc
    ‖upperEtaPairedTerm k s‖
        ≤ 2 * ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) *
            (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re)) := hterm
    _ = 2 * ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ ((-1 : ℝ) + (-s.re))) := by
          dsimp [a] at hcombine
          calc
            2 * ‖s‖ * (1 / (((2 * k + 1 : ℕ) : ℝ))) *
                (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re))
                = 2 * ‖s‖ *
                    ((1 / (((2 * k + 1 : ℕ) : ℝ))) *
                      (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re))) := by ring
            _ = 2 * ‖s‖ *
                  (((2 * k + 1 : ℕ) : ℝ) ^ ((-1 : ℝ) + (-s.re))) := by
                rw [hcombine]

theorem upperEtaPairedTailTerm_norm_le_majorant
    (P : ℕ) (s : ℂ)
    (hcut : ‖s‖ ≤ (((2 * P + 1 : ℕ) : ℝ))) :
    ∀ j : ℕ,
      ‖upperEtaPairedTerm (P + j) s‖ ≤ upperEtaPairedTailMajorant P s j := by
  intro j
  have hmono : (((2 * P + 1 : ℕ) : ℝ)) ≤
      (((2 * (P + j) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 2 * P + 1 ≤ 2 * (P + j) + 1)
  simpa [upperEtaPairedTailMajorant] using
    upperEtaPairedTerm_norm_le_rpowMajorant_of_norm_le_odd (P + j) s
      (le_trans hcut hmono)

theorem upperEtaPairedTailMajorant_summable
    (P : ℕ) {s : ℂ} (hsre : 0 < s.re) :
    Summable (upperEtaPairedTailMajorant P s) := by
  have hp : (-1 : ℝ) + (-s.re) < -1 := by linarith
  have hsumm : Summable (fun n : ℕ => ((n : ℝ) ^ ((-1 : ℝ) + (-s.re)))) :=
    (Real.summable_nat_rpow).2 hp
  have hinj : Function.Injective (fun j : ℕ => 2 * (P + j) + 1) := by
    intro i j hij
    have hmul : 2 * (P + i) = 2 * (P + j) := Nat.succ.inj hij
    have hadd : P + i = P + j := Nat.mul_left_cancel (by decide : 0 < 2) hmul
    exact Nat.add_left_cancel hadd
  exact (Summable.mul_left (2 * ‖s‖) (hsumm.comp_injective hinj)).congr (fun j => by
    simp [upperEtaPairedTailMajorant, Nat.cast_add, Nat.cast_mul])

theorem upperEtaPairedTail_tsum_norm_le_majorant_tsum
    (P : ℕ) {s : ℂ} (hsre : 0 < s.re)
    (hcut : ‖s‖ ≤ (((2 * P + 1 : ℕ) : ℝ))) :
    ‖∑' j : ℕ, upperEtaPairedTerm (P + j) s‖ ≤
      ∑' j : ℕ, upperEtaPairedTailMajorant P s j := by
  exact tsum_of_norm_bounded
    (upperEtaPairedTailMajorant_summable P hsre).hasSum
    (upperEtaPairedTailTerm_norm_le_majorant P s hcut)

/-- Canonical paired eta cutoff: large enough to make each tail log-step small. -/
noncomputable def upperEtaNormPairCutoff (s : ℂ) : ℕ :=
  Nat.ceil ‖s‖

theorem upperEtaNormPairCutoff_spec (s : ℂ) :
    ‖s‖ ≤ (((2 * upperEtaNormPairCutoff s + 1 : ℕ) : ℝ)) := by
  have hceil : ‖s‖ ≤ ((upperEtaNormPairCutoff s : ℕ) : ℝ) := by
    unfold upperEtaNormPairCutoff
    exact Nat.le_ceil ‖s‖
  have hmono : ((upperEtaNormPairCutoff s : ℕ) : ℝ) ≤
      (((2 * upperEtaNormPairCutoff s + 1 : ℕ) : ℝ)) := by
    exact_mod_cast
      (by omega : upperEtaNormPairCutoff s ≤ 2 * upperEtaNormPairCutoff s + 1)
  exact le_trans hceil hmono

/-- Infinite paired eta sum. -/
noncomputable def upperEtaPairedInfinite (s : ℂ) : ℂ :=
  ∑' k : ℕ, upperEtaPairedTerm k s

/--
Compact-local `p`-series majorant for the paired eta terms.

On a compact set with `‖s‖ ≤ B` and `δ ≤ Re(s)`, all sufficiently far pairs are
bounded by this summable sequence.
-/
noncomputable def upperEtaPairedCompactMajorant (B δ : ℝ) (k : ℕ) : ℝ :=
  2 * B * (((2 * k + 1 : ℕ) : ℝ) ^ ((-1 : ℝ) + (-δ)))

theorem upperEtaPairedCompactMajorant_summable
    (B δ : ℝ) (hδ : 0 < δ) :
    Summable (upperEtaPairedCompactMajorant B δ) := by
  have hp : (-1 : ℝ) + (-δ) < -1 := by linarith
  have hsumm : Summable (fun n : ℕ => ((n : ℝ) ^ ((-1 : ℝ) + (-δ)))) :=
    (Real.summable_nat_rpow).2 hp
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    have hmul : 2 * i = 2 * j := Nat.succ.inj hij
    exact Nat.mul_left_cancel (by decide : 0 < 2) hmul
  exact (Summable.mul_left (2 * B) (hsumm.comp_injective hinj)).congr (fun k => by
    simp [upperEtaPairedCompactMajorant, Nat.cast_add, Nat.cast_mul])

theorem upperEtaPairedTerm_norm_le_compactMajorant_of_bounds
    (B δ : ℝ) (k : ℕ) (s : ℂ)
    (hsnorm : ‖s‖ ≤ B)
    (hsre : δ ≤ s.re)
    (hBcut : B ≤ (((2 * k + 1 : ℕ) : ℝ))) :
    ‖upperEtaPairedTerm k s‖ ≤ upperEtaPairedCompactMajorant B δ k := by
  have hnorm_le_odd : ‖s‖ ≤ (((2 * k + 1 : ℕ) : ℝ)) := le_trans hsnorm hBcut
  have hterm := upperEtaPairedTerm_norm_le_rpowMajorant_of_norm_le_odd k s hnorm_le_odd
  let a : ℝ := (((2 * k + 1 : ℕ) : ℝ))
  have ha_one : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  have hpow : a ^ ((-1 : ℝ) + (-s.re)) ≤ a ^ ((-1 : ℝ) + (-δ)) := by
    exact Real.rpow_le_rpow_of_exponent_le ha_one (by linarith)
  have hcoef : 2 * ‖s‖ ≤ 2 * B := by nlinarith [hsnorm]
  have hcoef_nonneg : 0 ≤ 2 * B := by nlinarith [norm_nonneg s, hsnorm]
  have hpow_nonneg : 0 ≤ a ^ ((-1 : ℝ) + (-s.re)) :=
    Real.rpow_nonneg (by positivity) _
  have hmajor : 2 * ‖s‖ * a ^ ((-1 : ℝ) + (-s.re)) ≤
      2 * B * a ^ ((-1 : ℝ) + (-δ)) := by
    exact mul_le_mul hcoef hpow hpow_nonneg hcoef_nonneg
  exact hterm.trans (by simpa [upperEtaPairedCompactMajorant, a] using hmajor)

theorem upperEtaPairedTerm_summableLocallyUniformlyOn_punctured :
    SummableLocallyUniformlyOn
      (fun k : ℕ => fun s : ℂ => upperEtaPairedTerm k s)
      C2.puncturedOpenRightHalfPlane := by
  refine SummableLocallyUniformlyOn.of_locally_bounded_eventually
    C2.puncturedOpenRightHalfPlane_isOpen ?_
  intro K hKsubset hKcompact
  rcases Set.eq_empty_or_nonempty K with hKempty | hKnonempty
  · refine ⟨fun _ : ℕ => (0 : ℝ), summable_zero, ?_⟩
    rw [Nat.cofinite_eq_atTop]
    exact Filter.Eventually.of_forall (fun _ z hz => by
      rw [hKempty] at hz
      cases hz)
  · have hbounded : Bornology.IsBounded K :=
      (Metric.isCompact_iff_isClosed_bounded.mp hKcompact).2
    obtain ⟨B, _hBpos, hBbound⟩ := hbounded.exists_pos_norm_le
    obtain ⟨z0, hz0, hmin⟩ :=
      hKcompact.exists_isMinOn hKnonempty (Complex.continuous_re.continuousOn)
    have hz0_punct : z0 ∈ C2.puncturedOpenRightHalfPlane := hKsubset hz0
    have hδpos : 0 < z0.re := by
      simpa [C2.puncturedOpenRightHalfPlane] using hz0_punct.1
    refine ⟨upperEtaPairedCompactMajorant B z0.re,
      upperEtaPairedCompactMajorant_summable B z0.re hδpos, ?_⟩
    rw [Nat.cofinite_eq_atTop]
    refine Filter.eventually_atTop.mpr ⟨Nat.ceil B, ?_⟩
    intro n hn z hz
    have hBcut : B ≤ (((2 * n + 1 : ℕ) : ℝ)) := by
      have hB_le_ceil : B ≤ ((Nat.ceil B : ℕ) : ℝ) := Nat.le_ceil B
      have hceil_le_n : ((Nat.ceil B : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn_le_odd : (n : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (by omega : n ≤ 2 * n + 1)
      exact le_trans (le_trans hB_le_ceil hceil_le_n) hn_le_odd
    exact upperEtaPairedTerm_norm_le_compactMajorant_of_bounds
      B z0.re n z (hBbound z hz) (hmin hz) hBcut

theorem upperEtaPairedTerm_differentiableAt (n : ℕ) (z : ℂ) :
    DifferentiableAt ℂ (fun s => upperEtaPairedTerm n s) z := by
  have h1 : AnalyticAt ℂ (fun s => C2.complexDirichletCoeff s (2 * n + 1)) z :=
    (C2.complexDirichletCoeff_analyticOnNhd (2 * n + 1) Set.univ) z trivial
  have h2 : AnalyticAt ℂ (fun s => C2.complexDirichletCoeff s (2 * n + 2)) z :=
    (C2.complexDirichletCoeff_analyticOnNhd (2 * n + 2) Set.univ) z trivial
  simpa [upperEtaPairedTerm] using h1.differentiableAt.sub h2.differentiableAt

theorem upperEtaPairedInfinite_analyticOnNhd_punctured_of_summableLocallyUniformly
    (hlocal : SummableLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => upperEtaPairedTerm n s)
      C2.puncturedOpenRightHalfPlane) :
    AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane := by
  have hdiff :
      DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, upperEtaPairedTerm n s)
        C2.puncturedOpenRightHalfPlane :=
    SummableLocallyUniformlyOn.differentiableOn
      C2.puncturedOpenRightHalfPlane_isOpen hlocal
      (fun n r _hr => upperEtaPairedTerm_differentiableAt n r)
  simpa [upperEtaPairedInfinite] using
    hdiff.analyticOnNhd C2.puncturedOpenRightHalfPlane_isOpen

theorem upperEtaPairedInfinite_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane :=
  upperEtaPairedInfinite_analyticOnNhd_punctured_of_summableLocallyUniformly
    upperEtaPairedTerm_summableLocallyUniformlyOn_punctured

theorem upperEtaPairedTerm_summable_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    Summable fun k : ℕ => upperEtaPairedTerm k s := by
  let f : ℕ → ℂ := fun n => C2.complexDirichletCoeff s (n + 1)
  have hf : Summable f := C2.summable_positiveDirichletCoeff_of_one_lt_re s hs
  have hodd0 : Summable fun k : ℕ => f (2 * k) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a = 2 * b := by simpa using h
      exact Nat.mul_left_cancel (by decide : 0 < 2) h')
  have heven0 : Summable fun k : ℕ => f (2 * k + 1) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a + 1 = 2 * b + 1 := by simpa using h
      have hmul : 2 * a = 2 * b := Nat.succ.inj h'
      exact Nat.mul_left_cancel (by decide : 0 < 2) hmul)
  have hodd : Summable fun k : ℕ => C2.complexDirichletCoeff s (2 * k + 1) := by
    simpa [f] using hodd0
  have heven : Summable fun k : ℕ => C2.complexDirichletCoeff s (2 * k + 2) := by
    simpa [f] using heven0
  simpa [upperEtaPairedTerm] using hodd.sub heven

theorem upperEtaPairedTerm_summable_of_re_pos
    (s : ℂ) (hsre : 0 < s.re) :
    Summable fun k : ℕ => upperEtaPairedTerm k s := by
  let P : ℕ := upperEtaNormPairCutoff s
  have hcut : ‖s‖ ≤ (((2 * P + 1 : ℕ) : ℝ)) := by
    simpa [P] using upperEtaNormPairCutoff_spec s
  have htail : Summable fun j : ℕ => upperEtaPairedTerm (P + j) s :=
    Summable.of_norm_bounded
      (upperEtaPairedTailMajorant_summable P hsre)
      (upperEtaPairedTailTerm_norm_le_majorant P s hcut)
  have htail' : Summable fun j : ℕ => upperEtaPairedTerm (j + P) s :=
    htail.congr (fun j => by rw [Nat.add_comm])
  exact (summable_nat_add_iff P).mp htail'

theorem upperEtaPairedInfinite_eq_upperEtaChannel_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    upperEtaPairedInfinite s = upperEtaChannel s := by
  let f : ℕ → ℂ := fun n => C2.complexDirichletCoeff s (n + 1)
  have hf : Summable f := C2.summable_positiveDirichletCoeff_of_one_lt_re s hs
  have hodd0 : Summable fun k : ℕ => f (2 * k) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a = 2 * b := by simpa using h
      exact Nat.mul_left_cancel (by decide : 0 < 2) h')
  have heven0 : Summable fun k : ℕ => f (2 * k + 1) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a + 1 = 2 * b + 1 := by simpa using h
      have hmul : 2 * a = 2 * b := Nat.succ.inj h'
      exact Nat.mul_left_cancel (by decide : 0 < 2) hmul)
  have hodd : Summable fun k : ℕ => C2.complexDirichletCoeff s (2 * k + 1) := by
    simpa [f] using hodd0
  have heven : Summable fun k : ℕ => C2.complexDirichletCoeff s (2 * k + 2) := by
    simpa [f] using heven0
  have hpaired_tsum :
      upperEtaPairedInfinite s = C2.oddDirichletChannel s - C2.evenDirichletChannel s := by
    unfold upperEtaPairedInfinite upperEtaPairedTerm
      C2.oddDirichletChannel C2.evenDirichletChannel
    rw [hodd.tsum_sub heven]
    congr 1
  have hodd_euler := C2.oddDirichletChannel_eulerRelation_of_one_lt_re s hs
  have hpos := C2.positiveDirichletChannel_eq_riemannZeta s hs
  have heven_euler := C2.evenDirichletChannel_eq_coeff_two_mul_positive s
  unfold upperEtaChannel
  rw [hpaired_tsum, hodd_euler, heven_euler, hpos]
  ring

theorem upperEtaChannel_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ upperEtaChannel C2.puncturedOpenRightHalfPlane := by
  unfold upperEtaChannel
  exact
    ((analyticOnNhd_const.sub
      ((C2.complexDirichletCoeff_analyticOnNhd 2 C2.puncturedOpenRightHalfPlane).const_smul
        (c := (2 : ℂ)))).mul
      C2.riemannZeta_analyticOnNhd_punctured)

theorem upperEtaPairedInfinite_eq_upperEtaChannel_on_punctured_of_analyticOnNhd
    (hpaired : AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane) :
    ∀ s : ℂ, s ∈ C2.puncturedOpenRightHalfPlane →
      upperEtaPairedInfinite s = upperEtaChannel s := by
  exact
    (C2.ComparisonFromOneLtPuncturedData.of_analyticOnNhd_punctured
      hpaired upperEtaChannel_analyticOnNhd_punctured).eqOnPuncturedOpenRightHalfPlane
      (fun s hs => upperEtaPairedInfinite_eq_upperEtaChannel_of_one_lt_re s hs)

theorem upperEtaPairedInfinite_eq_upperEtaChannel_on_punctured :
    ∀ s : ℂ, s ∈ C2.puncturedOpenRightHalfPlane →
      upperEtaPairedInfinite s = upperEtaChannel s :=
  upperEtaPairedInfinite_eq_upperEtaChannel_on_punctured_of_analyticOnNhd
    upperEtaPairedInfinite_analyticOnNhd_punctured

/-- Paired eta partial sum through `P` cancellation pairs. -/
noncomputable def upperEtaPairedPartial (P : ℕ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range P) (fun k => upperEtaPairedTerm k s)

theorem upperEtaPaired_tailIdentity_of_one_lt_re
    (P : ℕ) (s : ℂ) (hs : 1 < s.re) :
    upperEtaChannel s - upperEtaPairedPartial P s =
      ∑' j : ℕ, upperEtaPairedTerm (P + j) s := by
  have hsumm := upperEtaPairedTerm_summable_of_one_lt_re s hs
  have hsplit := hsumm.sum_add_tsum_nat_add P
  have hinf := upperEtaPairedInfinite_eq_upperEtaChannel_of_one_lt_re s hs
  have htail_comm :
      (∑' j : ℕ, upperEtaPairedTerm (j + P) s) =
        ∑' j : ℕ, upperEtaPairedTerm (P + j) s := by
    apply tsum_congr
    intro j
    rw [Nat.add_comm]
  unfold upperEtaPairedPartial
  calc
    upperEtaChannel s - Finset.sum (Finset.range P) (fun k => upperEtaPairedTerm k s)
        = upperEtaPairedInfinite s -
            Finset.sum (Finset.range P) (fun k => upperEtaPairedTerm k s) := by
            rw [← hinf]
    _ = (∑' k : ℕ, upperEtaPairedTerm k s) -
          Finset.sum (Finset.range P) (fun k => upperEtaPairedTerm k s) := rfl
    _ = ∑' j : ℕ, upperEtaPairedTerm (P + j) s := by
        rw [← htail_comm]
        rw [← hsplit]
        ring

theorem upperEtaAlternatingPartial_two_mul_eq_paired (P : ℕ) (s : ℂ) :
    upperEtaAlternatingPartial (2 * P) s = upperEtaPairedPartial P s := by
  induction P with
  | zero =>
      simp [upperEtaAlternatingPartial, upperEtaPairedPartial]
  | succ P ih =>
      have heven : (-1 : ℂ) ^ (2 * P) = 1 := by
        rw [pow_mul]
        norm_num
      have hodd : (-1 : ℂ) ^ (2 * P + 1) = -1 := by
        rw [show 2 * P + 1 = Nat.succ (2 * P) by omega, pow_succ, heven]
        norm_num
      have hstep :
          upperEtaAlternatingPartial (2 * (P + 1)) s =
            upperEtaAlternatingPartial (2 * P) s + upperEtaPairedTerm P s := by
        unfold upperEtaAlternatingPartial upperEtaPairedTerm
        rw [show 2 * (P + 1) = 2 * P + 2 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp [heven, hodd]
        ring
      calc
        upperEtaAlternatingPartial (2 * (P + 1)) s
            = upperEtaAlternatingPartial (2 * P) s + upperEtaPairedTerm P s := hstep
        _ = upperEtaPairedPartial P s + upperEtaPairedTerm P s := by rw [ih]
        _ = upperEtaPairedPartial (P + 1) s := by
            unfold upperEtaPairedPartial
            rw [Finset.sum_range_succ]

/-- Odd-channel approximation obtained from the paired eta partial sum. -/
noncomputable def upperEtaPairedOddChannelApproximation (P : ℕ) : ℂ → ℂ :=
  upperEtaOddChannelApproximationOf (upperEtaPairedPartial P)

/-- Paired eta partial sum with a point-dependent cutoff. -/
noncomputable def upperEtaPairedPartialBy (P : ℂ → ℕ) (s : ℂ) : ℂ :=
  upperEtaPairedPartial (P s) s

/-- Odd-channel approximation obtained from a point-dependent paired cutoff. -/
noncomputable def upperEtaPairedOddChannelApproximationBy (P : ℂ → ℕ) : ℂ → ℂ :=
  upperEtaOddChannelApproximationOf (upperEtaPairedPartialBy P)

theorem upperEtaPaired_tailIdentityBy_of_analyticOnNhd_punctured
    (P : ℂ → ℕ)
    (hpaired : AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane) :
    ∀ s : ℂ, upperOffCriticalStrip s →
      upperEtaChannel s - upperEtaPairedPartialBy P s =
        ∑' j : ℕ, upperEtaPairedTerm (P s + j) s := by
  intro s hs
  have hsPunct : s ∈ C2.puncturedOpenRightHalfPlane := by
    refine ⟨by linarith [hs.1], ?_⟩
    intro h
    have hsre_one : s.re = 1 := by simp [h]
    linarith [hs.2]
  have hsre : 0 < s.re := by linarith [hs.1]
  have hsumm := upperEtaPairedTerm_summable_of_re_pos s hsre
  have hsplit := hsumm.sum_add_tsum_nat_add (P s)
  have hinf := upperEtaPairedInfinite_eq_upperEtaChannel_on_punctured_of_analyticOnNhd
    hpaired s hsPunct
  have htail_comm :
      (∑' j : ℕ, upperEtaPairedTerm (j + P s) s) =
        ∑' j : ℕ, upperEtaPairedTerm (P s + j) s := by
    apply tsum_congr
    intro j
    rw [Nat.add_comm]
  unfold upperEtaPairedPartialBy upperEtaPairedPartial
  calc
    upperEtaChannel s - Finset.sum (Finset.range (P s)) (fun k => upperEtaPairedTerm k s)
        = upperEtaPairedInfinite s -
            Finset.sum (Finset.range (P s)) (fun k => upperEtaPairedTerm k s) := by
            rw [← hinf]
    _ = (∑' k : ℕ, upperEtaPairedTerm k s) -
          Finset.sum (Finset.range (P s)) (fun k => upperEtaPairedTerm k s) := rfl
    _ = ∑' j : ℕ, upperEtaPairedTerm (P s + j) s := by
        rw [← htail_comm]
        rw [← hsplit]
        ring

theorem upperEtaPaired_normCutoff_tailIdentity_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    upperEtaChannel s - upperEtaPairedPartialBy upperEtaNormPairCutoff s =
      ∑' j : ℕ, upperEtaPairedTerm (upperEtaNormPairCutoff s + j) s := by
  simpa [upperEtaPairedPartialBy] using
    upperEtaPaired_tailIdentity_of_one_lt_re (upperEtaNormPairCutoff s) s hs

theorem upperEtaPaired_tailIdentityBy
    (P : ℂ → ℕ) :
    ∀ s : ℂ, upperOffCriticalStrip s →
      upperEtaChannel s - upperEtaPairedPartialBy P s =
        ∑' j : ℕ, upperEtaPairedTerm (P s + j) s :=
  upperEtaPaired_tailIdentityBy_of_analyticOnNhd_punctured P
    upperEtaPairedInfinite_analyticOnNhd_punctured

theorem upperEtaPaired_normCutoff_tailIdentity :
    ∀ s : ℂ, upperOffCriticalStrip s →
      upperEtaChannel s - upperEtaPairedPartialBy upperEtaNormPairCutoff s =
        ∑' j : ℕ, upperEtaPairedTerm (upperEtaNormPairCutoff s + j) s :=
  upperEtaPaired_tailIdentityBy upperEtaNormPairCutoff

/--
Endpoint for the paired eta approximation.

The remaining analytic obligation is now a bound for the paired eta tail
`upperEtaChannel - upperEtaPairedPartial P`; this is the natural next target for
summation-by-parts or mean-value estimates.
-/
theorem RiemannHypothesis_of_upperEtaPairedTailRelativeBound
    (P : ℕ) (etaPairErrorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperEtaChannel s - upperEtaPairedPartial P s‖ ≤
            etaPairErrorUpper s ∧
          ‖upperEtaOddChannelTransportFactor s‖ * etaPairErrorUpper s <
            ‖upperEtaPairedOddChannelApproximation P s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaApproximationTailRelativeBound
    (upperEtaPairedPartial P) etaPairErrorUpper
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · exact Or.inr
          ⟨hbulk.1, by
            simpa [upperEtaPairedOddChannelApproximation] using hbulk.2⟩)

/--
Variable-cutoff paired eta endpoint with the paired-tail `p`-series majorant.

Here `Z(s)` is the transported paired eta partial with cutoff `P s`.  The
formal tail bound below follows from the paired tail identity, the termwise
logarithmic-step estimate, and `p`-series summability.
-/
theorem RiemannHypothesis_of_upperEtaPairedVariableTsumMajorantRelativeBound
    (P : ℂ → ℕ)
    (tailIdentity : ∀ s : ℂ, upperOffCriticalStrip s →
      upperEtaChannel s - upperEtaPairedPartialBy P s =
        ∑' j : ℕ, upperEtaPairedTerm (P s + j) s)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖s‖ ≤ (((2 * P s + 1 : ℕ) : ℝ)) ∧
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (P s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy P s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaApproximationTailRelativeBound
    (upperEtaPairedPartialBy P)
    (fun s => ∑' j : ℕ, upperEtaPairedTailMajorant (P s) s j)
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · rcases hbulk with ⟨hcut, hrelative⟩
        have hsre : 0 < s.re := by linarith [hs.1]
        have htail := upperEtaPairedTail_tsum_norm_le_majorant_tsum
          (P s) hsre hcut
        exact Or.inr
          ⟨by
            calc
              ‖upperEtaChannel s - upperEtaPairedPartialBy P s‖
                  = ‖∑' j : ℕ, upperEtaPairedTerm (P s + j) s‖ := by
                      rw [tailIdentity s hs]
              _ ≤ ∑' j : ℕ, upperEtaPairedTailMajorant (P s) s j := htail,
            by simpa [upperEtaPairedOddChannelApproximationBy] using hrelative⟩)

/--
Norm-cutoff paired eta endpoint.

This fixes the cutoff to `P(s) = ceil ‖s‖`, so the small-log-step condition is
proved internally.  The only remaining global obligation is the relative
dominance inequality outside the canonical near-axis region.
-/
theorem RiemannHypothesis_of_upperEtaPairedNormCutoffTsumMajorantRelativeBound
    (tailIdentity : ∀ s : ℂ, upperOffCriticalStrip s →
      upperEtaChannel s - upperEtaPairedPartialBy upperEtaNormPairCutoff s =
        ∑' j : ℕ, upperEtaPairedTerm (upperEtaNormPairCutoff s + j) s)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (upperEtaNormPairCutoff s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy upperEtaNormPairCutoff s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaPairedVariableTsumMajorantRelativeBound
    upperEtaNormPairCutoff tailIdentity
    (fun s hs => by
      rcases cover s hs with hnear | hrelative
      · exact Or.inl hnear
      · exact Or.inr ⟨upperEtaNormPairCutoff_spec s, hrelative⟩)

/--
Variable-cutoff paired eta endpoint with analytic continuation of the paired
tail identity.

The tail identity on the upper strip is derived from the absolute-half-plane
equality `upperEtaPairedInfinite = upperEtaChannel`, the identity theorem on
the punctured right half-plane, and paired-tail summability for `0 < Re(s)`.
-/
theorem RiemannHypothesis_of_upperEtaPairedVariableAnalyticTsumMajorantRelativeBound
    (P : ℂ → ℕ)
    (hpaired : AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖s‖ ≤ (((2 * P s + 1 : ℕ) : ℝ)) ∧
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (P s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy P s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaPairedVariableTsumMajorantRelativeBound
    P
    (upperEtaPaired_tailIdentityBy_of_analyticOnNhd_punctured P hpaired)
    cover

/--
Norm-cutoff paired eta endpoint with analytic continuation of the paired tail
identity.  After this reduction, the only remaining bulk inequality is the
displayed relative dominance condition.
-/
theorem RiemannHypothesis_of_upperEtaPairedNormCutoffAnalyticTsumMajorantRelativeBound
    (hpaired : AnalyticOnNhd ℂ upperEtaPairedInfinite C2.puncturedOpenRightHalfPlane)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (upperEtaNormPairCutoff s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy upperEtaNormPairCutoff s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaPairedNormCutoffTsumMajorantRelativeBound
    (upperEtaPaired_tailIdentityBy_of_analyticOnNhd_punctured
      upperEtaNormPairCutoff hpaired)
    cover

theorem RiemannHypothesis_of_upperEtaPairedVariableClosedTsumMajorantRelativeBound
    (P : ℂ → ℕ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖s‖ ≤ (((2 * P s + 1 : ℕ) : ℝ)) ∧
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (P s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy P s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaPairedVariableTsumMajorantRelativeBound
    P (upperEtaPaired_tailIdentityBy P) cover

theorem RiemannHypothesis_of_upperEtaPairedNormCutoffClosedTsumMajorantRelativeBound
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
          ‖upperEtaOddChannelTransportFactor s‖ *
              (∑' j : ℕ, upperEtaPairedTailMajorant (upperEtaNormPairCutoff s) s j) <
            ‖upperEtaPairedOddChannelApproximationBy upperEtaNormPairCutoff s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaPairedNormCutoffTsumMajorantRelativeBound
    upperEtaPaired_normCutoff_tailIdentity cover

/--
Eta-specialized full-resolvent endpoint.

To close the remaining bulk bound with this choice of `Z`, it is enough to prove
the certified eta approximation error and the scalar dominance inequality below
outside the canonical near-axis region.
-/
theorem RiemannHypothesis_of_upperEtaOddChannelApproximationErrorBound
    (N : ℕ) (errorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖C2.continuedOddDirichletChannel s -
            upperEtaOddChannelApproximation N s‖ ≤ errorUpper s ∧
          2 * C2.verticalDepthTailUpper s * errorUpper s <
            ‖upperOddChannelResolventNumerator
                (upperEtaOddChannelApproximation N) s‖ /
              (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOddChannelResolventErrorBound
    (upperEtaOddChannelApproximation N) errorUpper cover

/--
Eta-specialized endpoint in the reduced relative-error form.

This is the current canonical final bound target for the upper-half route.
-/
theorem RiemannHypothesis_of_upperEtaOddChannelApproximationRelativeError
    (N : ℕ) (errorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖C2.continuedOddDirichletChannel s -
            upperEtaOddChannelApproximation N s‖ ≤ errorUpper s ∧
          errorUpper s <
            ‖upperEtaOddChannelApproximation N s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperOddChannelResolventRelativeError
    (upperEtaOddChannelApproximation N) errorUpper cover

/--
Eta endpoint with the transported tail error exposed.

The remaining external analytic/numeric certificate can now be stated as:

1. the eta Euler denominator is nonzero;
2. `η_N` approximates the eta channel within `etaErrorUpper`;
3. the transported eta error satisfies the reduced relative margin.
-/
theorem RiemannHypothesis_of_upperEtaOddChannelApproximationTransportedRelativeError
    (N : ℕ) (etaErrorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        (1 - (2 : ℂ) * C2.complexDirichletCoeff s 2 ≠ 0) ∧
          ‖upperEtaChannel s - upperEtaAlternatingPartial N s‖ ≤
            etaErrorUpper s ∧
          ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s <
            ‖upperEtaOddChannelApproximation N s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaOddChannelApproximationRelativeError N
    (fun s => ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s)
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · rcases hbulk with ⟨hden, heta, hrelative⟩
        exact Or.inr
          ⟨upperEtaOddChannelApproximation_error_le_transport
              N etaErrorUpper hden heta,
            hrelative⟩)

/--
Streamlined eta endpoint on the upper off-critical strip.

The eta Euler denominator is discharged internally from `Re(s) < 1`; the only
bulk certificate obligations are the eta-tail estimate and the transported
relative dominance inequality.
-/
theorem RiemannHypothesis_of_upperEtaOddChannelTailRelativeBound
    (N : ℕ) (etaErrorUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperEtaChannel s - upperEtaAlternatingPartial N s‖ ≤
            etaErrorUpper s ∧
          ‖upperEtaOddChannelTransportFactor s‖ * etaErrorUpper s <
            ‖upperEtaOddChannelApproximation N s‖ *
              (1 - ‖C2.q s‖) / (1 + ‖C2.q s‖)) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperEtaOddChannelApproximationTransportedRelativeError
    N etaErrorUpper
    (fun s hs => by
      rcases cover s hs with hnear | hbulk
      · exact Or.inl hnear
      · exact Or.inr
          ⟨upperEtaOddChannelTransportFactor_den_ne_zero_of_upperOffCriticalStrip hs,
            hbulk.1, hbulk.2⟩)

/--
The vertical-tail specialization of the full-resolvent defect, obtained by
choosing the raw C2 numerator `K₂ = q²`.

This specialization is useful as a diagnostic and as a minimal sufficient
criterion, but the flexible `upperFullResolventDefect` endpoint above is the
route-facing target for refined numerators.
-/
noncomputable def upperFullResolventRemainder (s : ℂ) : ℂ :=
  genuineFInfinite s - C2.verticalDepthTailFromTwo s

theorem upperFullResolventDefect_q_sq_eq_remainder_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    upperFullResolventDefect (fun s => C2.q s ^ 2) s =
      upperFullResolventRemainder s := by
  unfold upperFullResolventDefect upperFullResolventRemainder
  rw [C2.verticalDepthTailFromTwo_eq s hs]
  unfold C2.verticalResolvent
  rw [div_eq_mul_inv]

theorem genuineFInfinite_eq_c2AnalyticBulkF_upperFullResolventRemainder_zero
    (s : ℂ) :
    genuineFInfinite s =
      C2.c2AnalyticBulkF upperFullResolventRemainder (fun _ => 0) s := by
  unfold upperFullResolventRemainder C2.c2AnalyticBulkF
  ring

/--
Vertical-tail full-resolvent endpoint with an explicit scalar majorant.

For each point in `1/2 < Re(s) < 1`, either the canonical near-axis certificate
applies, or a supplied bound `GUpper` dominates the vertical-tail remainder and
still fits below the C2 allowance.
-/
theorem RiemannHypothesis_of_upperFullResolventRemainderBound
    (GUpper : ℂ → ℝ)
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperFullResolventRemainder s‖ ≤ GUpper s ∧
          GUpper s < C2.c2AnalyticBulkAllowance s) :
    RiemannHypothesis := by
  refine RiemannHypothesis_of_upperBulkAntiMiracleOffCritical
    upperFullResolventRemainder (fun _ => 0)
    GUpper (fun _ => 0) ?_ ?_
  · intro s _hs
    exact genuineFInfinite_eq_c2AnalyticBulkF_upperFullResolventRemainder_zero s
  · intro s hs
    rcases cover s hs with hnear | hbulk
    · exact Or.inl hnear
    · exact Or.inr
        ⟨⟨by linarith [hs.1], hs.2, ne_of_gt hs.1⟩,
          hbulk.1, by simp, by simpa using hbulk.2⟩

/--
Sharp full-resolvent dominance endpoint.

This is the same closure with the majorant chosen to be the actual norm of the
vertical-tail remainder.  Thus a sufficient analytic inequality is exactly

`‖genuineFInfinite s - verticalDepthTailFromTwo s‖ <
  c2AnalyticBulkAllowance s`

on the upper half-strip outside the canonical near-axis region.
-/
theorem RiemannHypothesis_of_upperFullResolventRemainderDominance
    (cover : ∀ s : ℂ, upperOffCriticalStrip s →
      s ∈ C2.nearAxisRegion riemannZeta
            genuineFInfiniteNearAxis.near_axis.radius ∨
        ‖upperFullResolventRemainder s‖ <
          C2.c2AnalyticBulkAllowance s) :
    RiemannHypothesis :=
  RiemannHypothesis_of_upperFullResolventRemainderBound
    (fun s => ‖upperFullResolventRemainder s‖)
    (fun s hs => by
      rcases cover s hs with hnear | hdom
      · exact Or.inl hnear
      · exact Or.inr ⟨le_rfl, hdom⟩)

end PeerReview
end C2
