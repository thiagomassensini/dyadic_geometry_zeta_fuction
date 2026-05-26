import LeanC2.Analytic.GenuineBulkConcrete

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

end PeerReview
end C2
