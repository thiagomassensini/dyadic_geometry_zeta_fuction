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
