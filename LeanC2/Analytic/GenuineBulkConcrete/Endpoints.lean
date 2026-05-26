import LeanC2.Analytic.GenuineBulkConcrete.ContinuationRoutes

namespace C2

/--
Continuation-driven middle-strip closure for the natural odd-tail balancing
seed using a pointwise oscillatory cutoff witness
`‖Σ_{1 ≤ j < J} (-1)^j D_j(s)/(j! X^j)‖ + remainderUpper(s)`.
-/
theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
          oscillatoryMoment J cutoffScale remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
        oscillatoryMoment J cutoffScale remainderUpper)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
          oscillatoryMoment J cutoffScale remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
        oscillatoryMoment J cutoffScale remainderUpper)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_pointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
          oscillatoryMoment J cutoffScale remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (remainderUpper := remainderUpper)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hresidual hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_pointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
          oscillatoryMoment J cutoffScale remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (remainderUpper := remainderUpper)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hresidual hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
        c2ConcreteResolventNonCancellationAdjustedMain
            (c2OddTailBalancingSeed coreCutoff K M) s -
          c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
          c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_dominance
          (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
          (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
          (tiltConstant := tiltConstant) (tiltScale := tiltScale)
          (horizontalConstant := horizontalConstant)
          (horizontalScale := horizontalScale)
          (horizontalRatio := horizontalRatio)
          (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
          (hdominance hs))

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
        c2ConcreteResolventNonCancellationAdjustedMain
            (c2OddTailBalancingSeed coreCutoff K M) s -
          c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
          c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_dominance
          (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
          (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
          (tiltConstant := tiltConstant) (tiltScale := tiltScale)
          (horizontalConstant := horizontalConstant)
          (horizontalScale := horizontalScale)
          (horizontalRatio := horizontalRatio)
          (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
          (hdominance hs))

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        have hsScale := hscale hs
        have hsHorizontal := hhorizontal hs
        exact
          c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_combinedResidualDominance
            (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
            (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
            (tiltConstant := tiltConstant) (tiltScale := tiltScale)
            (horizontalConstant := horizontalConstant)
            (horizontalScale := horizontalScale)
            (horizontalRatio := horizontalRatio)
            (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
            hs.1
            hsScale.tiltScale_pos
            hsScale.tiltConstant_nonneg
            (hseed hs)
            hsScale.horizontalScale_pos
            hsScale.horizontalConstant_nonneg
            hsScale.horizontalRatio_nonneg
            hsScale.horizontalRatio_lt_one
            hsHorizontal.layer_bound
            (hdominance hs))

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        have hsScale := hscale hs
        have hsHorizontal := hhorizontal hs
        exact
          c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_combinedResidualDominance
            (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
            (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
            (tiltConstant := tiltConstant) (tiltScale := tiltScale)
            (horizontalConstant := horizontalConstant)
            (horizontalScale := horizontalScale)
            (horizontalRatio := horizontalRatio)
            (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
            hs.1
            hsScale.tiltScale_pos
            hsScale.tiltConstant_nonneg
            (hseed hs)
            hsScale.horizontalScale_pos
            hsScale.horizontalConstant_nonneg
            hsScale.horizontalRatio_nonneg
            hsScale.horizontalRatio_lt_one
            hsHorizontal.layer_bound
            (hdominance hs))

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {remainderTerm : ℂ → ℂ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_add_remainder
          (K := K) (M := M) (J := J) (X := X)
          (hexpansion hs) (hremainder hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {remainderTerm : ℂ → ℂ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_add_remainder
          (K := K) (M := M) (J := J) (X := X)
          (hexpansion hs) (hremainder hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤ remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_pointwiseOscillatoryResidualUpper_of_eq_add_remainder
          (hexpansion hs) (hremainder hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤ remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_pointwiseOscillatoryResidualUpper_of_eq_add_remainder
          (hexpansion hs) (hremainder hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_pointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤ remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (remainderUpper := remainderUpper)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      (remainderTerm := remainderTerm)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion hremainder hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_pointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤ remainderUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_pointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (remainderUpper := remainderUpper)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      (remainderTerm := remainderTerm)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion hremainder hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {remainderTerm : ℂ → ℂ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion hremainder hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {remainderTerm : ℂ → ℂ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion hremainder hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hJ : 1 ≤ J)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion
      (fun {s} hs =>
        c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper
          K M J X (s := s) hJ)
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hJ : 1 ≤ J)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hexpansion
      (fun {s} hs =>
        c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper
          K M J X (s := s) hJ)
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hJ : 1 ≤ J)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_canonicalRemainder
          (K := K) (M := M) (J := J) (X := X) (s := s) hJ (hexpansion hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hJ : 1 ≤ J)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialPointwiseOscillatoryCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_canonicalRemainder
          (K := K) (M := M) (J := J) (X := X) (s := s) hJ (hexpansion hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion_three
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M 3 X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M 3 X s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := 3) (X := X)
      continuation (hJ := by decide) hmiddle hseed hcutoff hexpansion hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion_three
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M 3 X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M 3 X s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansion
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := 3) (X := X)
      continuation (hJ := by decide) hmiddle hseed hcutoff hexpansion hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance_three
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M 3 X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M 3 X s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := 3) (X := X)
      continuation (hJ := by decide) hmiddle hseed hcutoff hexpansion hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance_three
    {coreCutoff : ℕ → ℕ} {K M : ℕ} {X : ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M 3 X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M 3 X s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exponentialPointwiseOscillatoryCanonicalExpansionCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := 3) (X := X)
      continuation (hJ := by decide) hmiddle hseed hcutoff hexpansion hdominance

/--
Continuation-driven middle-strip closure for the natural odd-tail balancing
seed using the note-style exponential cutoff residual upper
`C_Γ(s) * X^(1-σ) + C₁(s)/X + C₂(s)/X²`.
-/
theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      mellinGammaUpper dirichletShiftUpper secondOrderUpper : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationExponentialResidualUpper
          mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          mellinGammaUpper dirichletShiftUpper secondOrderUpper s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ConcreteResolventNonCancellationExponentialResidualUpper
        mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exponentialResidualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      mellinGammaUpper dirichletShiftUpper secondOrderUpper : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationExponentialResidualUpper
          mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedExponentialMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          mellinGammaUpper dirichletShiftUpper secondOrderUpper s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := c2ConcreteResolventNonCancellationExponentialResidualUpper
        mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale)
      continuation hscale hhorizontal hseed hcutoff hresidual
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialMargin,
          c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedMain
          (c2OddTailBalancingSeed coreCutoff K M) s -
        c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
        c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := fun _ => 0)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs => by
        have hsOpen : s ∈ openRightHalfPlane := by
          simpa [openRightHalfPlane] using hs.1.1
        have hres_eq :
            c2ConcreteResolventNonCancellationResidual
                (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s = 0 :=
          c2ConcreteResolventNonCancellationResidual_eq_zero_of_oddTailBalancingSeed_of_comparison
            comparison hsOpen
        simp [hres_eq])
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_atOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedMain
          (c2OddTailBalancingSeed coreCutoff K M) s -
        c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
        c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne comparison)
      hscale hhorizontal hseed hcutoff hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_atOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hscale : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarScaleData
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffScale s)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedMain
          (c2OddTailBalancingSeed coreCutoff K M) s -
        c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
        c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne comparison)
      hscale hhorizontal hseed hcutoff hdominance

theorem mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleSeparatedBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (hK : 2 ≤ K)
    (continuation : GenuineFInfiniteContinuationData)
    (hscale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < horizontalScale s)
    (hconstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 ≤ horizontalConstant s)
    (hratio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 ≤ horizontalRatio s)
    (hratio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      horizontalRatio s < 1)
    (hhorizontal : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedHorizontalLayerBudget
        coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedSeedScaledBound
        K M horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ)) s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedCutoffScaledBound K M
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedQuartetDominance
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleSeparatedMainBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio)
    (tiltScale := fun _ => (1 : ℝ))
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := c2CanonicalClosedCutoffConstant K M)
    (cutoffScale := fun _ => (1 : ℝ))
    hK continuation
    (fun _ hs => {
      tiltScale_pos := by norm_num
      tiltConstant_nonneg :=
        c2CanonicalClosedTiltConstant_nonneg_of_offCritical K M hs.1
          (hscale_pos hs)
          (hconstant_nonneg hs)
          (hratio_lt_one hs)
      horizontalScale_pos := hscale_pos hs
      horizontalConstant_nonneg := hconstant_nonneg hs
      horizontalRatio_nonneg := hratio_nonneg hs
      horizontalRatio_lt_one := hratio_lt_one hs
      cutoffScale_pos := by norm_num
    })
    (fun _ hs => hhorizontal hs)
    (fun _ hs => hseed hs)
    (fun _ hs => hcutoff hs)
    (fun _ hs => hdominance hs)

noncomputable def
    RiemannHypothesisTerminalData.ofContinuationAndExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofGenuineFInfiniteNearAxisAndExplicitScalarExactZetaMiddleRegion
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (GenuineFInfiniteNearAxisData.of_continuation continuation)
    hmiddle

theorem mathlibRiemannHypothesis_of_continuationAndExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesis := by
  let terminalData :=
    RiemannHypothesisTerminalData.ofContinuationAndExplicitScalarExactZetaMiddleRegion
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      continuation hmiddle
  exact mathlibRiemannHypothesis_of_terminalData terminalData

theorem mathlibRiemannHypothesis_of_continuationAndExpandedDominanceMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2ExpandedExactZetaDominanceRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_expandedDominanceMiddleRegion
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem mathlibRiemannHypothesis_of_continuationAndQuartetExactMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetExactMiddleRegion
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem mathlibRiemannHypothesis_of_continuationAndQuartetTriangleMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetTriangleMiddleRegion
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem mathlibRiemannHypothesis_of_continuationAndQuartetClosedMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
        coreCutoff K M rectangularUpper centralUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetClosedMiddleRegion
    (rectangularUpper := rectangularUpper) (centralUpper := centralUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
        coreCutoff K M continuedVerticalUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetComponentMiddleRegion
    (continuedVerticalUpper := continuedVerticalUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)


theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentTruncationBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (htiltScale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < tiltScale s)
    (htiltConstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 ≤ tiltConstant s)
    (hvertical : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ContinuedVerticalResidualBound K M continuedVerticalUpper s)
    (hhorizontalScale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < horizontalScale s)
    (hhorizontalConstant_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      horizontalRatio s < 1)
    (htruncation : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedOddTruncationBudget
        coreCutoff oddTruncationUpper
        horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2BalancingSeedFactorScaledBound
        continuedVerticalUpper
        (c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio)
        (fun s => 1 + ‖q s‖)
        tiltConstant tiltScale s)
    (hcutoffScale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < cutoffScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
          cutoffScale s ≤ cutoffConstant s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2QuartetBulkGUpper
          (c2BulkGUpper
            (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
            (c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio)) s +
        c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndQuartetComponentMiddleRegion
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (continuedVerticalUpper := continuedVerticalUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    continuation
    (fun _ hs =>
      C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates.of_truncationBounds
        hs.1
        (htiltScale_pos hs)
        (htiltConstant_nonneg hs)
        (hvertical hs)
        (hhorizontalScale_pos hs)
        (hhorizontalConstant_nonneg hs)
        (hhorizontalRatio_nonneg hs)
        (hhorizontalRatio_lt_one hs)
        (htruncation hs)
        (hseed hs)
        (hcutoffScale_pos hs)
        (hcutoff hs)
        (hdominance hs))

theorem mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleRegion
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem mathlibRiemannHypothesis_of_continuationAndExplicitFiniteCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
        coreCutoff K M zetaUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitFiniteCoreCover
    (zetaUpper := zetaUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (c2ExpandedScalarMiddleRegion_cover nearC2 edgeC2 hmiddle)

theorem mathlibRiemannHypothesis_of_continuationAndExplicitScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
        coreCutoff K M zetaUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitScalarCover
    (zetaUpper := zetaUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (c2ExpandedScalarMiddleRegion_cover nearC2 edgeC2 hmiddle)

theorem mathlibRiemannHypothesis_of_zetaDepthCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper oddFactorUpper zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
        coreCutoff K M
        depthUpper coreUpper oddFactorUpper zetaUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_zetaDepthCoreCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem mathlibRiemannHypothesis_of_explicitFiniteCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
        coreCutoff K M zetaUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitFiniteCoreCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem mathlibRiemannHypothesis_of_explicitScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
        coreCutoff K M zetaUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitScalarCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem offCriticalStripNonvanishing_of_explicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_explicitScalarExactZetaRegion
        (hmiddle hs))

theorem mathlibRiemannHypothesis_of_explicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_explicitScalarExactZetaRegion
        (hmiddle hs))

theorem rectangularOddCoreSum_sub_oddDirichletChannel_norm_le_explicit_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) (M : ℕ) :
    ‖rectangularOddCoreSum s M - oddDirichletChannel s‖ ≤
      oddDirichletTailExplicitUpper s ((M + 1) / 2) := by
  have hbound :=
    c2ConcreteOddTruncation_bound_of_oddDirichletTailExplicitUpper
      (coreCutoff := fun _ : ℕ => M)
      (oddTruncationUpper :=
        fun s _ => oddDirichletTailExplicitUpper s ((M + 1) / 2))
      (s := s) hs (by
        intro j
        exact le_rfl)
  simpa [c2ConcreteOddTruncationError, c2OddTruncationError] using hbound 0

theorem c2ConcreteCutoffErrorC0Zeta_eq_split_of_one_lt_re
    (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    c2ConcreteCutoffErrorC0Zeta K M s =
      (2 : ℂ) * rectangularDepthFactor s K *
        (rectangularOddCoreSum s M - oddDirichletChannel s) +
      (2 : ℂ) * (rectangularDepthFactor s K - verticalDepthTailFromTwo s) *
        oddDirichletChannel s := by
  unfold c2ConcreteCutoffErrorC0Zeta c2ConcreteCutoffErrorFromTarget
    c2RectangularGenuineOperator
  rw [rectangularGenuine_eq_depth_core]
  change 2 * rectangularDepthFactor s K * rectangularOddCoreSum s M -
      c0 s * riemannZeta s =
    (2 : ℂ) * rectangularDepthFactor s K *
        (rectangularOddCoreSum s M - oddDirichletChannel s) +
      (2 : ℂ) * (rectangularDepthFactor s K - verticalDepthTailFromTwo s) *
        oddDirichletChannel s
  rw [← centralFromOddDirichletChannel_identity_of_one_lt_re s hs]
  unfold centralFromOddChannel
  ring

theorem c2ConcreteCutoffErrorC0Zeta_norm_le_explicit_of_one_lt_re
    (K M : ℕ) {s : ℂ} (hK : 2 ≤ K) (hs : 1 < s.re) :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ ≤
      c2ConcreteCutoffErrorC0ZetaExplicitUpper s K M := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hdepth :
      ‖rectangularDepthFactor s K‖ ≤ rectangularDepthFactorExplicitUpper s K :=
    rectangularDepthFactor_norm_le_explicit_of_re_pos s K hs0 hK
  have hdepthCut :
      ‖rectangularDepthFactor s K - verticalDepthTailFromTwo s‖ ≤
        rectangularDepthCutoffUpper s K :=
    rectangularDepthFactor_sub_verticalDepthTailFromTwo_norm_le_explicit_of_re_pos
      s K hs0 hK
  have hoddTail :
      ‖rectangularOddCoreSum s M - oddDirichletChannel s‖ ≤
        oddDirichletTailExplicitUpper s ((M + 1) / 2) :=
    rectangularOddCoreSum_sub_oddDirichletChannel_norm_le_explicit_of_one_lt_re s hs M
  have hodd :
      ‖oddDirichletChannel s‖ ≤ oddDirichletChannelExplicitUpper s :=
    oddDirichletChannel_norm_le_explicit_of_one_lt_re s hs
  have hdepthUpper_nonneg : 0 ≤ rectangularDepthFactorExplicitUpper s K :=
    rectangularDepthFactorExplicitUpper_nonneg_of_re_pos s K hs0
  have hdepthCut_nonneg : 0 ≤ rectangularDepthCutoffUpper s K :=
    rectangularDepthCutoffUpper_nonneg_of_re_pos s K hs0
  have hterm1mul :
      ‖rectangularDepthFactor s K‖ *
          ‖rectangularOddCoreSum s M - oddDirichletChannel s‖ ≤
        rectangularDepthFactorExplicitUpper s K *
          oddDirichletTailExplicitUpper s ((M + 1) / 2) := by
    exact mul_le_mul hdepth hoddTail (norm_nonneg _) hdepthUpper_nonneg
  have hterm2mul :
      ‖rectangularDepthFactor s K - verticalDepthTailFromTwo s‖ *
          ‖oddDirichletChannel s‖ ≤
        rectangularDepthCutoffUpper s K * oddDirichletChannelExplicitUpper s := by
    exact mul_le_mul hdepthCut hodd (norm_nonneg _) hdepthCut_nonneg
  have hterm1 :
      ‖(2 : ℂ) * rectangularDepthFactor s K *
          (rectangularOddCoreSum s M - oddDirichletChannel s)‖ ≤
        2 * rectangularDepthFactorExplicitUpper s K *
          oddDirichletTailExplicitUpper s ((M + 1) / 2) := by
    rw [norm_mul, norm_mul]
    norm_num
    have h := mul_le_mul_of_nonneg_left hterm1mul (by positivity : 0 ≤ (2 : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hterm2 :
      ‖(2 : ℂ) * (rectangularDepthFactor s K - verticalDepthTailFromTwo s) *
          oddDirichletChannel s‖ ≤
        2 * rectangularDepthCutoffUpper s K * oddDirichletChannelExplicitUpper s := by
    rw [norm_mul, norm_mul]
    norm_num
    have h := mul_le_mul_of_nonneg_left hterm2mul (by positivity : 0 ≤ (2 : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  rw [c2ConcreteCutoffErrorC0Zeta_eq_split_of_one_lt_re K M hs]
  exact le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)

theorem c2ConcreteCutoffErrorC0Zeta_scaled_bound_of_explicit
    {K M : ℕ} {cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hK : 2 ≤ K) (hs : 1 < s.re)
    (hscale_nonneg : 0 ≤ cutoffScale s)
    (hscaled :
      c2ConcreteCutoffErrorC0ZetaExplicitUpper s K M * cutoffScale s ≤
        cutoffConstant s) :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (c2ConcreteCutoffErrorC0Zeta_norm_le_explicit_of_one_lt_re K M hK hs)
      hscale_nonneg)
    hscaled

structure C2OddTailBalancingSeedExplicitCutoffEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (fun s => c2VerticalC0ZetaAnchorExplicitUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_explicit_scaled_bound :
    c2ConcreteCutoffErrorC0ZetaExplicitUpper s K M * cutoffScale s ≤
      cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2OddTailBalancingSeedExplicitCutoffRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailBalancingSeedExplicitCutoffEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailBalancingSeedExplicitCutoffRegion_eq_empty
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2OddTailBalancingSeedExplicitCutoffRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale = ∅ := by
  ext s
  constructor
  · intro hs
    simpa using false_of_one_lt_re_offCritical hs.one_lt_re hs.offCritical
  · intro hs
    simp at hs

theorem c2OddTailBalancingSeed_mem_explicitAnchorRegion_of_mem_explicitCutoffRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailBalancingSeedExplicitAnchorRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_c0Zeta_scaled_bound :=
      c2ConcreteCutoffErrorC0Zeta_scaled_bound_of_explicit
        hs.two_le_K hs.one_lt_re (le_of_lt hs.cutoffScale_pos)
        hs.cutoff_explicit_scaled_bound
    dominance := hs.dominance
  }

theorem c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitCutoffRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitAnchorRegion
    (c2OddTailBalancingSeed_mem_explicitAnchorRegion_of_mem_explicitCutoffRegion hs)

theorem c2OddTailBalancingSeed_nonvanishing_of_mem_explicitCutoffRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact c2OddTailBalancingSeed_nonvanishing_of_mem_explicitAnchorRegion
    (c2OddTailBalancingSeed_mem_explicitAnchorRegion_of_mem_explicitCutoffRegion hs)

theorem c2OddTailBalancingSeedExplicitCutoffRegion_nonempty_iff
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) ↔
      ∃ s : ℂ,
        C2OddTailBalancingSeedExplicitCutoffEstimates
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  rfl

theorem
    c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion_nonempty_of_nonempty_explicitCutoffRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    Set.Nonempty
      (c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s,
    c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitCutoffRegion hs⟩

theorem c2OddTailBalancingSeed_exists_nonvanishing_point_of_nonempty_explicitCutoffRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∧
      genuineFInfinite s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  refine ⟨s,
    c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitCutoffRegion hs,
    c2OddTailBalancingSeed_nonvanishing_of_mem_explicitCutoffRegion hs⟩

/-!
### Right-half-plane explicit cutoff region

This is the domain-correct replacement for the vacuous off-critical version above.
It keeps the explicit `K, M` cutoff envelope on the half-plane `Re(s) > 1`, where
the current `c0 * ζ` identities and odd-tail estimates are actually available.
-/

structure C2OddTailBalancingSeedExplicitCutoffOneLtEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  one_lt_re : 1 < s.re
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (fun s => c2VerticalC0ZetaAnchorExplicitUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_explicit_scaled_bound :
    c2ConcreteCutoffErrorC0ZetaExplicitUpper s K M * cutoffScale s ≤
      cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2OddTailBalancingSeedExplicitCutoffOneLtRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailBalancingSeedExplicitCutoffOneLtEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailBalancingSeed_mem_c0ZetaCutoffOneLtRegion_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  have hscale_nonneg : 0 ≤ tiltScale s := le_of_lt hs.tiltScale_pos
  have hanchor_nonneg : 0 ≤ c2VerticalC0ZetaAnchorExplicitUpper s := by
    exact le_trans (norm_nonneg _)
      (c2VerticalC0ZetaAnchorResidual_bound_explicit_of_one_lt_re s hs.one_lt_re)
  have hcutoff_c0Zeta_scaled :
      ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s :=
    c2ConcreteCutoffErrorC0Zeta_scaled_bound_of_explicit
      hs.two_le_K hs.one_lt_re (le_of_lt hs.cutoffScale_pos)
      hs.cutoff_explicit_scaled_bound
  have hcutoff_constant_nonneg : 0 ≤ cutoffConstant s := by
    exact le_trans
      (mul_nonneg (norm_nonneg _) (le_of_lt hs.cutoffScale_pos))
      hcutoff_c0Zeta_scaled
  have hcutoff_upper_nonneg :
      0 ≤ c2CutoffUpperFromScale cutoffConstant cutoffScale s := by
    unfold c2CutoffUpperFromScale
    exact div_nonneg hcutoff_constant_nonneg (le_of_lt hs.cutoffScale_pos)
  have hvert_nonneg :
      0 ≤ c2VerticalC0ZetaAnchorExplicitUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s :=
    add_nonneg hanchor_nonneg hcutoff_upper_nonneg
  have hgap_nonneg : 0 ≤ 1 + ‖q s‖ := by
    positivity
  have hvertical :
      C2VerticalRectangularResidualBound K M
        (fun s => c2VerticalC0ZetaAnchorExplicitUpper s +
          c2CutoffUpperFromScale cutoffConstant cutoffScale s) s := by
    exact c2VerticalRectangularResidualBound_of_c0ZetaAnchor_and_cutoffScaled
      hs.one_lt_re
      (c2VerticalC0ZetaAnchorResidual_bound_explicit_of_one_lt_re s hs.one_lt_re)
      hs.cutoffScale_pos hcutoff_c0Zeta_scaled
  have hlayer :
      ∀ j : ℕ,
        ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
          (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j := by
    exact
      c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
        (coreCutoff := coreCutoff)
        (oddTruncationUpper :=
          fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (s := s)
        (c2ConcreteOddTruncation_bound_of_oddDirichletTailExplicitUpper
          (coreCutoff := coreCutoff)
          (oddTruncationUpper :=
            fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
          hs.one_lt_re
          (by
            intro j
            rfl))
        hs.horizontal_budget
  have hhorizontal :
      C2OddHorizontalDefectBound coreCutoff
        (c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio) s :=
    c2OddHorizontalDefectBound_of_layer_geometric
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one hlayer
  have hgap : C2ResolventGapBound (fun s => 1 + ‖q s‖) s :=
    c2ResolventGapBound_one_add_norm_q s
  have hseed_scaled_bound :
      C2OddTailBalancingSeedScaledBound coreCutoff K M tiltConstant tiltScale s :=
    c2OddTailBalancingSeed_scaledBound_of_componentBounds
      hvert_nonneg hgap_nonneg hscale_nonneg
      hvertical hhorizontal hgap hs.balancing_seed_factor_scaled_bound
  exact {
    one_lt_re := hs.one_lt_re
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound :=
      c2OddTailBalancingSeed_scaled_bound hscale_nonneg hseed_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_c0Zeta_scaled_bound := hcutoff_c0Zeta_scaled
    dominance := hs.dominance
  }

theorem c2OddTailBalancingSeed_nonvanishing_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  rw [c2OddTailGenuineIdentity_balancingSeed_at_of_one_lt_re
    coreCutoff K M hs.one_lt_re]
  exact c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLt_nonvanishing_of_mem
    (c2OddTailBalancingSeed_mem_c0ZetaCutoffOneLtRegion_of_mem_explicitCutoffOneLtRegion hs)

theorem c2OddTailBalancingSeedBulkModel_nonvanishing_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rw [show c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s by
    simpa [oneLtHalfPlane] using
      (c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_oneLtHalfPlane
        coreCutoff K M s hs.one_lt_re)]
  exact c2OddTailBalancingSeed_nonvanishing_of_mem_explicitCutoffOneLtRegion hs

theorem c2OddTailContinuedBalancingSeedBulkModel_eq_oldBulkModel_on_oneLtHalfPlane
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    ∀ s : ℂ, s ∈ oneLtHalfPlane →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s =
        c2OddTailBalancingSeedBulkModel coreCutoff K M s := by
  intro s hs
  have hsOneLt : 1 < s.re := by
    simpa [oneLtHalfPlane] using hs
  have hsRePos : 0 < s.re :=
    lt_trans zero_lt_one hsOneLt
  calc
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s =
        continuedCentralOddChannel s := by
          simpa using
            (c2OddTailContinuedBalancingSeedBulkModel_eq_continuedCentral_of_re_pos
              coreCutoff K M (s := s) hsRePos)
    _ = c2OddTailBalancingSeedBulkModel coreCutoff K M s := by
          symm
          exact
            c2OddTailBalancingSeedBulkModel_eq_continuedCentralOddChannel_on_oneLtHalfPlane
              coreCutoff K M s hs

theorem c2OddTailBalancingSeedBulkModel_norm_le_exactZetaScalar_of_one_lt_re
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖c2OddTailBalancingSeedBulkModel coreCutoff K M s‖ ≤
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  have hsOneLt : s ∈ oneLtHalfPlane := by
    simpa [oneLtHalfPlane] using hs
  calc
    ‖c2OddTailBalancingSeedBulkModel coreCutoff K M s‖ =
        ‖continuedCentralOddChannel s‖ := by
          rw [c2OddTailBalancingSeedBulkModel_eq_continuedCentralOddChannel_on_oneLtHalfPlane
            coreCutoff K M s hsOneLt]
    _ = ‖genuineCentralDoubleSeries s‖ := by
          rw [continuedCentralOddChannel_eq_genuineCentralDoubleSeries_on_oneLtHalfPlane
            s hsOneLt]
    _ ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
          c2GenuineCentralDoubleSeries_norm_le_exactZetaScalar_of_one_lt_re hs

theorem c2OddTailContinuedBalancingSeedBulkModel_norm_le_exactZetaScalar_of_one_lt_re
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s‖ ≤
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  have hsOneLt : s ∈ oneLtHalfPlane := by
    simpa [oneLtHalfPlane] using hs
  rw [c2OddTailContinuedBalancingSeedBulkModel_eq_oldBulkModel_on_oneLtHalfPlane
    coreCutoff K M s hsOneLt]
  exact c2OddTailBalancingSeedBulkModel_norm_le_exactZetaScalar_of_one_lt_re
    coreCutoff K M hs

theorem c2OddTailBalancingSeedBulkModel_norm_le_exactZetaScalar_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    ‖c2OddTailBalancingSeedBulkModel coreCutoff K M s‖ ≤
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
  c2OddTailBalancingSeedBulkModel_norm_le_exactZetaScalar_of_one_lt_re
    coreCutoff K M hs.one_lt_re

theorem c2OddTailContinuedBalancingSeedBulkModel_norm_le_exactZetaScalar_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    ‖c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s‖ ≤
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
  c2OddTailContinuedBalancingSeedBulkModel_norm_le_exactZetaScalar_of_one_lt_re
    coreCutoff K M hs.one_lt_re

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rw [show c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s =
      c2OddTailBalancingSeedBulkModel coreCutoff K M s by
    simpa [oneLtHalfPlane] using
      (c2OddTailContinuedBalancingSeedBulkModel_eq_oldBulkModel_on_oneLtHalfPlane
        coreCutoff K M s hs.one_lt_re)]
  exact c2OddTailBalancingSeedBulkModel_nonvanishing_of_mem_explicitCutoffOneLtRegion hs

theorem c2OddTailBalancingSeedExplicitCutoffOneLtRegion_nonempty_iff
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) ↔
      ∃ s : ℂ,
        C2OddTailBalancingSeedExplicitCutoffOneLtEstimates
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  rfl

theorem
    c2OddTailBalancingSeed_exists_nonvanishing_point_of_nonempty_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∧
      genuineFInfinite s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s, hs,
    c2OddTailBalancingSeed_nonvanishing_of_mem_explicitCutoffOneLtRegion hs⟩

theorem
    c2OddTailBalancingSeedBulkModel_exists_nonvanishing_point_of_nonempty_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∧
      c2OddTailBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s, hs,
    c2OddTailBalancingSeedBulkModel_nonvanishing_of_mem_explicitCutoffOneLtRegion hs⟩

theorem
  c2OddTailContinuedBalancingSeedBulkModel_exists_nonzero_of_nonempty_explicitCutoffOneLtRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2OddTailBalancingSeedExplicitCutoffOneLtRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∧
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s, hs,
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitCutoffOneLtRegion hs⟩

end C2
