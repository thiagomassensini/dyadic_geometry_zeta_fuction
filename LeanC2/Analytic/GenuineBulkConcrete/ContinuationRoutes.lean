import LeanC2.Analytic.GenuineBulkConcrete.Terminal

namespace C2

noncomputable def C2ExpandedScalarMiddleRegionData.ofContinuation
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
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact {
    near := nearC2
    edge := edgeC2
    middle_local := fun _ hs => hmiddle hs
  }

theorem offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegionWithBounds
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
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_expandedScalarMiddleRegionData
    (C2ExpandedScalarMiddleRegionData.ofContinuation
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation hmiddle)

theorem mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegionWithBounds
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
      C2ExpandedScalarLocalBulkData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_expandedScalarMiddleRegionData
    (C2ExpandedScalarMiddleRegionData.ofContinuation
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation hmiddle)

theorem mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddlePointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hK : 2 ≤ K)
    (continuation : GenuineFInfiniteContinuationData)
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
    (hmain : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedScalarMainInequalities
        K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegionWithBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    continuation
    (fun _ hs => {
      two_le_K := hK
      offCritical := hs.1
      scale := hscale hs
      horizontal := hhorizontal hs
      main := hmain hs
    })

theorem mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleSeparatedMainBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hK : 2 ≤ K)
    (continuation : GenuineFInfiniteContinuationData)
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
      C2ExpandedSeedScaledBound
        K M horizontalConstant horizontalScale horizontalRatio
        tiltConstant tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedCutoffScaledBound K M cutoffConstant cutoffScale s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ExpandedQuartetDominance
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    hK continuation hscale hhorizontal
    (fun _ hs =>
      C2ExpandedScalarMainInequalities.ofComponents
        (hseed hs)
        (hcutoff hs)
        (hdominance hs))

/--
Continuation-driven middle-strip closure for the natural odd-tail balancing
seed using a real residual upper `|F_∞ - F_X| ≤ residualUpper` in the
resolvent non-cancellation criterion.
-/
theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale residualUpper : ℂ → ℝ}
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
        residualUpper s)
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
          cutoffConstant cutoffScale s -
        residualUpper s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  intro s hs
  rcases c2ExpandedScalarMiddleRegion_cover nearC2 edgeC2 (fun _ hs => hs) s hs with
    hnear | hmiddle | hedge
  · exact nearC2.near_axis.nonvanishing_of_mem hnear
  · have hsScale := hscale hmiddle
    have hsHorizontal := hhorizontal hmiddle
    have hgenuine : genuineFInfinite s ≠ 0 :=
      c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
        hmiddle.1
        hsScale.tiltScale_pos
        hsScale.tiltConstant_nonneg
        (hseed hmiddle)
        hsScale.horizontalScale_pos
        hsScale.horizontalConstant_nonneg
        hsScale.horizontalRatio_nonneg
        hsScale.horizontalRatio_lt_one
        hsHorizontal.layer_bound
        hsScale.cutoffScale_pos
        (hcutoff hmiddle)
        (hresidual hmiddle)
        (hdominance hmiddle)
    have hsPunctured : s ∈ puncturedOpenRightHalfPlane := by
      refine ⟨hmiddle.1.1, ?_⟩
      intro hsOne
      have hre : s.re = 1 := by
        have hre' : s.re = (1 : ℂ).re := congrArg Complex.re hsOne
        norm_num at hre'
        exact hre'
      linarith [hmiddle.1.2.1, hre]
    have hEq :
        c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s :=
      c2OddTailContinuedBalancingSeedBulkModel_eq_genuineFInfinite_on_punctured
        (coreCutoff := coreCutoff) (K := K) (M := M)
        continuation s hsPunctured
    exact fun hzero => by
      have hgenuineZero : genuineFInfinite s = 0 := by
        rw [hEq] at hzero
        exact hzero
      exact hgenuine hgenuineZero
  · exact edgeC2.edge_nonvanishing hedge

/--
Continuation-driven middle-strip closure for the natural odd-tail balancing
seed using the zero-proxy resolvent non-cancellation criterion.
-/
theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle
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
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := fun _ => 0)
      continuation
      hscale hhorizontal hseed hcutoff
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
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale residualUpper : ℂ → ℝ}
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
        residualUpper s)
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
          cutoffConstant cutoffScale s -
        residualUpper s > 0) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity
    (c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity_offCritical
      coreCutoff K M)
    (offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := residualUpper)
      continuation hscale hhorizontal hseed hcutoff hresidual hdominance)

/--
Continuation-driven middle-strip closure for the natural odd-tail balancing
seed, with the resolvent non-cancellation residual bounded through the central defect
`‖genuineCentralDoubleSeries - continuedCentralOddChannel‖`.
-/
theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_centralDefectBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale centralDefectUpper s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := centralDefectUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs => by
        rw [c2ConcreteResolventNonCancellationResidual_norm_eq_centralDefect_of_continuation_offCritical
          continuation hs.1]
        exact hcentralDefect hs)
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_centralDefectBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale centralDefectUpper s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_residualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (residualUpper := centralDefectUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs => by
        rw [c2ConcreteResolventNonCancellationResidual_norm_eq_centralDefect_of_continuation_offCritical
          continuation hs.1]
        exact hcentralDefect hs)
      (fun {s} hs => by
        simpa [c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_separatedCentralBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      genuineCentralUpper continuedCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hcontinued : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ContinuedCentralBound continuedCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_centralDefectBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (centralDefectUpper :=
        c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2CentralDefectBound_triangle_of_bounds
          (hgenuineCombined hs) (hcontinued hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_separatedCentralBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      genuineCentralUpper continuedCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hcontinued : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ContinuedCentralBound continuedCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper) s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_centralDefectBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (centralDefectUpper :=
        c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun {s} hs =>
        c2CentralDefectBound_triangle_of_bounds
          (hgenuineCombined hs) (hcontinued hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_separatedCentralBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (genuineCentralUpper := genuineCentralUpper)
      (continuedCentralUpper := c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
      continuation hscale hhorizontal hseed hcutoff hgenuineCombined
      (fun {s} hs => by
        simpa [C2ContinuedCentralBound, c2ContinuedCentralExactUpper] using
          c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip hs.1)
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_separatedCentralBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (genuineCentralUpper := genuineCentralUpper)
      (continuedCentralUpper := c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
      continuation hscale hhorizontal hseed hcutoff hgenuineCombined
      (fun {s} hs => by
        simpa [C2ContinuedCentralBound, c2ContinuedCentralExactUpper] using
          c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip hs.1)
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exactGenuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralExactUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun _ _ => c2GenuineCentralBound_exact _)
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_exactGenuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralExactUpper)
      continuation hscale hhorizontal hseed hcutoff
      (fun _ _ => c2GenuineCentralBound_exact _)
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation hscale hhorizontal hseed hcutoff hgenuineCombined
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
          (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
          (coreCutoff := coreCutoff)
          (tiltConstant := tiltConstant) (tiltScale := tiltScale)
          (horizontalConstant := horizontalConstant)
          (horizontalScale := horizontalScale)
          (horizontalRatio := horizontalRatio)
          (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
          (residualUpper := c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
          hs.1 (hscale hs).tiltScale_pos
          (hscale hs).tiltConstant_nonneg (hseed hs)
          (hscale hs).horizontalScale_pos
          (hscale hs).horizontalConstant_nonneg
          (hscale hs).horizontalRatio_nonneg
          (hscale hs).horizontalRatio_lt_one
          (hhorizontal hs).layer_bound (hdominance hs))

theorem
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation hscale hhorizontal hseed hcutoff hgenuineCombined
      (fun {s} hs =>
        c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
          (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
          (coreCutoff := coreCutoff)
          (tiltConstant := tiltConstant) (tiltScale := tiltScale)
          (horizontalConstant := horizontalConstant)
          (horizontalScale := horizontalScale)
          (horizontalRatio := horizontalRatio)
          (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
          (residualUpper := c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
          hs.1 (hscale hs).tiltScale_pos
          (hscale hs).tiltConstant_nonneg (hseed hs)
          (hscale hs).horizontalScale_pos
          (hscale hs).horizontalConstant_nonneg
          (hscale hs).horizontalRatio_nonneg
          (hscale hs).horizontalRatio_lt_one
          (hhorizontal hs).layer_bound (hdominance hs))

/--
Local middle-strip data for the resolvent non-cancellation route through a genuine-central
upper bound. The continued-central side stays discharged by the exact-zeta
scalar envelope, so the remaining local input is exactly scale, horizontal,
seed, cutoff, a `genuineCentralUpper`, and the final adjusted-margin positivity.
-/
structure C2ResolventNonCancellationGenuineCentralLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ)
    (s : ℂ) : Prop where
  scale : C2ExpandedScalarScaleData
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffScale s
  horizontal : C2ExpandedHorizontalLayerBudget
    coreCutoff horizontalConstant horizontalScale horizontalRatio s
  seed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s
  cutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  genuine : C2GenuineCentralBound genuineCentralUpper s
  dominance :
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale
        (c2CentralDefectTriangleUpper
          genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0

theorem C2ExpandedScalarLocalBulkData.toResolventNonCancellationGenuineCentralLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      tiltConstant s / tiltScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤
      cutoffConstant s)
    (hgenuine : C2GenuineCentralBound genuineCentralUpper s)
    (hdominance :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    C2ResolventNonCancellationGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper s := by
  exact {
    scale := data.scale
    horizontal := data.horizontal
    seed := hseed
    cutoff := hcutoff
    genuine := hgenuine
    dominance := hdominance
  }

theorem C2ResolventNonCancellationGenuineCentralLocalData.of_majorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper centralDefectMajorant : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      tiltConstant s / tiltScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤
      cutoffConstant s)
    (hgenuine : C2GenuineCentralBound genuineCentralUpper s)
    (hmajorant :
      c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper s := by
  refine {
    scale := hscale
    horizontal := hhorizontal
    seed := hseed
    cutoff := hcutoff
    genuine := hgenuine
    dominance := ?_
  }
  have hcombined :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s := by
    exact lt_of_le_of_lt
      (by
        simpa [add_comm] using
          add_le_add_left hmajorant
            (c2ExpandedQuartetResidualUpper
              tiltConstant tiltScale
              horizontalConstant horizontalScale horizontalRatio
              cutoffConstant cutoffScale s))
      hdominance
  exact
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
      (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
      (coreCutoff := coreCutoff)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (residualUpper := c2CentralDefectTriangleUpper
        genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
      hoff hscale.tiltScale_pos hscale.tiltConstant_nonneg hseed
      hscale.horizontalScale_pos hscale.horizontalConstant_nonneg
      hscale.horizontalRatio_nonneg hscale.horizontalRatio_lt_one
      hhorizontal.layer_bound hcombined

theorem
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ResolventNonCancellationGenuineCentralLocalData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale genuineCentralUpper s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      (fun _ hs => (hmiddle hs).seed)
      (fun _ hs => (hmiddle hs).cutoff)
      (fun _ hs => (hmiddle hs).genuine)
      (fun _ hs => (hmiddle hs).dominance)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs =>
        C2ExpandedScalarLocalBulkData.toResolventNonCancellationGenuineCentralLocalData
          (hmiddle hs) (hseed hs) (hcutoff hs)
            (hgenuineCombined hs) (hdominance hs))

theorem
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ResolventNonCancellationGenuineCentralLocalData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale genuineCentralUpper s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      (fun _ hs => (hmiddle hs).seed)
      (fun _ hs => (hmiddle hs).cutoff)
      (fun _ hs => (hmiddle hs).genuine)
      (fun _ hs => (hmiddle hs).dominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs =>
        C2ExpandedScalarLocalBulkData.toResolventNonCancellationGenuineCentralLocalData
          (hmiddle hs) (hseed hs) (hcutoff hs)
            (hgenuineCombined hs) (hdominance hs))

private theorem c2ContinuedVerticalResidualBound_exactZetaScalar_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hK : 2 ≤ K) (hs : offCriticalStrip s) :
    C2ContinuedVerticalResidualBound K M
      (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M) s := by
  have hrect :
      C2RectangularGenuineBound K M
        (c2ExplicitFiniteCoreRectangularUpper K M) s := by
    unfold c2ExplicitFiniteCoreRectangularUpper
    exact c2RectangularGenuineBound_depthCore_of_bounds
      (c2RectangularDepthFactorBound_explicit_of_offCriticalStrip K hs hK)
      (c2RectangularOddCoreBound_finite M s)
  have hodd :
      C2ContinuedOddChannelBound
        (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper) s := by
    simpa [c2ExplicitFiniteCoreOddUpper] using
      (c2ContinuedOddChannelBound_of_zetaBound
        (c2OddEulerFactorBound_triangle s)
        (c2RiemannZetaBound_exact s))
  have hcentral :
      C2ContinuedCentralBound
        (c2ExplicitFiniteCoreCentralUpper c2RiemannZetaExactUpper) s :=
    c2ContinuedCentralBound_of_oddChannelBound hs hodd
  simpa [c2ExplicitFiniteCoreContinuedVerticalUpper_exactZeta_eq_scalar] using
    (c2ContinuedVerticalResidualBound_closedUpper_of_bounds hs hrect hcentral)

private theorem
    c2OddTailContinuedBalancingSeed_norm_le_exactZetaScalar_of_localData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
      (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s) *
        (1 + ‖q s‖) := by
  have hvert :
      C2ContinuedVerticalResidualBound K M
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M) s :=
    c2ContinuedVerticalResidualBound_exactZetaScalar_of_offCriticalStrip
      K M data.two_le_K data.offCritical
  have hhorizontal :
      C2OddHorizontalDefectBound coreCutoff
        (c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio) s :=
    c2OddHorizontalDefectBound_of_layer_geometric
      data.scale.horizontalScale_pos data.scale.horizontalConstant_nonneg
      data.scale.horizontalRatio_nonneg data.scale.horizontalRatio_lt_one
      data.horizontal.layer_bound
  have hgap : ‖1 - q s‖ ≤ 1 + ‖q s‖ := by
    simpa [C2ResolventGapBound] using (c2ResolventGapBound_one_add_norm_q s)
  have hsum_nonneg :
      0 ≤ c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s := by
    have hvert_nonneg :
        0 ≤ c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s :=
      c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper_nonneg_of_re_pos
        K M data.offCritical.1
    have hhorizontal_nonneg :
        0 ≤ c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s :=
      le_trans (norm_nonneg _) hhorizontal
    exact add_nonneg hvert_nonneg hhorizontal_nonneg
  have hsum :
      ‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s := by
    exact add_le_add hvert hhorizontal
  have hprod :
      (‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
          ‖1 - q s‖ ≤
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖) := by
    exact mul_le_mul hsum hgap (norm_nonneg _) hsum_nonneg
  exact le_trans
    (c2OddTailContinuedBalancingSeed_norm_le coreCutoff K M s)
    hprod

private theorem
    c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    {centralDefectUpper : ℂ → ℝ}
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hscaled :
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
  have hcontinued :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖) :=
    c2OddTailContinuedBalancingSeed_norm_le_exactZetaScalar_of_localData data
  have hgap : ‖1 - q s‖ ≤ 1 + ‖q s‖ := by
    simpa [C2ResolventGapBound] using (c2ResolventGapBound_one_add_norm_q s)
  have hseed_scaled :
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ * tiltScale s ≤
        tiltConstant s :=
    c2OddTailBalancingSeed_scaled_bound_of_continued_and_centralDefect
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedSeedUpper := fun s =>
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖))
      (centralDefectUpper := centralDefectUpper)
      (resolventGapUpper := fun s => 1 + ‖q s‖)
      (hscale_nonneg := le_of_lt data.scale.tiltScale_pos)
      (hcontinued := hcontinued)
      (hcentralDefect := hcentralDefect)
      (hgap := hgap)
      (hscaled := hscaled)
  exact c2TiltSeed_bound_from_scaled data.scale.tiltScale_pos hseed_scaled

private theorem
    c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneUpper
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hgenuineUpper :
      s.re ≤ 1 →
        centralDefectUpper s +
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s)
    (hscaled :
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
  have hcontinued :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖) :=
    c2OddTailContinuedBalancingSeed_norm_le_exactZetaScalar_of_localData data
  have hgap : ‖1 - q s‖ ≤ 1 + ‖q s‖ := by
    simpa [C2ResolventGapBound] using (c2ResolventGapBound_one_add_norm_q s)
  have hdefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s :=
    c2CentralDefect_norm_le_splitAtOneUpper_of_exactZetaCentralDefect
      data.offCritical hcentralDefect hgenuineUpper
  have hseed_scaled :
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ * tiltScale s ≤ tiltConstant s :=
    c2OddTailBalancingSeed_scaled_bound_of_continued_and_centralDefect
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedSeedUpper := fun s =>
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖))
      (centralDefectUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (resolventGapUpper := fun s => 1 + ‖q s‖)
      (hscale_nonneg := le_of_lt data.scale.tiltScale_pos)
      (hcontinued := hcontinued)
      (hcentralDefect := hdefect)
      (hgap := hgap)
      (hscaled := hscaled)
  exact c2TiltSeed_bound_from_scaled data.scale.tiltScale_pos hseed_scaled

private theorem
    c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneDefectUpper
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    (hdefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hscaled :
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
  have hcontinued :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖) :=
    c2OddTailContinuedBalancingSeed_norm_le_exactZetaScalar_of_localData data
  have hgap : ‖1 - q s‖ ≤ 1 + ‖q s‖ := by
    simpa [C2ResolventGapBound] using (c2ResolventGapBound_one_add_norm_q s)
  have hseed_scaled :
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ * tiltScale s ≤ tiltConstant s :=
    c2OddTailBalancingSeed_scaled_bound_of_continued_and_centralDefect
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedSeedUpper := fun s =>
        (c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖))
      (centralDefectUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (resolventGapUpper := fun s => 1 + ‖q s‖)
      (hscale_nonneg := le_of_lt data.scale.tiltScale_pos)
      (hcontinued := hcontinued)
      (hcentralDefect := hdefect)
      (hgap := hgap)
      (hscaled := hscaled)
  exact c2TiltSeed_bound_from_scaled data.scale.tiltScale_pos hseed_scaled

private theorem
    c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    {centralDefectUpper genuineCentralUpper : ℂ → ℝ}
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hupper :
      s.re ≤ 1 →
        centralDefectUpper s +
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s) :
    s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
  intro hle
  unfold C2GenuineCentralBound
  have hcontinued :
      ‖continuedCentralOddChannel s‖ ≤
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
    simpa [C2ContinuedCentralBound, c2ContinuedCentralExactUpper] using
      c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip
        data.offCritical
  have hdecomp :
      (genuineCentralDoubleSeries s - continuedCentralOddChannel s) +
          continuedCentralOddChannel s =
        genuineCentralDoubleSeries s := by
    ring
  calc
    ‖genuineCentralDoubleSeries s‖ =
        ‖(genuineCentralDoubleSeries s - continuedCentralOddChannel s) +
            continuedCentralOddChannel s‖ := by
          rw [hdecomp]
    _ ≤ ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ +
          ‖continuedCentralOddChannel s‖ := by
            exact norm_add_le _ _
    _ ≤ centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
            exact add_le_add hcentralDefect hcontinued
    _ ≤ genuineCentralUpper s := hupper hle

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOneScaledBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hdefectSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneDefectUpper
      (data := hmiddle hs)
      (hdefect := hdefectSplitAtOne hs)
      (hscaled := hseedSplitAtOne hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneDefectUpper
      (hdefect := hdefectSplitAtOne hs)
      (hscaled := hcutoffSplitAtOne hs)
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuineLeOne hs))
      hdominance

/--
Middle-strip package for the resolvent non-cancellation route through a caller-supplied
genuine-central upper bound.
-/
structure C2ResolventNonCancellationGenuineCentralMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ) where
  continuation : GenuineFInfiniteContinuationData
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion
      (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
        (coreCutoff := coreCutoff) (K := K) (M := M)
        continuation
        (GenuineFInfiniteNearAxisData.of_continuation continuation))
      (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
        (coreCutoff := coreCutoff) (K := K) (M := M)) →
    C2ResolventNonCancellationGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper s

theorem offCriticalStripNonvanishing_of_resolventNonCancellationGenuineCentralMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (data : C2ResolventNonCancellationGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      data.continuation
      (fun _ hs => data.middle_local hs)

theorem mathlibRiemannHypothesis_of_resolventNonCancellationGenuineCentralMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (data : C2ResolventNonCancellationGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      data.continuation
      (fun _ hs => data.middle_local hs)

def C2ResolventNonCancellationGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2ResolventNonCancellationGenuineCentralLocalData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale genuineCentralUpper s) :
    C2ResolventNonCancellationGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper where
  continuation := continuation
  middle_local := fun _ hs => hmiddle hs

def C2ResolventNonCancellationGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionGenuineCentralBoundSplitAtOneScaledBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
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
    (hdefectSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s)
    (hexactLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) where
  continuation := continuation
  middle_local := fun s hs => by
    have hseed :
        ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s :=
      c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneDefectUpper
        (data := hmiddle hs)
        (hdefect := hdefectSplitAtOne hs)
        (hscaled := hseedSplitAtOne hs)
    have hcutoff :
        ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s :=
      (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneDefectUpper
        (hdefect := hdefectSplitAtOne hs)
        (hscaled := hcutoffSplitAtOne hs)
    have hgenuine :
        C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s :=
      c2GenuineCentralBound_splitAtOne
        (genuineCentralUpper := genuineCentralUpper) (s := s)
        (hgenuineLeOne hs)
    have hmajorant :
        c2CentralDefectTriangleUpper
            (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s :=
      c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper_of_exactZetaLeOne
        (genuineCentralUpper := genuineCentralUpper)
        (s := s)
        (hexact_le := hexactLeOne hs)
    exact
      C2ResolventNonCancellationGenuineCentralLocalData.of_majorantCombinedResidualDominance
        (centralDefectMajorant := fun s =>
          2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
        hs.1 (hmiddle hs).scale (hmiddle hs).horizontal
        hseed hcutoff hgenuine hmajorant (hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOneScaledBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hdefectSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s)
    (hexactLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_resolventNonCancellationGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionGenuineCentralBoundSplitAtOneScaledBoundsCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        (genuineCentralUpper := genuineCentralUpper)
        continuation hmiddle hdefectSplitAtOne hseedSplitAtOne hcutoffSplitAtOne
        hgenuineLeOne hexactLeOne hdominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOneScaledBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hdefectSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s)
    (hexactLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_resolventNonCancellationGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionGenuineCentralBoundSplitAtOneScaledBoundsCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        (genuineCentralUpper := genuineCentralUpper)
        continuation hmiddle hdefectSplitAtOne hseedSplitAtOne hcutoffSplitAtOne
        hgenuineLeOne hexactLeOne hdominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound_splitAtOneScaledBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hdefectSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineLeOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneDefectUpper
      (data := hmiddle hs)
      (hdefect := hdefectSplitAtOne hs)
      (hscaled := hseedSplitAtOne hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneDefectUpper
      (hdefect := hdefectSplitAtOne hs)
      (hscaled := hcutoffSplitAtOne hs)
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuineLeOne hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hgenuine hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
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
    (hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndOddTailBalancingResolventNonCancellationMiddle_of_genuineCentralCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs => (hmiddle hs).scale)
      (fun _ hs => (hmiddle hs).horizontal)
      hseed hcutoff hgenuine hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        c2CentralDefectTriangleUpper
          (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper centralDefectMajorant : ℂ → ℝ}
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
    (hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs =>
        C2ResolventNonCancellationGenuineCentralLocalData.of_majorantCombinedResidualDominance
          hs.1 (hmiddle hs).scale (hmiddle hs).horizontal
          (hseed hs) (hcutoff hs) (hgenuine hs) (hmajorant hs) (hdominance hs))

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper centralDefectMajorant : ℂ → ℝ}
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
    (hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound genuineCentralUpper s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          genuineCentralUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := genuineCentralUpper)
      continuation
      (fun _ hs =>
        C2ResolventNonCancellationGenuineCentralLocalData.of_majorantCombinedResidualDominance
          hs.1 (hmiddle hs).scale (hmiddle hs).horizontal
          (hseed hs) (hcutoff hs) (hgenuine hs) (hmajorant hs) (hdominance hs))

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper
      centralDefectMajorant : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := centralDefectMajorant)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hmajorant hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance_splitAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper
      centralDefectMajorant : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_exactZetaCentralDefect
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hcutoffCombined hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s := by
    intro s hs hle
    exact
      c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
        (data := hmiddle hs)
        (hcentralDefect := hcentralDefect hs)
        (hupper := hgenuineCombined hs)
        hle
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := centralDefectMajorant)
      continuation hmiddle hseed hcutoff
      (fun {s} hs =>
        c2GenuineCentralBound_splitAtOne
          (genuineCentralUpper := genuineCentralUpper) (s := s)
          (hgenuine hs))
      hmajorant hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneDoubleUpperCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance_splitAtOne
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (centralDefectUpper := centralDefectUpper)
      (genuineCentralUpper := genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hcentralDefect hseedCombined hcutoffCombined
      hgenuineCombined
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneDoubleUpperCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance_splitAtOne
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (centralDefectUpper := centralDefectUpper)
      (genuineCentralUpper := genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hcentralDefect hseedCombined hcutoffCombined
      hgenuineCombined
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneUpperBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneUpper
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hcutoffSplitAtOne hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s := by
    intro s hs
    exact c2GenuineCentralBound_splitAtOne
      (genuineCentralUpper := genuineCentralUpper) (s := s)
      (fun hle =>
        c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
          (data := hmiddle hs)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs)
          hle)
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hseed hcutoffCombined hgenuine
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneUpperBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * centralDefectUpper s) * (1 + ‖q s‖)) * tiltScale s ≤
          tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_exactZetaCentralDefect
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hscaled := hseedCombined hs)
  have hcutoffCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneUpper
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hcutoffSplitAtOne hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s := by
    intro s hs
    exact c2GenuineCentralBound_splitAtOne
      (genuineCentralUpper := genuineCentralUpper) (s := s)
      (fun hle =>
        c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
          (data := hmiddle hs)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs)
          hle)
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hseed hcutoffCombined hgenuine
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneScaledBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneUpper
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hseedSplitAtOne hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneUpper
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hcutoffSplitAtOne hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s := by
    intro s hs
    exact c2GenuineCentralBound_splitAtOne
      (genuineCentralUpper := genuineCentralUpper) (s := s)
      (fun hle =>
        c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
          (data := hmiddle hs)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs)
          hle)
  exact
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hseed hcutoff hgenuine
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralSplitAtOneScaledBoundsCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper genuineCentralUpper : ℂ → ℝ}
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
    (hcentralDefect : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hseedSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s) *
          (1 + ‖q s‖)) +
        (2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s)
    (hcutoffSplitAtOne : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s)
    (hgenuineCombined : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      s.re ≤ 1 →
      centralDefectUpper s +
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        genuineCentralUpper s)
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
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  have hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s := by
    intro s hs
    exact c2ExpandedScalarLocalBulkData_balancingSeed_bound_of_splitAtOneUpper
      (data := hmiddle hs)
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hseedSplitAtOne hs)
  have hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
    intro s hs
    exact (hmiddle hs).concreteCutoff_scaled_bound_of_splitAtOneUpper
      (hcentralDefect := hcentralDefect hs)
      (hgenuineUpper := hgenuineCombined hs)
      (hscaled := hcutoffSplitAtOne hs)
  have hgenuine : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s := by
    intro s hs
    exact c2GenuineCentralBound_splitAtOne
      (genuineCentralUpper := genuineCentralUpper) (s := s)
      (fun hle =>
        c2ExpandedScalarLocalBulkData_genuineCentral_bound_of_exactZetaCentralDefect_le_one
          (data := hmiddle hs)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs)
          hle)
  exact
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_genuineCentralMajorantCombinedResidualDominance
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
      (centralDefectMajorant := fun s =>
        2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s)
      continuation hmiddle hseed hcutoff hgenuine
      (fun {s} hs =>
        c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
          (genuineCentralUpper := genuineCentralUpper)
          (hcentralDefect := hcentralDefect hs)
          (hupper := hgenuineCombined hs))
      hdominance

/--
Exact-version local data for the resolvent non-cancellation fallback route in the middle
strip. This removes the separate `genuine` field by specializing to the neutral
upper `c2GenuineCentralExactUpper`.
-/
structure C2ResolventNonCancellationExactGenuineCentralLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  scale : C2ExpandedScalarScaleData
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffScale s
  horizontal : C2ExpandedHorizontalLayerBudget
    coreCutoff horizontalConstant horizontalScale horizontalRatio s
  seed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s
  cutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale
        (c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0

theorem C2ResolventNonCancellationExactGenuineCentralLocalData.ofCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      tiltConstant s / tiltScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤
      cutoffConstant s)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact {
    scale := hscale
    horizontal := hhorizontal
    seed := hseed
    cutoff := hcutoff
    dominance :=
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
        (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
        (coreCutoff := coreCutoff)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        (residualUpper := c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
        hoff hscale.tiltScale_pos hscale.tiltConstant_nonneg hseed
        hscale.horizontalScale_pos hscale.horizontalConstant_nonneg
        hscale.horizontalRatio_nonneg hscale.horizontalRatio_lt_one
        hhorizontal.layer_bound hdominance
  }

theorem C2ResolventNonCancellationExactGenuineCentralLocalData.of_majorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectMajorant : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      tiltConstant s / tiltScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤
      cutoffConstant s)
    (hmajorant :
      c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  apply C2ResolventNonCancellationExactGenuineCentralLocalData.ofCombinedResidualDominance
    hoff hscale hhorizontal hseed hcutoff
  exact lt_of_le_of_lt
    (by
      simpa [add_comm] using
        add_le_add_right hmajorant
          (c2ExpandedQuartetResidualUpper
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale s))
    hdominance

theorem C2ExpandedScalarLocalBulkData.toResolventNonCancellationExactGenuineCentralLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      tiltConstant s / tiltScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤
      cutoffConstant s)
    (hdominance :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact {
    scale := data.scale
    horizontal := data.horizontal
    seed := hseed
    cutoff := hcutoff
    dominance := hdominance
  }

theorem C2ResolventNonCancellationExactGenuineCentralLocalData.toGenuineCentralLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ResolventNonCancellationGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale c2GenuineCentralExactUpper s := by
  exact {
    scale := hs.scale
    horizontal := hs.horizontal
    seed := hs.seed
    cutoff := hs.cutoff
    genuine := c2GenuineCentralBound_exact s
    dominance := hs.dominance
  }

theorem C2ResolventNonCancellationExactGenuineCentralLocalData.nonvanishing
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    {s : ℂ} (hoff : offCriticalStrip s)
    (hs : C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_exactGenuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation hoff hs.scale.tiltScale_pos hs.scale.tiltConstant_nonneg hs.seed
      hs.scale.horizontalScale_pos hs.scale.horizontalConstant_nonneg
      hs.scale.horizontalRatio_nonneg hs.scale.horizontalRatio_lt_one
      hs.horizontal.layer_bound hs.scale.cutoffScale_pos hs.cutoff
      hs.dominance

theorem
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationExactGenuineCentralMiddleRegionWithBounds
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
      C2ResolventNonCancellationExactGenuineCentralLocalData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralExactUpper)
      continuation
      (fun _ hs => (hmiddle hs).toGenuineCentralLocalData)

theorem
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationExactGenuineCentralMiddleRegionWithBounds
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
      C2ResolventNonCancellationExactGenuineCentralLocalData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralExactUpper)
      continuation
      (fun _ hs => (hmiddle hs).toGenuineCentralLocalData)

/--
Middle-strip package for the exact resolvent non-cancellation fallback route. This bundles
the continuation data together with the pointwise exact local certificate.
-/
structure C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  continuation : GenuineFInfiniteContinuationData
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion
      (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
        (coreCutoff := coreCutoff) (K := K) (M := M)
        continuation
        (GenuineFInfiniteNearAxisData.of_continuation continuation))
      (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
        (coreCutoff := coreCutoff) (K := K) (M := M)) →
    C2ResolventNonCancellationExactGenuineCentralLocalData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem offCriticalStripNonvanishing_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndResolventNonCancellationExactGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      data.continuation
      (fun _ hs => data.middle_local hs)

theorem mathlibRiemannHypothesis_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndResolventNonCancellationExactGenuineCentralMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      data.continuation
      (fun _ hs => data.middle_local hs)

def C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegion
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  continuation := continuation
  middle_local := fun _ hs =>
    (hmiddle hs).toResolventNonCancellationExactGenuineCentralLocalData
      (hseed hs) (hcutoff hs) (hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralBound
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegion
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        continuation hmiddle hseed hcutoff hdominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralBound
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegion
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        continuation hmiddle hseed hcutoff hdominance)

def C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionCombinedResidualDominance
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  continuation := continuation
  middle_local := fun _ hs =>
    {
      scale := (hmiddle hs).scale
      horizontal := (hmiddle hs).horizontal
      seed := hseed hs
      cutoff := hcutoff hs
      dominance :=
        c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
          (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
          (coreCutoff := coreCutoff)
          (tiltConstant := tiltConstant) (tiltScale := tiltScale)
          (horizontalConstant := horizontalConstant)
          (horizontalScale := horizontalScale)
          (horizontalRatio := horizontalRatio)
          (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
          (residualUpper := c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
          hs.1 (hmiddle hs).scale.tiltScale_pos
          (hmiddle hs).scale.tiltConstant_nonneg (hseed hs)
          (hmiddle hs).scale.horizontalScale_pos
          (hmiddle hs).scale.horizontalConstant_nonneg
          (hmiddle hs).scale.horizontalRatio_nonneg
          (hmiddle hs).scale.horizontalRatio_lt_one
          (hmiddle hs).horizontal.layer_bound (hdominance hs)
    }

def C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionMajorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectMajorant : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    C2ResolventNonCancellationExactGenuineCentralMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  continuation := continuation
  middle_local := fun _ hs =>
    C2ResolventNonCancellationExactGenuineCentralLocalData.of_majorantCombinedResidualDominance
      hs.1 (hmiddle hs).scale (hmiddle hs).horizontal
      (hseed hs) (hcutoff hs) (hmajorant hs) (hdominance hs)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralCombinedResidualDominance
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        continuation hmiddle hseed hcutoff hdominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralCombinedResidualDominance
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
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
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        continuation hmiddle hseed hcutoff hdominance)

theorem
    offCriticalStripNonvanishing_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralMajorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectMajorant : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionMajorantCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        (centralDefectMajorant := centralDefectMajorant)
        continuation hmiddle hseed hcutoff hmajorant hdominance)

theorem
    mathlibRiemannHypothesis_of_continuationAndExpandedScalarMiddleRegion_of_exactGenuineCentralMajorantCombinedResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectMajorant : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
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
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hmajorant : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CentralDefectTriangleUpper
          c2GenuineCentralExactUpper
          c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
        centralDefectMajorant s)
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
        centralDefectMajorant s <
      c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_resolventNonCancellationExactGenuineCentralMiddleRegionData
      (C2ResolventNonCancellationExactGenuineCentralMiddleRegionData.ofContinuationAndExpandedScalarMiddleRegionMajorantCombinedResidualDominance
        (coreCutoff := coreCutoff) (K := K) (M := M)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        (centralDefectMajorant := centralDefectMajorant)
        continuation hmiddle hseed hcutoff hmajorant hdominance)

end C2
