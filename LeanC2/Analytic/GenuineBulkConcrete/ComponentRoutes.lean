import LeanC2.Analytic.GenuineBulkConcrete.ExpandedScalar

namespace C2

/--
Pointwise local data for the quartet-component resolvent route with an external
off-axis odd-truncation budget.
-/
structure C2QuartetComponentTruncationLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  continued_vertical_bound :
    C2ContinuedVerticalResidualBound K M continuedVerticalUpper s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  truncation_budget :
    C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      continuedVerticalUpper
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

theorem C2QuartetComponentTruncationLocalData.mem_componentRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2QuartetComponentTruncationLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M continuedVerticalUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact
    C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates.of_truncationBounds
      data.offCritical
      data.tiltScale_pos
      data.tiltConstant_nonneg
      data.continued_vertical_bound
      data.horizontalScale_pos
      data.horizontalConstant_nonneg
      data.horizontalRatio_nonneg
      data.horizontalRatio_lt_one
      data.truncation_budget
      data.balancing_seed_factor_scaled_bound
      data.cutoffScale_pos
      data.cutoff_scaled_bound
      data.quartet_dominance

/--
Regional middle-strip package for the quartet-component route with external
odd-truncation data.
-/
structure C2QuartetComponentTruncationMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2QuartetComponentTruncationLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem offCriticalStripNonvanishing_of_quartetComponentTruncationMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2QuartetComponentTruncationMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_quartetComponentMiddleRegion
    (continuedVerticalUpper := continuedVerticalUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    data.near data.edge (fun _ hs => (data.middle_local hs).mem_componentRegion)

theorem mathlibRiemannHypothesis_of_quartetComponentTruncationMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2QuartetComponentTruncationMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_quartetComponentMiddleRegion
    (continuedVerticalUpper := continuedVerticalUpper)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    data.near data.edge (fun _ hs => (data.middle_local hs).mem_componentRegion)


theorem offCriticalStripNonvanishing_of_continuationAndQuartetComponentTruncationLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
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
      C2QuartetComponentTruncationLocalData
        coreCutoff K M continuedVerticalUpper oddTruncationUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
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
  exact offCriticalStripNonvanishing_of_quartetComponentTruncationMiddleRegionData {
    near := nearC2
    edge := edgeC2
    middle_local := fun _ hs => hmiddle hs
  }


theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentTruncationLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
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
      C2QuartetComponentTruncationLocalData
        coreCutoff K M continuedVerticalUpper oddTruncationUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetComponentTruncationMiddleRegionData {
    near := nearC2
    edge := edgeC2
    middle_local := fun _ hs => hmiddle hs
  }

/--
Pointwise quartet-component package in the notation of the resolvent note: the
combined continued-vertical plus horizontal defect is supplied as a single
`C_R / X` budget, using `cutoffScale` as the cutoff parameter `X`.
-/
structure C2QuartetComponentResolventNoteLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (resolventConstant : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  continued_vertical_bound :
    C2ContinuedVerticalResidualBound K M continuedVerticalUpper s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  truncation_budget :
    C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s
  cutoffScale_pos : 0 < cutoffScale s
  resolvent_note_bound :
    continuedVerticalUpper s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s ≤
      c2ResolventNoteUpper resolventConstant cutoffScale s
  resolvent_note_scaled_bound :
    (c2ResolventNoteUpper resolventConstant cutoffScale s *
        (1 + ‖q s‖)) *
      tiltScale s ≤ tiltConstant s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

theorem C2QuartetComponentResolventNoteLocalData.of_noteBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale_pos : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hvertical : C2ContinuedVerticalResidualBound K M continuedVerticalUpper s)
    (hhorizontalScale_pos : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (htruncation : C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s)
    (hcutoffScale_pos : 0 < cutoffScale s)
    (hresolvent_note_bound :
      continuedVerticalUpper s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s ≤
        c2ResolventNoteUpper resolventConstant cutoffScale s)
    (hresolvent_note_scaled :
      (c2ResolventNoteUpper resolventConstant cutoffScale s *
          (1 + ‖q s‖)) *
        tiltScale s ≤ tiltConstant s)
    (hcutoff :
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
          cutoffScale s ≤ cutoffConstant s)
    (hdominance :
      c2QuartetBulkGUpper
          (c2BulkGUpper
            (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
            (c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio)) s +
        c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    C2QuartetComponentResolventNoteLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact {
    offCritical := hoff
    tiltScale_pos := htiltScale_pos
    tiltConstant_nonneg := htiltConstant_nonneg
    continued_vertical_bound := hvertical
    horizontalScale_pos := hhorizontalScale_pos
    horizontalConstant_nonneg := hhorizontalConstant_nonneg
    horizontalRatio_nonneg := hhorizontalRatio_nonneg
    horizontalRatio_lt_one := hhorizontalRatio_lt_one
    truncation_budget := htruncation
    cutoffScale_pos := hcutoffScale_pos
    resolvent_note_bound := hresolvent_note_bound
    resolvent_note_scaled_bound := hresolvent_note_scaled
    cutoff_scaled_bound := hcutoff
    quartet_dominance := hdominance
  }

theorem C2QuartetComponentResolventNoteLocalData.toTruncationLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2QuartetComponentResolventNoteLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2QuartetComponentTruncationLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  have hseed :
      C2BalancingSeedFactorScaledBound
        continuedVerticalUpper
        (c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio)
        (fun s => 1 + ‖q s‖)
        tiltConstant tiltScale s :=
    C2BalancingSeedFactorScaledBound.of_noteUpper
      (show 0 ≤ 1 + ‖q s‖ by positivity)
      (le_of_lt data.tiltScale_pos)
      data.resolvent_note_bound
      data.resolvent_note_scaled_bound
  exact {
    offCritical := data.offCritical
    tiltScale_pos := data.tiltScale_pos
    tiltConstant_nonneg := data.tiltConstant_nonneg
    continued_vertical_bound := data.continued_vertical_bound
    horizontalScale_pos := data.horizontalScale_pos
    horizontalConstant_nonneg := data.horizontalConstant_nonneg
    horizontalRatio_nonneg := data.horizontalRatio_nonneg
    horizontalRatio_lt_one := data.horizontalRatio_lt_one
    truncation_budget := data.truncation_budget
    balancing_seed_factor_scaled_bound := hseed
    cutoffScale_pos := data.cutoffScale_pos
    cutoff_scaled_bound := data.cutoff_scaled_bound
    quartet_dominance := data.quartet_dominance
  }

theorem C2QuartetComponentResolventNoteLocalData.mem_componentRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (data : C2QuartetComponentResolventNoteLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M continuedVerticalUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact data.toTruncationLocalData.mem_componentRegion

/--
Regional middle-strip package for the resolvent-note presentation of the
quartet-component route.
-/
structure C2QuartetComponentResolventNoteMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (resolventConstant : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2QuartetComponentResolventNoteLocalData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

def C2QuartetComponentResolventNoteMiddleRegionData.toTruncationMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2QuartetComponentResolventNoteMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2QuartetComponentTruncationMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  middle_local := fun {_} hs =>
    (data.middle_local hs).toTruncationLocalData

theorem offCriticalStripNonvanishing_of_quartetComponentResolventNoteMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2QuartetComponentResolventNoteMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_quartetComponentTruncationMiddleRegionData
    data.toTruncationMiddleRegionData

theorem mathlibRiemannHypothesis_of_quartetComponentResolventNoteMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2QuartetComponentResolventNoteMiddleRegionData
      coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_quartetComponentTruncationMiddleRegionData
    data.toTruncationMiddleRegionData


theorem offCriticalStripNonvanishing_of_continuationAndQuartetComponentResolventNoteLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
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
      C2QuartetComponentResolventNoteLocalData
        coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
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
  exact
    offCriticalStripNonvanishing_of_quartetComponentResolventNoteMiddleRegionData {
      near := nearC2
      edge := edgeC2
      middle_local := fun _ hs => hmiddle hs
    }


theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentResolventNoteLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
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
      C2QuartetComponentResolventNoteLocalData
        coreCutoff K M continuedVerticalUpper oddTruncationUpper resolventConstant
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact mathlibRiemannHypothesis_of_quartetComponentResolventNoteMiddleRegionData {
    near := nearC2
    edge := edgeC2
    middle_local := fun _ hs => hmiddle hs
  }


theorem offCriticalStripNonvanishing_of_continuationAndQuartetComponentResolventNoteBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
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
    (hcutoffScale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < cutoffScale s)
    (hresolvent_note_bound : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      continuedVerticalUpper s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s ≤
        c2ResolventNoteUpper resolventConstant cutoffScale s)
    (hresolvent_note_scaled : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ResolventNoteUpper resolventConstant cutoffScale s *
          (1 + ‖q s‖)) *
        tiltScale s ≤ tiltConstant s)
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
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndQuartetComponentResolventNoteLocalData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedVerticalUpper := continuedVerticalUpper)
      (oddTruncationUpper := oddTruncationUpper)
      (resolventConstant := resolventConstant)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation
      (fun _ hs =>
        C2QuartetComponentResolventNoteLocalData.of_noteBounds
          hs.1
          (htiltScale_pos hs)
          (htiltConstant_nonneg hs)
          (hvertical hs)
          (hhorizontalScale_pos hs)
          (hhorizontalConstant_nonneg hs)
          (hhorizontalRatio_nonneg hs)
          (hhorizontalRatio_lt_one hs)
          (htruncation hs)
          (hcutoffScale_pos hs)
          (hresolvent_note_bound hs)
          (hresolvent_note_scaled hs)
          (hcutoff hs)
          (hdominance hs))


theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentResolventNoteBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {resolventConstant : ℂ → ℝ}
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
    (hcutoffScale_pos : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      0 < cutoffScale s)
    (hresolvent_note_bound : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      continuedVerticalUpper s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s ≤
        c2ResolventNoteUpper resolventConstant cutoffScale s)
    (hresolvent_note_scaled : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      (c2ResolventNoteUpper resolventConstant cutoffScale s *
          (1 + ‖q s‖)) *
        tiltScale s ≤ tiltConstant s)
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
  exact
    mathlibRiemannHypothesis_of_continuationAndQuartetComponentResolventNoteLocalData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedVerticalUpper := continuedVerticalUpper)
      (oddTruncationUpper := oddTruncationUpper)
      (resolventConstant := resolventConstant)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation
      (fun _ hs =>
        C2QuartetComponentResolventNoteLocalData.of_noteBounds
          hs.1
          (htiltScale_pos hs)
          (htiltConstant_nonneg hs)
          (hvertical hs)
          (hhorizontalScale_pos hs)
          (hhorizontalConstant_nonneg hs)
          (hhorizontalRatio_nonneg hs)
          (hhorizontalRatio_lt_one hs)
          (htruncation hs)
          (hcutoffScale_pos hs)
          (hresolvent_note_bound hs)
          (hresolvent_note_scaled hs)
          (hcutoff hs)
          (hdominance hs))

/--
Concrete resolvent-note constant for the quartet-component route, using the
exact continued-vertical upper and the scale match `horizontalScale = X`.
-/
noncomputable def c2QuartetComponentExactScaleMatchedResolventConstant
    (K M : ℕ)
    (horizontalConstant cutoffScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  c2ResolventNoteScaleMatchedConstant
    (c2ContinuedVerticalResidualExactUpper K M)
    horizontalConstant cutoffScale horizontalRatio

theorem c2ResolventNoteUpper_eq_quartetComponentExactScaleMatched_of_pos
    {K M : ℕ}
    {horizontalConstant cutoffScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hcutoffScale_pos : 0 < cutoffScale s) :
    c2ResolventNoteUpper
        (c2QuartetComponentExactScaleMatchedResolventConstant
          K M horizontalConstant cutoffScale horizontalRatio)
        cutoffScale s =
      c2ContinuedVerticalResidualExactUpper K M s +
        c2HorizontalRegularizedUpper
          horizontalConstant cutoffScale horizontalRatio s := by
  simpa [c2QuartetComponentExactScaleMatchedResolventConstant] using
    (c2ResolventNoteUpper_eq_scaleMatched_of_pos
      (continuedVerticalUpper := c2ContinuedVerticalResidualExactUpper K M)
      (horizontalConstant := horizontalConstant)
      (cutoffScale := cutoffScale)
      (horizontalRatio := horizontalRatio)
      (s := s)
      hcutoffScale_pos)


theorem
  offCriticalStripNonvanishing_of_continuationAndQuartetComponentExactScaleMatchedResolventBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalRatio
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
        horizontalConstant cutoffScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2BalancingSeedFactorScaledBound
        (c2ContinuedVerticalResidualExactUpper K M)
        (c2HorizontalRegularizedUpper
          horizontalConstant cutoffScale horizontalRatio)
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
              horizontalConstant cutoffScale horizontalRatio)) s +
        c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndQuartetComponentResolventNoteBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedVerticalUpper := c2ContinuedVerticalResidualExactUpper K M)
      (oddTruncationUpper := oddTruncationUpper)
      (resolventConstant :=
        c2QuartetComponentExactScaleMatchedResolventConstant
          K M horizontalConstant cutoffScale horizontalRatio)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := cutoffScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation
      htiltScale_pos
      htiltConstant_nonneg
      (fun {s} _ => c2ContinuedVerticalResidualBound_exact K M s)
      hcutoffScale_pos
      hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg
      hhorizontalRatio_lt_one
      htruncation
      hcutoffScale_pos
      (fun {s} hs => by
        rw [c2ResolventNoteUpper_eq_quartetComponentExactScaleMatched_of_pos
          (K := K) (M := M)
          (horizontalConstant := horizontalConstant)
          (cutoffScale := cutoffScale)
          (horizontalRatio := horizontalRatio)
          (s := s)
          (hcutoffScale_pos hs)])
      (fun {s} hs => by
        simpa [c2ResolventNoteUpper_eq_quartetComponentExactScaleMatched_of_pos
          (K := K) (M := M)
          (horizontalConstant := horizontalConstant)
          (cutoffScale := cutoffScale)
          (horizontalRatio := horizontalRatio)
          (s := s)
          (hcutoffScale_pos hs)] using hseed hs)
      hcutoff
      hdominance


theorem mathlibRiemannHypothesis_of_continuationAndQuartetComponentExactScaleMatchedResolventBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalRatio
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
        horizontalConstant cutoffScale horizontalRatio s)
    (hseed : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      C2BalancingSeedFactorScaledBound
        (c2ContinuedVerticalResidualExactUpper K M)
        (c2HorizontalRegularizedUpper
          horizontalConstant cutoffScale horizontalRatio)
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
              horizontalConstant cutoffScale horizontalRatio)) s +
        c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndQuartetComponentResolventNoteBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (continuedVerticalUpper := c2ContinuedVerticalResidualExactUpper K M)
      (oddTruncationUpper := oddTruncationUpper)
      (resolventConstant :=
        c2QuartetComponentExactScaleMatchedResolventConstant
          K M horizontalConstant cutoffScale horizontalRatio)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := cutoffScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation
      htiltScale_pos
      htiltConstant_nonneg
      (fun {s} _ => c2ContinuedVerticalResidualBound_exact K M s)
      hcutoffScale_pos
      hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg
      hhorizontalRatio_lt_one
      htruncation
      hcutoffScale_pos
      (fun {s} hs => by
        rw [c2ResolventNoteUpper_eq_quartetComponentExactScaleMatched_of_pos
          (K := K) (M := M)
          (horizontalConstant := horizontalConstant)
          (cutoffScale := cutoffScale)
          (horizontalRatio := horizontalRatio)
          (s := s)
          (hcutoffScale_pos hs)])
      (fun {s} hs => by
        simpa [c2ResolventNoteUpper_eq_quartetComponentExactScaleMatched_of_pos
          (K := K) (M := M)
          (horizontalConstant := horizontalConstant)
          (cutoffScale := cutoffScale)
          (horizontalRatio := horizontalRatio)
          (s := s)
          (hcutoffScale_pos hs)] using hseed hs)
      hcutoff
      hdominance

theorem offCriticalStripNonvanishing_of_canonicalClosedMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  let bulk :=
    c2OddTailContinuedBalancingSeedBulkQuartetConcreteBulkRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
  have hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulk.bulkRegion ∨ s ∈ edge.edgeRegion := by
    intro s hs
    by_cases hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius
    · exact Or.inl hnear
    · by_cases hedge : s ∈ edge.edgeRegion
      · exact Or.inr <| Or.inr hedge
      · exact Or.inr <| Or.inl <|
          c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_canonicalClosedRegion
            (hmiddle ⟨hs, hnear, hedge⟩)
  simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData]
    using offCriticalStripNonvanishing_of_coverData
      (OffCriticalCoverData.ofNearBulkRegionEdge
        near.toNearAxisRouteData
        bulk.bulk
        edge.toEdgeRouteData
        (by
          simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData]
            using bulk.F_eq)
        rfl
        hcover)

theorem mathlibRiemannHypothesis_of_canonicalClosedMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_quartetClosedMiddleRegion
    (rectangularUpper := c2RectangularGenuineDirectBracketUpper K M)
    (centralUpper := c2ContinuedCentralExactUpper)
    near edge
    (fun _ hs =>
      c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_canonicalClosedRegion
        (hmiddle hs))

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedMiddleRegion
    (tiltConstant := c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio)
    (tiltScale := fun _ => (1 : ℝ))
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := c2CanonicalClosedCutoffConstant K M)
    (cutoffScale := fun _ => (1 : ℝ))
    near edge
    (fun _ hs =>
      c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosed_mem_of_scaledRegion
        (hmiddle hs))

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedMiddleRegion
    (tiltConstant := c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio)
    (tiltScale := fun _ => (1 : ℝ))
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := c2CanonicalClosedCutoffConstant K M)
    (cutoffScale := fun _ => (1 : ℝ))
    near edge
    (fun _ hs =>
      c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosed_mem_of_scaledRegion
        (hmiddle hs))

end C2
