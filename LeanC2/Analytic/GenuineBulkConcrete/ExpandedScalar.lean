import LeanC2.Analytic.GenuineBulkConcrete.ConcreteEstimates

namespace C2

structure C2ExpandedScalarCoverData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∨
      s ∈ edge.edgeRegion

noncomputable def C2ExpandedScalarCoverData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (_data : C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M :=
  c2ExpandedScalarBulkRegionData
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def C2ExpandedScalarCoverData.toOffCriticalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkRegionEdge
    data.near.toNearAxisRouteData
    data.toBulkRegionData.bulk
    data.edge.toEdgeRouteData
    (by
      simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData]
        using data.toBulkRegionData.F_eq)
    rfl
    (by
      change ∀ s : ℂ, offCriticalStrip s →
        s ∈ nearAxisRegion riemannZeta data.near.near_axis.radius ∨
          s ∈ c2ExpandedExactZetaScalarRegion
            coreCutoff K M
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale ∨
          s ∈ data.edge.edgeRegion
      exact data.cover)

theorem offCriticalStripNonvanishing_of_expandedScalarCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  simpa [C2ExpandedScalarCoverData.toOffCriticalCoverData,
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem mathlibRiemannHypothesis_of_expandedScalarCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_expandedScalarCover
    data.near data.edge data.cover

theorem
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {bulkRegion : Set ℂ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hsubset : ∀ ⦃s : ℂ⦄, s ∈ bulkRegion →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulkRegion ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteCover
      near edge (c2LiftBulkCover_of_subset hsubset cover)

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetExactCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_exactRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetTriangleCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_triangleRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetClosedCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
          coreCutoff K M rectangularUpper centralUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
          coreCutoff K M rectangularUpper centralUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_closedRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_zetaDepthCoreCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper oddFactorUpper zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
          coreCutoff K M depthUpper coreUpper oddFactorUpper zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
          coreCutoff K M depthUpper coreUpper oddFactorUpper zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_zetaDepthCoreRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitFiniteCoreCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
          coreCutoff K M zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
          coreCutoff K M zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitFiniteCoreRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitScalarCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
          coreCutoff K M zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
          coreCutoff K M zetaUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_explicitScalarExactZetaCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarExactZetaRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_expandedExactZetaCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedExactZetaRegion hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_expandedDominanceCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedExactZetaDominanceRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  refine
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (bulkRegion :=
        c2ExpandedExactZetaDominanceRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale)
      near edge ?_ cover
  intro s hs
  exact c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedDominanceRegion hs

/-- Local sign and scale hypotheses used by the expanded scalar bulk region. -/
structure C2ExpandedScalarScaleData
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  cutoffScale_pos : 0 < cutoffScale s

/-- Local horizontal-layer budget for the expanded scalar bulk region. -/
structure C2ExpandedHorizontalLayerBudget
    (coreCutoff : ℕ → ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  layer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j

/--
External odd-truncation budget for the off-axis horizontal channel.
This isolates the missing analytic input before converting it into the geometric
layer bound used throughout the canonical closed/scaled route.
-/
structure C2ExpandedOddTruncationBudget
    (coreCutoff : ℕ → ℕ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  truncation_bound : ∀ j : ℕ,
    ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddTruncationUpper s j ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j

theorem C2ExpandedOddTruncationBudget.toHorizontalLayerBudget
    {coreCutoff : ℕ → ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s) :
    C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    layer_bound :=
      c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
        data.truncation_bound data.horizontal_budget
  }

theorem C2ExpandedHorizontalLayerBudget.of_truncationBounds
    {coreCutoff : ℕ → ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (htruncation : ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j)
    (hhorizontal : ∀ j : ℕ,
      2 * ‖q s‖ ^ (j + 2) * oddTruncationUpper s j ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s :=
  C2ExpandedOddTruncationBudget.toHorizontalLayerBudget {
    truncation_bound := htruncation
    horizontal_budget := hhorizontal
  }

theorem C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates.of_truncationBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
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
    (hseed : C2BalancingSeedFactorScaledBound
      continuedVerticalUpper
      (c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s)
    (hcutoffScale_pos : 0 < cutoffScale s)
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
    C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates
      coreCutoff K M continuedVerticalUpper
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
    horizontalLayer_bound := htruncation.toHorizontalLayerBudget.layer_bound
    balancing_seed_factor_scaled_bound := hseed
    cutoffScale_pos := hcutoffScale_pos
    cutoff_scaled_bound := hcutoff
    quartet_dominance := hdominance
  }

/-- The three scalar inequalities left in the expanded exact-zeta bulk region. -/
structure C2ExpandedScalarMainInequalities
    (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  seed_scaled :
    C2ExpandedSeedScaledBound
      K M horizontalConstant horizontalScale horizontalRatio
      tiltConstant tiltScale s
  cutoff_scaled :
    C2ExpandedCutoffScaledBound K M cutoffConstant cutoffScale s
  dominance :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem C2ExpandedScalarMainInequalities.ofComponents
    {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hseed : C2ExpandedSeedScaledBound
      K M horizontalConstant horizontalScale horizontalRatio
      tiltConstant tiltScale s)
    (hcutoff : C2ExpandedCutoffScaledBound K M cutoffConstant cutoffScale s)
    (hdominance : C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedScalarMainInequalities
      K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  {
    seed_scaled := hseed
    cutoff_scaled := hcutoff
    dominance := hdominance
  }

theorem c2ExpandedExactZetaScalarEstimates_of_localData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hK : 2 ≤ K)
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hmain : C2ExpandedScalarMainInequalities
      K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedExactZetaScalarEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact {
    two_le_K := hK
    offCritical := hoff
    tiltScale_pos := hscale.tiltScale_pos
    tiltConstant_nonneg := hscale.tiltConstant_nonneg
    horizontalScale_pos := hscale.horizontalScale_pos
    horizontalConstant_nonneg := hscale.horizontalConstant_nonneg
    horizontalRatio_nonneg := hscale.horizontalRatio_nonneg
    horizontalRatio_lt_one := hscale.horizontalRatio_lt_one
    horizontalLayer_bound := hhorizontal.layer_bound
    seed_scaled_bound := hmain.seed_scaled
    cutoffScale_pos := hscale.cutoffScale_pos
    cutoff_scaled_bound := hmain.cutoff_scaled
    dominance := hmain.dominance
  }

theorem c2ExpandedExactZetaScalarRegion_mem_of_localData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hK : 2 ≤ K)
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hmain : C2ExpandedScalarMainInequalities
      K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2ExpandedExactZetaScalarEstimates_of_localData
    hK hoff hscale hhorizontal hmain

theorem c2ExpandedScalarBulkModel_nonvanishing_of_localData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hK : 2 ≤ K)
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hmain : C2ExpandedScalarMainInequalities
      K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedScalarRegion
    (c2ExpandedExactZetaScalarRegion_mem_of_localData
      hK hoff hscale hhorizontal hmain)

/-- Pointwise near/scalar-bulk/edge branch choice for the expanded scalar cover. -/
inductive C2ExpandedScalarCoverChoice
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (s : ℂ) : Prop where
  | nearAxis
      (hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius) :
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s
  | scalarBulk
      (hbulk : s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s
  | edgeRegion
      (hedge : s ∈ edge.edgeRegion) :
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s

theorem C2ExpandedScalarCoverChoice.toCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (choice : C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s) :
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∨
      s ∈ edge.edgeRegion := by
  rcases choice with hnear | hbulk | hedge
  · exact Or.inl hnear
  · exact Or.inr (Or.inl hbulk)
  · exact Or.inr (Or.inr hedge)

theorem C2ExpandedScalarCoverChoice.scalarBulk_of_localData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hK : 2 ≤ K)
    (hoff : offCriticalStrip s)
    (hscale : C2ExpandedScalarScaleData
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffScale s)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hmain : C2ExpandedScalarMainInequalities
      K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s :=
  C2ExpandedScalarCoverChoice.scalarBulk
    (c2ExpandedExactZetaScalarRegion_mem_of_localData
      hK hoff hscale hhorizontal hmain)

/-- A single pointwise package for the expanded scalar-bulk branch. -/
structure C2ExpandedScalarLocalBulkData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  scale : C2ExpandedScalarScaleData
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffScale s
  horizontal : C2ExpandedHorizontalLayerBudget
    coreCutoff horizontalConstant horizontalScale horizontalRatio s
  main : C2ExpandedScalarMainInequalities
    K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s

theorem C2ExpandedScalarLocalBulkData.toScalarEstimates
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
    C2ExpandedExactZetaScalarEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  c2ExpandedExactZetaScalarEstimates_of_localData
    data.two_le_K data.offCritical data.scale data.horizontal data.main

theorem C2ExpandedScalarLocalBulkData.mem_scalarRegion
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
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  data.toScalarEstimates

theorem C2ExpandedScalarLocalBulkData.nonvanishing
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
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2ExpandedScalarBulkModel_nonvanishing_of_localData
    data.two_le_K data.offCritical data.scale data.horizontal data.main

theorem C2ExpandedScalarLocalBulkData.concreteCutoff_scaled_bound_of_exactZetaCentralDefect
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
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          centralDefectUpper s) * cutoffScale s ≤
        cutoffConstant s) :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  have hcontinued :
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
        c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s :=
    c2ContinuedCutoff_norm_le_exactZetaScalar_of_offCriticalStrip
      K M data.two_le_K data.offCritical
  exact c2ConcreteCutoffError_scaled_bound_of_continued_and_centralDefect
    (hscale_nonneg := le_of_lt data.scale.cutoffScale_pos)
    (hcontinued := hcontinued)
    (hcentralDefect := hcentralDefect)
    (hscaled := hscaled)

theorem C2ExpandedScalarLocalBulkData.concreteCutoff_scaled_bound_of_splitAtOneUpper
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
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  have hcontinued :
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
        c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s :=
    c2ContinuedCutoff_norm_le_exactZetaScalar_of_offCriticalStrip
      K M data.two_le_K data.offCritical
  have hdefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        c2GenuineCentralSplitAtOneUpper genuineCentralUpper s :=
    c2CentralDefect_norm_le_splitAtOneUpper_of_exactZetaCentralDefect
      data.offCritical hcentralDefect hgenuineUpper
  exact c2ConcreteCutoffError_scaled_bound_of_continued_and_centralDefect
    (hscale_nonneg := le_of_lt data.scale.cutoffScale_pos)
    (hcontinued := hcontinued)
    (hcentralDefect := hdefect)
    (hscaled := hscaled)

theorem C2ExpandedScalarLocalBulkData.concreteCutoff_scaled_bound_of_splitAtOneDefectUpper
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
      (c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s +
          c2GenuineCentralSplitAtOneUpper genuineCentralUpper s) *
          cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  have hcontinued :
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
        c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s :=
    c2ContinuedCutoff_norm_le_exactZetaScalar_of_offCriticalStrip
      K M data.two_le_K data.offCritical
  exact c2ConcreteCutoffError_scaled_bound_of_continued_and_centralDefect
    (hscale_nonneg := le_of_lt data.scale.cutoffScale_pos)
    (hcontinued := hcontinued)
    (hcentralDefect := hdefect)
    (hscaled := hscaled)

theorem C2ExpandedScalarLocalBulkData.ofScalarEstimates
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : C2ExpandedExactZetaScalarEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    scale := {
      tiltScale_pos := hs.tiltScale_pos
      tiltConstant_nonneg := hs.tiltConstant_nonneg
      horizontalScale_pos := hs.horizontalScale_pos
      horizontalConstant_nonneg := hs.horizontalConstant_nonneg
      horizontalRatio_nonneg := hs.horizontalRatio_nonneg
      horizontalRatio_lt_one := hs.horizontalRatio_lt_one
      cutoffScale_pos := hs.cutoffScale_pos
    }
    horizontal := {
      layer_bound := hs.horizontalLayer_bound
    }
    main := {
      seed_scaled := hs.seed_scaled_bound
      cutoff_scaled := hs.cutoff_scaled_bound
      dominance := hs.dominance
    }
  }

theorem C2ExpandedScalarLocalBulkData.of_mem_scalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  C2ExpandedScalarLocalBulkData.ofScalarEstimates hs

theorem C2ExpandedScalarLocalBulkData.of_expandedDominanceEstimates
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : C2ExpandedExactZetaDominanceEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  refine {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    scale := {
      tiltScale_pos := hs.tiltScale_pos
      tiltConstant_nonneg := hs.tiltConstant_nonneg
      horizontalScale_pos := hs.horizontalScale_pos
      horizontalConstant_nonneg := hs.horizontalConstant_nonneg
      horizontalRatio_nonneg := hs.horizontalRatio_nonneg
      horizontalRatio_lt_one := hs.horizontalRatio_lt_one
      cutoffScale_pos := hs.cutoffScale_pos
    }
    horizontal := {
      layer_bound := hs.horizontalLayer_bound
    }
    main := {
      seed_scaled := by
        simpa [C2ExpandedSeedScaledBound, c2ExpandedSeedScaledLeft] using
          hs.balancing_seed_factor_scaled_bound
      cutoff_scaled := by
        simpa [C2ExpandedCutoffScaledBound, c2ExpandedCutoffScaledLeft] using
          hs.cutoff_closed_scaled_bound
      dominance := hs.dominance
    }
  }

theorem C2ExpandedScalarLocalBulkData.of_mem_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  C2ExpandedScalarLocalBulkData.of_expandedDominanceEstimates hs

theorem c2ExpandedDominance_mem_of_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    dominance := by
      simpa [C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper,
        c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
        c2ExpandedQuartetK2Margin] using hs.quartet_dominance
  }

theorem C2ExpandedScalarLocalBulkData.of_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  C2ExpandedScalarLocalBulkData.of_mem_expandedDominanceRegion
    (c2ExpandedDominance_mem_of_mem_expandedExactZetaRegion hs)

theorem c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  (C2ExpandedScalarLocalBulkData.of_mem_expandedDominanceRegion hs).mem_scalarRegion

theorem c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedDominanceRegion
    (c2ExpandedDominance_mem_of_mem_expandedExactZetaRegion hs)

theorem C2ExpandedScalarLocalBulkData.of_mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  C2ExpandedScalarLocalBulkData.of_mem_expandedExactZetaRegion
    (c2ExplicitScalarExactZeta_mem_expandedExactZetaRegion hs)

theorem c2ExpandedExactZetaScalarRegion_mem_of_mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  (C2ExpandedScalarLocalBulkData.of_mem_explicitScalarExactZetaRegion hs).mem_scalarRegion

theorem C2ExpandedScalarLocalBulkData.mem_canonicalClosedScaledRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ)) s) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaled_mem_of_expandedScalarRegion
    data.mem_scalarRegion

theorem C2ExpandedScalarCoverChoice.nearAxis_of_mem
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius) :
    C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s :=
  C2ExpandedScalarCoverChoice.nearAxis hnear

theorem C2ExpandedScalarCoverChoice.scalarBulk_of_localBulkData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s :=
  C2ExpandedScalarCoverChoice.scalarBulk data.mem_scalarRegion

theorem C2ExpandedScalarCoverChoice.edgeRegion_of_mem
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hedge : s ∈ edge.edgeRegion) :
    C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s :=
  C2ExpandedScalarCoverChoice.edgeRegion hedge

noncomputable def C2ExpandedScalarCoverData.ofLocalChoice
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (choose : ∀ s : ℂ, offCriticalStrip s →
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s) :
    C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := near
  edge := edge
  cover := by
    intro s hs
    exact C2ExpandedScalarCoverChoice.toCover (choose s hs)

theorem offCriticalStripNonvanishing_of_expandedScalarLocalChoice
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (choose : ∀ s : ℂ, offCriticalStrip s →
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofLocalChoice near edge choose)

theorem mathlibRiemannHypothesis_of_expandedScalarLocalChoice
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (choose : ∀ s : ℂ, offCriticalStrip s →
      C2ExpandedScalarCoverChoice
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale near edge s) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofLocalChoice near edge choose)

/--
Abstract regional decomposition for the expanded scalar cover.

The three branches need not be given directly as the canonical near/scalar/edge regions.
It suffices to provide subregions that feed those branches.
-/
structure C2ExpandedScalarChoiceRegions
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M) where
  nearRegion : Set ℂ
  localBulkRegion : Set ℂ
  edgeRegion : Set ℂ
  near_subset : ∀ ⦃s : ℂ⦄, s ∈ nearRegion →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius
  localBulk_data : ∀ ⦃s : ℂ⦄, s ∈ localBulkRegion →
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s
  edge_subset : ∀ ⦃s : ℂ⦄, s ∈ edgeRegion → s ∈ edge.edgeRegion

def C2ExpandedScalarChoiceRegions.combinedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    (data : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge) : Set ℂ :=
  data.nearRegion ∪ data.localBulkRegion ∪ data.edgeRegion

theorem C2ExpandedScalarChoiceRegions.toChoice
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    (data : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge)
    {s : ℂ}
    (hs : s ∈ data.combinedRegion) :
    C2ExpandedScalarCoverChoice
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge s := by
  rcases hs with hleft | hedge
  · rcases hleft with hnear | hbulk
    · exact C2ExpandedScalarCoverChoice.nearAxis (data.near_subset hnear)
    · exact C2ExpandedScalarCoverChoice.scalarBulk_of_localBulkData
        (data.localBulk_data hbulk)
  · exact C2ExpandedScalarCoverChoice.edgeRegion_of_mem (data.edge_subset hedge)

theorem C2ExpandedScalarChoiceRegions.toCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    (data : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge)
    {s : ℂ}
    (hs : s ∈ data.combinedRegion) :
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∨
      s ∈ edge.edgeRegion := by
  exact C2ExpandedScalarCoverChoice.toCover (data.toChoice hs)

noncomputable def C2ExpandedScalarCoverData.ofChoiceRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (regions : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge)
    (cover : ∀ s : ℂ, offCriticalStrip s → s ∈ regions.combinedRegion) :
    C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  C2ExpandedScalarCoverData.ofLocalChoice near edge
    (fun s hs => regions.toChoice (cover s hs))

theorem offCriticalStripNonvanishing_of_expandedScalarChoiceRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (regions : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge)
    (cover : ∀ s : ℂ, offCriticalStrip s → s ∈ regions.combinedRegion) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofChoiceRegions near edge regions cover)

theorem mathlibRiemannHypothesis_of_expandedScalarChoiceRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (regions : C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge)
    (cover : ∀ s : ℂ, offCriticalStrip s → s ∈ regions.combinedRegion) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofChoiceRegions near edge regions cover)

/-- Concrete local-bulk region: points carrying the full local scalar-bulk data package. -/
def c2ExpandedScalarLocalBulkRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2ExpandedScalarLocalBulkData
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem C2ExpandedScalarLocalBulkData.mem_localBulkRegion
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
    s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  simpa [c2ExpandedScalarLocalBulkRegion] using data

theorem c2ExpandedExactZetaScalarRegion_mem_of_mem_localBulkRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  simpa [c2ExpandedScalarLocalBulkRegion] using
    (show C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s from hs).mem_scalarRegion

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_localBulkRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  simpa [c2ExpandedScalarLocalBulkRegion] using
    (show C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s from hs).nonvanishing

theorem c2ExpandedScalarLocalBulkRegion_mem_of_mem_scalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  (C2ExpandedScalarLocalBulkData.of_mem_scalarRegion hs).mem_localBulkRegion

theorem c2ExpandedScalarLocalBulkRegion_eq_scalarRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2ExpandedScalarLocalBulkRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale =
      c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale := by
  ext s
  constructor
  · exact c2ExpandedExactZetaScalarRegion_mem_of_mem_localBulkRegion
  · exact c2ExpandedScalarLocalBulkRegion_mem_of_mem_scalarRegion

/-- Canonical regional decomposition: near-axis, local scalar-bulk data, and edge. -/
def C2ExpandedScalarChoiceRegions.canonical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M) :
    C2ExpandedScalarChoiceRegions
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale near edge where
  nearRegion := nearAxisRegion riemannZeta near.near_axis.radius
  localBulkRegion :=
    c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
  edgeRegion := edge.edgeRegion
  near_subset := by
    intro s hs
    exact hs
  localBulk_data := by
    intro s hs
    simpa [c2ExpandedScalarLocalBulkRegion] using hs
  edge_subset := by
    intro s hs
    exact hs

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_nearAxis
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ nearAxisRegion riemannZeta near.near_axis.radius) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  exact Or.inl <| Or.inl hs

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_localBulkData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (data : C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  exact Or.inl <| Or.inr data.mem_localBulkRegion

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_mem_localBulkRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  exact Or.inl <| Or.inr hs

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_scalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  exact
    C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_mem_localBulkRegion
      (c2ExpandedScalarLocalBulkRegion_mem_of_mem_scalarRegion hs)

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_edge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ edge.edgeRegion) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  exact Or.inr hs

theorem C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2ExpandedScalarLocalBulkRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∨
      s ∈ edge.edgeRegion) :
    s ∈ (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge).combinedRegion := by
  rcases hs with hnear | hrest
  · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_nearAxis hnear
  · rcases hrest with hbulk | hedge
    · exact
        C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_mem_localBulkRegion hbulk
    · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_edge hedge

noncomputable def C2ExpandedScalarCoverData.ofCanonicalRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ (C2ExpandedScalarChoiceRegions.canonical
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        near edge).combinedRegion) :
    C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  C2ExpandedScalarCoverData.ofChoiceRegions near edge
    (C2ExpandedScalarChoiceRegions.canonical
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      near edge)
    cover

theorem offCriticalStripNonvanishing_of_expandedScalarCanonicalRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ (C2ExpandedScalarChoiceRegions.canonical
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        near edge).combinedRegion) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofCanonicalRegions near edge cover)

theorem mathlibRiemannHypothesis_of_expandedScalarCanonicalRegions
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ (C2ExpandedScalarChoiceRegions.canonical
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        near edge).combinedRegion) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCoverData
    (C2ExpandedScalarCoverData.ofCanonicalRegions near edge cover)

theorem offCriticalStripNonvanishing_of_expandedScalarCanonicalCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedScalarLocalBulkRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCanonicalRegions near edge
    (fun s hs => C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_cover (cover s hs))

theorem mathlibRiemannHypothesis_of_expandedScalarCanonicalCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedScalarLocalBulkRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCanonicalRegions near edge
    (fun s hs => C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_cover (cover s hs))

theorem offCriticalStripNonvanishing_of_expandedScalarCanonicalScalarCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedExactZetaScalarRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCanonicalRegions
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    near edge
    (fun s hs => by
      rcases cover s hs with hnear | hrest
      · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_nearAxis hnear
      · rcases hrest with hbulk | hedge
        · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_scalarRegion hbulk
        · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_edge hedge)

theorem mathlibRiemannHypothesis_of_expandedScalarCanonicalScalarCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedExactZetaScalarRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCanonicalRegions
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant) (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    near edge
    (fun s hs => by
      rcases cover s hs with hnear | hrest
      · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_nearAxis hnear
      · rcases hrest with hbulk | hedge
        · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_scalarRegion hbulk
        · exact C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_edge hedge)

/-- Off-critical points that are in neither the near-axis region nor the edge region. -/
def c2ExpandedScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M) : Set ℂ :=
  {s | offCriticalStrip s ∧
    s ∉ nearAxisRegion riemannZeta near.near_axis.radius ∧
    s ∉ edge.edgeRegion}

theorem c2ExpandedScalarMiddleRegion_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    {bulkRegion : Set ℂ}
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ bulkRegion) :
    ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulkRegion ∨ s ∈ edge.edgeRegion := by
  intro s hs
  by_cases hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius
  · exact Or.inl hnear
  · by_cases hedge : s ∈ edge.edgeRegion
    · exact Or.inr <| Or.inr hedge
    · exact Or.inr <| Or.inl <| hmiddle ⟨hs, hnear, hedge⟩

theorem offCriticalStripNonvanishing_of_expandedScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        near edge →
      s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCanonicalScalarCover near edge
    (fun s hs => by
      by_cases hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius
      · exact Or.inl hnear
      · by_cases hedge : s ∈ edge.edgeRegion
        · exact Or.inr <| Or.inr hedge
        · exact Or.inr <| Or.inl <| hmiddle ⟨hs, hnear, hedge⟩)

theorem mathlibRiemannHypothesis_of_expandedScalarMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        near edge →
      s ∈ c2ExpandedExactZetaScalarRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCanonicalScalarCover near edge
    (fun s hs => by
      by_cases hnear : s ∈ nearAxisRegion riemannZeta near.near_axis.radius
      · exact Or.inl hnear
      · by_cases hedge : s ∈ edge.edgeRegion
        · exact Or.inr <| Or.inr hedge
        · exact Or.inr <| Or.inl <| hmiddle ⟨hs, hnear, hedge⟩)

structure C2ExpandedScalarCanonicalCoverData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2ExpandedScalarLocalBulkRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∨
      s ∈ edge.edgeRegion

noncomputable def C2ExpandedScalarCanonicalCoverData.toCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  C2ExpandedScalarCoverData.ofCanonicalRegions data.near data.edge
      (fun s hs =>
        C2ExpandedScalarChoiceRegions.mem_canonicalCombinedRegion_of_cover
          (data.cover s hs))

theorem offCriticalStripNonvanishing_of_expandedScalarCanonicalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCoverData data.toCoverData

theorem mathlibRiemannHypothesis_of_expandedScalarCanonicalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCoverData data.toCoverData

/--
Regional middle-strip package: every off-critical point outside near-axis and edge
comes with the local scalar-bulk data needed to enter the canonical scalar region.
-/
structure C2ExpandedScalarMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2ExpandedScalarLocalBulkData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem C2ExpandedScalarMiddleRegionData.mem_scalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  (data.middle_local hs).mem_scalarRegion

theorem C2ExpandedScalarMiddleRegionData.mem_localBulkRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2ExpandedScalarLocalBulkRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  (data.middle_local hs).mem_localBulkRegion

noncomputable def C2ExpandedScalarMiddleRegionData.toCanonicalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  cover := by
    intro s hs
    by_cases hnear : s ∈ nearAxisRegion riemannZeta data.near.near_axis.radius
    · exact Or.inl hnear
    · by_cases hedge : s ∈ data.edge.edgeRegion
      · exact Or.inr <| Or.inr hedge
      · exact Or.inr <| Or.inl <| data.mem_localBulkRegion ⟨hs, hnear, hedge⟩

theorem offCriticalStripNonvanishing_of_expandedScalarMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarCanonicalCoverData
    data.toCanonicalCoverData

theorem mathlibRiemannHypothesis_of_expandedScalarMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarCanonicalCoverData data.toCanonicalCoverData

theorem C2ExpandedScalarMiddleRegionData.mem_canonicalClosedScaledRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ)))
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  (data.middle_local hs).mem_canonicalClosedScaledRegion

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegionData data

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegionData data

theorem offCriticalStripNonvanishing_of_expandedExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedExactZetaRegion (hmiddle hs))

theorem mathlibRiemannHypothesis_of_expandedExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedExactZetaRegion (hmiddle hs))

theorem offCriticalStripNonvanishing_of_expandedDominanceMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2ExpandedExactZetaDominanceRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedDominanceRegion (hmiddle hs))

theorem mathlibRiemannHypothesis_of_expandedDominanceMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2ExpandedExactZetaDominanceRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegion near edge
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_expandedDominanceRegion
        (hmiddle hs))

theorem mathlibRiemannHypothesis_of_quartetExactMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetExactCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem mathlibRiemannHypothesis_of_quartetTriangleMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetTriangleCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem mathlibRiemannHypothesis_of_quartetClosedMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
        coreCutoff K M rectangularUpper centralUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetClosedCover
    near edge (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

theorem offCriticalStripNonvanishing_of_quartetComponentMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
        coreCutoff K M continuedVerticalUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  intro s hs
  rcases c2ExpandedScalarMiddleRegion_cover near edge (fun _ hs => hmiddle hs) s hs with
    hnear | hbulk | hedge
  · exact near.near_axis.nonvanishing_of_mem hnear
  · exact c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetComponentRegion
      hbulk
  · exact edge.edge_nonvanishing hedge

theorem mathlibRiemannHypothesis_of_quartetComponentMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
        coreCutoff K M continuedVerticalUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteSubsetCover
    (bulkRegion :=
      c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
        coreCutoff K M continuedVerticalUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
    near edge
    (fun _ hs =>
      c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion hs)
    (c2ExpandedScalarMiddleRegion_cover near edge hmiddle)

end C2
