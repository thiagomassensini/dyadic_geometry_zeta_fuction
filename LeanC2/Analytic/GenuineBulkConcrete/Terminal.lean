import LeanC2.Analytic.GenuineBulkConcrete.ComponentRoutes

namespace C2

/--
Final middle-strip cover package for the preferred `canonicalClosedScaled` route.
Once this data is available, the RH transfer no longer needs to mention
the intermediate `expandedScalar` scaffolding.
-/
structure C2CanonicalClosedScaledMiddleCoverData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_scaled : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio

def C2CanonicalClosedScaledMiddleCoverData.ofExpandedScalarMiddleRegionData
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
    C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_scaled := fun _ hs => data.mem_canonicalClosedScaledRegion hs

noncomputable def c2CanonicalClosedScaledBulkRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcreteBulkRegionData
    coreCutoff K M
    (c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio)
    (fun _ => (1 : ℝ))
    horizontalConstant horizontalScale horizontalRatio
    (c2CanonicalClosedCutoffConstant K M)
    (fun _ => (1 : ℝ))

structure C2CanonicalClosedScaledCoverData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio ∨
      s ∈ edge.edgeRegion

noncomputable def C2CanonicalClosedScaledCoverData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (_data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M :=
  c2CanonicalClosedScaledBulkRegionData
    coreCutoff K M horizontalConstant horizontalScale horizontalRatio

noncomputable def C2CanonicalClosedScaledCoverData.toOffCriticalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
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
      intro s hs
      rcases data.cover s hs with hnear | hmiddle | hedge
      · exact Or.inl hnear
      · exact Or.inr <| Or.inl <|
          c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_scaledCanonicalClosedRegion
            hmiddle
      · exact Or.inr <| Or.inr hedge)

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  simpa [C2CanonicalClosedScaledCoverData.toOffCriticalCoverData,
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteCover
    data.near data.edge
    (fun s hs => by
      rcases data.cover s hs with hnear | hmiddle | hedge
      · exact Or.inl hnear
      · exact Or.inr <| Or.inl <|
          c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_scaledCanonicalClosedRegion
            hmiddle
      · exact Or.inr <| Or.inr hedge)

noncomputable def C2CanonicalClosedScaledMiddleCoverData.toCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  cover := c2ExpandedScalarMiddleRegion_cover data.near data.edge data.middle_scaled

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledCoverData data.toCoverData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledCoverData data.toCoverData

/--
Regional middle-strip package directly in the preferred `canonicalClosedScaled`
estimates. This is the most economical pointwise target for the remaining
middle-strip analytic work.
-/
structure C2CanonicalClosedScaledMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s

theorem C2CanonicalClosedScaledMiddleRegionData.mem_scaledRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio)
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  data.middle_local hs

def C2CanonicalClosedScaledMiddleRegionData.ofExpandedScalarMiddleRegionData
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
    C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs => data.mem_canonicalClosedScaledRegion hs

def C2CanonicalClosedScaledMiddleRegionData.toMiddleCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_scaled := fun _ hs => data.mem_scaledRegion hs

noncomputable def C2CanonicalClosedScaledMiddleRegionData.toCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  data.toMiddleCoverData.toCoverData

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledDirectMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleCoverData
    data.toMiddleCoverData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledDirectMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleCoverData
    data.toMiddleCoverData

/--
Pointwise local obligations that remain for the preferred `canonicalClosedScaled`
route once off-criticality is already known from the ambient middle region.
-/
structure C2CanonicalClosedScaledLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper
            (c2CanonicalClosedTiltConstant
              K M horizontalConstant horizontalScale horizontalRatio)
            (fun _ => (1 : ℝ)))
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper
        (c2CutoffUpperFromScale
          (c2CanonicalClosedCutoffConstant K M)
          (fun _ => (1 : ℝ))) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

theorem C2CanonicalClosedScaledLocalData.of_residualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance :
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2ExpandedQuartetResidualMargin s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  refine {
    horizontalScale_pos := hscale_pos
    horizontalConstant_nonneg := hconstant_nonneg
    horizontalRatio_nonneg := hratio_nonneg
    horizontalRatio_lt_one := hratio_lt_one
    horizontalLayer_bound := hhorizontal.layer_bound
    quartet_dominance := ?_
  }
  simpa [c2CanonicalClosedScaledResidualUpper,
    C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper,
    c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
    c2ExpandedQuartetK2Margin] using
    (c2ExpandedQuartetDominance_of_residualBound hdominance)

theorem C2CanonicalClosedScaledLocalData.of_analyticResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance :
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  apply C2CanonicalClosedScaledLocalData.of_residualDominance
    hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
  simpa [c2ExpandedQuartetResidualMargin_eq_analyticBulkAllowance_sub_reserve_of_offCriticalStrip
    hoff] using
    hdominance

theorem C2CanonicalClosedScaledLocalData.of_majorantAnalyticResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance :
      c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  apply C2CanonicalClosedScaledLocalData.of_analyticResidualDominance
    hoff hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
  exact lt_of_le_of_lt
    (c2CanonicalClosedScaledResidualUpper_le_majorant_of_offCriticalStrip
      hoff)
    hdominance

theorem C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hvertical :
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance :
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  apply C2CanonicalClosedScaledLocalData.of_majorantAnalyticResidualDominance
    hoff hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
  exact lt_of_le_of_lt
    (c2CanonicalClosedScaledResidualMajorant_le_verticalBudget_of_offCriticalStrip
      hoff hvertical)
    hdominance

theorem C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualTruncationBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (htruncation : C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s)
    (hvertical :
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance :
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
    hoff hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one
    htruncation.toHorizontalLayerBudget hvertical hdominance

theorem C2CanonicalClosedScaledLocalData.of_finiteExactZetaVerticalAnalyticResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance :
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M (c2CanonicalClosedVerticalFiniteExactZetaUpper K M)
        horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  apply C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
    hoff hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (c2CanonicalClosedVerticalUpper_le_finiteExactZetaUpper_of_offCriticalStrip K M hoff)
    hdominance

theorem C2CanonicalClosedScaledLocalData.of_finiteExactZetaAnalyticResidualDominance
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hhorizontal : C2ExpandedHorizontalLayerBudget
      coreCutoff horizontalConstant horizontalScale horizontalRatio s)
    (hdominance :
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  apply C2CanonicalClosedScaledLocalData.of_finiteExactZetaVerticalAnalyticResidualDominance
    hoff hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
  exact lt_of_le_of_lt
    (c2CanonicalClosedScaledResidualVerticalBudgetUpper_le_finiteExactZeta_of_offCriticalStrip
      hoff)
    hdominance

theorem C2CanonicalClosedScaledLocalData.toEstimates
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hoff : offCriticalStrip s)
    (data : C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    offCritical := hoff
    horizontalScale_pos := data.horizontalScale_pos
    horizontalConstant_nonneg := data.horizontalConstant_nonneg
    horizontalRatio_nonneg := data.horizontalRatio_nonneg
    horizontalRatio_lt_one := data.horizontalRatio_lt_one
    horizontalLayer_bound := data.horizontalLayer_bound
    quartet_dominance := data.quartet_dominance
  }

theorem C2CanonicalClosedScaledLocalData.ofEstimates
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hs : C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem C2CanonicalClosedScaledLocalData.of_mem_scaledRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s :=
  C2CanonicalClosedScaledLocalData.ofEstimates hs

theorem C2ExpandedScalarLocalBulkData.toCanonicalClosedScaledLocalData
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
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s :=
  C2CanonicalClosedScaledLocalData.of_mem_scaledRegion
    data.mem_canonicalClosedScaledRegion

/--
Pointwise local data for the note-aligned full-resolvent route: the exact
vertical residual is controlled by an external budget `verticalUpper`, the
horizontal channel stays in geometric form, and the resulting residual budget
fits under the analytic allowance.
-/
structure C2CanonicalClosedScaledVerticalBudgetLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  vertical_bound :
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s ≤
      verticalUpper s
  residual_dominance :
    c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
      c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s

theorem C2CanonicalClosedScaledVerticalBudgetLocalData.toCanonicalClosedScaledLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (data : C2CanonicalClosedScaledVerticalBudgetLocalData
      coreCutoff K M
      verticalUpper horizontalConstant horizontalScale horizontalRatio s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
    data.offCritical
    data.horizontalScale_pos
    data.horizontalConstant_nonneg
    data.horizontalRatio_nonneg
    data.horizontalRatio_lt_one
    ⟨data.horizontalLayer_bound⟩
    data.vertical_bound
    data.residual_dominance

/--
Regional middle-strip package for the note-aligned full-resolvent route.
The only middle-region inputs are a horizontal geometric budget, an external
vertical upper bound, and the residual dominance inequality against the
analytic allowance.
-/
structure C2CanonicalClosedScaledVerticalBudgetMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2CanonicalClosedScaledVerticalBudgetLocalData
      coreCutoff K M
      verticalUpper horizontalConstant horizontalScale horizontalRatio s

def C2CanonicalClosedScaledVerticalBudgetMiddleRegionData.toCanonicalClosedScaledMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalBudgetMiddleRegionData
      coreCutoff K M
      verticalUpper horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun {s} hs => by
    let localData :
        C2CanonicalClosedScaledVerticalBudgetLocalData
          coreCutoff K M
          verticalUpper horizontalConstant horizontalScale horizontalRatio s :=
      data.middle_local hs
    let hcanonical :
        C2CanonicalClosedScaledLocalData
          coreCutoff K M horizontalConstant horizontalScale horizontalRatio s :=
      C2CanonicalClosedScaledVerticalBudgetLocalData.toCanonicalClosedScaledLocalData
        localData
    exact C2CanonicalClosedScaledLocalData.toEstimates localData.offCritical hcanonical

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledVerticalBudgetMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalBudgetMiddleRegionData
      coreCutoff K M
      verticalUpper horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledVerticalBudgetMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalBudgetMiddleRegionData
      coreCutoff K M
      verticalUpper horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData

/--
Pointwise local data for the combined external route: the horizontal channel is
supplied through an off-axis odd-truncation budget, while the vertical part is
controlled by an external `verticalUpper`.
-/
structure C2CanonicalClosedScaledVerticalTruncationLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  truncation_budget :
    C2ExpandedOddTruncationBudget
      coreCutoff oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s
  vertical_bound :
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s ≤
      verticalUpper s
  residual_dominance :
    c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
      c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s

theorem C2CanonicalClosedScaledVerticalTruncationLocalData.toCanonicalClosedScaledLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (data : C2CanonicalClosedScaledVerticalTruncationLocalData
      coreCutoff K M verticalUpper oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact
    C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualTruncationBounds
      data.offCritical
      data.horizontalScale_pos
      data.horizontalConstant_nonneg
      data.horizontalRatio_nonneg
      data.horizontalRatio_lt_one
      data.truncation_budget
      data.vertical_bound
      data.residual_dominance

/--
Regional middle-strip package for the combined external route. This is the most
compressed honest target for the current full-resolvent note: an external
odd-truncation envelope, an external vertical upper bound, and the residual
dominance inequality.
-/
structure C2CanonicalClosedScaledVerticalTruncationMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalUpper : ℂ → ℝ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2CanonicalClosedScaledVerticalTruncationLocalData
      coreCutoff K M verticalUpper oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio s

def
  C2CanonicalClosedScaledVerticalTruncationMiddleRegionData.toCanonicalClosedScaledMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalTruncationMiddleRegionData
      coreCutoff K M verticalUpper oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun {s} hs => by
    let localData :
        C2CanonicalClosedScaledVerticalTruncationLocalData
          coreCutoff K M verticalUpper oddTruncationUpper
          horizontalConstant horizontalScale horizontalRatio s :=
      data.middle_local hs
    let hcanonical :
        C2CanonicalClosedScaledLocalData
          coreCutoff K M horizontalConstant horizontalScale horizontalRatio s :=
      C2CanonicalClosedScaledVerticalTruncationLocalData.toCanonicalClosedScaledLocalData
        localData
    exact C2CanonicalClosedScaledLocalData.toEstimates localData.offCritical hcanonical

theorem
    offCriticalStripNonvanishing_of_canonicalClosedScaledVerticalTruncationMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalTruncationMiddleRegionData
      coreCutoff K M verticalUpper oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledVerticalTruncationMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledVerticalTruncationMiddleRegionData
      coreCutoff K M verticalUpper oddTruncationUpper
      horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData

/--
Pointwise local data for the less coarse residual-budget route: the quartet tail
stays peeled off, while tilt/horizontal/cutoff are controlled separately.
-/
structure C2CanonicalClosedScaledResidualBudgetLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  tilt_bound :
    c2TiltAnalyticRegularizedUpper
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ)) s ≤ tiltBudget s
  horizontal_bound :
    c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget s
  cutoff_bound :
    c2CutoffUpperFromScale
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ)) s ≤ cutoffBudget s
  residual_dominance :
    tiltBudget s + horizontalBudget s + cutoffBudget s <
      c2ExpandedQuartetResidualMargin s

theorem C2CanonicalClosedScaledResidualBudgetLocalData.toCanonicalClosedScaledLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
    {s : ℂ}
    (data : C2CanonicalClosedScaledResidualBudgetLocalData
      coreCutoff K M
      horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget s) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  refine {
    horizontalScale_pos := data.horizontalScale_pos
    horizontalConstant_nonneg := data.horizontalConstant_nonneg
    horizontalRatio_nonneg := data.horizontalRatio_nonneg
    horizontalRatio_lt_one := data.horizontalRatio_lt_one
    horizontalLayer_bound := data.horizontalLayer_bound
    quartet_dominance := ?_
  }
  simpa [C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper,
    c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
    c2ExpandedQuartetK2Margin] using
    (c2ExpandedQuartetDominance_of_residualBudgetBounds
      data.tilt_bound
      data.horizontal_bound
      data.cutoff_bound
      data.residual_dominance)

/--
Regional middle-strip package for the residual-budget route, keeping the three
remaining scalar budgets separate instead of collapsing them into one residual
upper.
-/
structure C2CanonicalClosedScaledResidualBudgetMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2CanonicalClosedScaledResidualBudgetLocalData
      coreCutoff K M
      horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget s

def C2CanonicalClosedScaledResidualBudgetMiddleRegionData.toCanonicalClosedScaledMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
    (data : C2CanonicalClosedScaledResidualBudgetMiddleRegionData
      coreCutoff K M
      horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget) :
    C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun {s} hs => by
    let localData :
        C2CanonicalClosedScaledResidualBudgetLocalData
          coreCutoff K M
          horizontalConstant horizontalScale horizontalRatio
          tiltBudget horizontalBudget cutoffBudget s :=
      data.middle_local hs
    let hcanonical :
        C2CanonicalClosedScaledLocalData
          coreCutoff K M horizontalConstant horizontalScale horizontalRatio s :=
      C2CanonicalClosedScaledResidualBudgetLocalData.toCanonicalClosedScaledLocalData localData
    exact C2CanonicalClosedScaledLocalData.toEstimates localData.offCritical hcanonical


theorem offCriticalStripNonvanishing_of_canonicalClosedScaledResidualBudgetMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
    (data : C2CanonicalClosedScaledResidualBudgetMiddleRegionData
      coreCutoff K M
      horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData


theorem mathlibRiemannHypothesis_of_canonicalClosedScaledResidualBudgetMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
    (data : C2CanonicalClosedScaledResidualBudgetMiddleRegionData
      coreCutoff K M
      horizontalConstant horizontalScale horizontalRatio
      tiltBudget horizontalBudget cutoffBudget) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledDirectMiddleRegionData
    data.toCanonicalClosedScaledMiddleRegionData

theorem C2CanonicalClosedScaledLocalData.of_mem_zetaDepthCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper oddFactorUpper zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
      coreCutoff K M
      depthUpper coreUpper oddFactorUpper zetaUpper
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    quartet_dominance := by
      simpa using hs.quartet_dominance
  }

theorem C2CanonicalClosedScaledLocalData.of_mem_explicitFiniteCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
      coreCutoff K M zetaUpper
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    quartet_dominance := by
      simpa using hs.quartet_dominance
  }

theorem C2CanonicalClosedScaledLocalData.of_mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s := by
  exact {
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    quartet_dominance := by
      simpa using hs.quartet_dominance
  }

theorem C2CanonicalClosedScaledLocalData.mem_scaledRegion_of_middle
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M}
    {edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M}
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion near edge)
    (data : C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  data.toEstimates hs.1

/--
Regional middle-strip package in the minimal pointwise local obligations for the
preferred `canonicalClosedScaled` route.
-/
structure C2CanonicalClosedScaledMiddleLocalData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2CanonicalClosedScaledLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio s

def C2CanonicalClosedScaledMiddleLocalData.ofMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    C2CanonicalClosedScaledLocalData.ofEstimates (data.middle_local hs)

def C2CanonicalClosedScaledMiddleLocalData.ofExpandedScalarMiddleRegionData
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
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  C2CanonicalClosedScaledMiddleLocalData.ofMiddleRegionData
    (C2CanonicalClosedScaledMiddleRegionData.ofExpandedScalarMiddleRegionData data)

def C2CanonicalClosedScaledMiddleLocalData.ofZetaDepthCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper oddFactorUpper zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
        coreCutoff K M
        depthUpper coreUpper oddFactorUpper zetaUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := near
  edge := edge
  middle_local := fun _ hs =>
    C2CanonicalClosedScaledLocalData.of_mem_zetaDepthCoreRegion (hmiddle hs)

def C2CanonicalClosedScaledMiddleLocalData.ofExplicitFiniteCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
        coreCutoff K M zetaUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := near
  edge := edge
  middle_local := fun _ hs =>
    C2CanonicalClosedScaledLocalData.of_mem_explicitFiniteCoreRegion (hmiddle hs)

def C2CanonicalClosedScaledMiddleLocalData.ofExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := near
  edge := edge
  middle_local := fun _ hs =>
    C2CanonicalClosedScaledLocalData.of_mem_explicitScalarExactZetaRegion
      (hmiddle hs)

def C2CanonicalClosedScaledMiddleLocalData.toMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    (data.middle_local hs).toEstimates hs.1

def C2CanonicalClosedScaledMiddleLocalData.toMiddleCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  data.toMiddleRegionData.toMiddleCoverData

noncomputable def C2CanonicalClosedScaledMiddleLocalData.toCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  data.toMiddleRegionData.toCoverData

theorem offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledDirectMiddleRegionData
    data.toMiddleRegionData

theorem mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledDirectMiddleRegionData
    data.toMiddleRegionData

/--
Terminal certificate package for the formal C2 route to RH.
An inhabitant of this structure supplies the calibrated middle-region data
needed by the current canonical endpoint.
-/
structure RiemannHypothesisTerminalData where
  coreCutoff : ℕ → ℕ
  K : ℕ
  M : ℕ
  horizontalConstant : ℂ → ℝ
  horizontalScale : ℂ → ℝ
  horizontalRatio : ℂ → ℝ
  middle : C2CanonicalClosedScaledMiddleLocalData
    coreCutoff K M horizontalConstant horizontalScale horizontalRatio

def RiemannHypothesisTerminalData.toMiddleLocalData
    (data : RiemannHypothesisTerminalData) :
    C2CanonicalClosedScaledMiddleLocalData
      data.coreCutoff data.K data.M
      data.horizontalConstant data.horizontalScale data.horizontalRatio :=
  data.middle

noncomputable def RiemannHypothesisTerminalData.toCoverData
    (data : RiemannHypothesisTerminalData) :
    C2CanonicalClosedScaledCoverData
      data.coreCutoff data.K data.M
      data.horizontalConstant data.horizontalScale data.horizontalRatio :=
  data.middle.toCoverData

theorem offCriticalStripNonvanishing_of_terminalData
    (data : RiemannHypothesisTerminalData) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel
        data.coreCutoff data.K data.M) :=
  offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleLocalData
    data.middle

theorem mathlibRiemannHypothesis_of_terminalData
    (data : RiemannHypothesisTerminalData) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleLocalData
    data.middle

def RiemannHypothesisTerminalData.ofMiddleLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData where
  coreCutoff := coreCutoff
  K := K
  M := M
  horizontalConstant := horizontalConstant
  horizontalScale := horizontalScale
  horizontalRatio := horizontalRatio
  middle := data


/--
Direct strong-middle endpoint from continuation data.
Unlike the canonical terminal package above, this version keeps the bulk-bound
functions `tiltConstant`, `tiltScale`, `cutoffConstant`, and `cutoffScale`
fully parametric.
-/
theorem mathlibRiemannHypothesis_of_continuationAndExplicitScalarExactZetaMiddleRegionWithBounds
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
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
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
  exact mathlibRiemannHypothesis_of_expandedScalarMiddleRegion nearC2 edgeC2
    (fun _ hs =>
      c2ExpandedExactZetaScalarRegion_mem_of_mem_explicitScalarExactZetaRegion
        (hmiddle hs))

theorem mathlibRiemannHypothesis_of_continuationAndExpandedExactZetaMiddleRegionWithBounds
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
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
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
  exact mathlibRiemannHypothesis_of_expandedExactZetaMiddleRegion
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem offCriticalStripNonvanishing_of_continuationAndBulkConcreteMiddleRegionWithBounds
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
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
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
  rcases c2ExpandedScalarMiddleRegion_cover nearC2 edgeC2 (fun _ hs => hmiddle hs) s hs with
    hnear | hbulk | hedge
  · exact nearC2.near_axis.nonvanishing_of_mem hnear
  · exact c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_concreteRegion hbulk
  · exact edgeC2.edge_nonvanishing hedge

theorem
  offCriticalStripNonvanishing_of_genuineFInfinite_of_continuationAndBulkConcreteMiddle
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
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing genuineFInfinite := by
  intro s hs
  have hcontinued :=
    offCriticalStripNonvanishing_of_continuationAndBulkConcreteMiddleRegionWithBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation hmiddle s hs
  have hsPunctured : s ∈ puncturedOpenRightHalfPlane := by
    refine ⟨hs.1, ?_⟩
    intro hsOne
    have hre : s.re = 1 := by
      simp [hsOne]
    linarith [hs.2.1, hre]
  have hEq :=
    c2OddTailContinuedBalancingSeedBulkModel_eq_genuineFInfinite_on_punctured
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation s hsPunctured
  simpa [hEq] using hcontinued

theorem mathlibRiemannHypothesis_of_continuationAndBulkConcreteMiddleRegionWithBounds
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
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
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
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_concreteCover
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      nearC2 edgeC2
      (c2ExpandedScalarMiddleRegion_cover nearC2 edgeC2 (fun _ hs => hmiddle hs))

theorem
  mathlibRiemannHypothesis_of_genuineFInfiniteContinuationAndBulkConcreteMiddle
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
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation continuation
    (offCriticalStripNonvanishing_of_genuineFInfinite_of_continuationAndBulkConcreteMiddle
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation hmiddle)

theorem mathlibRiemannHypothesis_of_continuationAndBulkConcreteMiddlePointwiseBounds
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
      C2OddTailContinuedBalancingSeedBulkConcreteEstimates
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndBulkConcreteMiddleRegionWithBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    continuation (fun _ hs => hmiddle hs)

theorem
  offCriticalStripNonvanishing_of_genuineFInfinite_of_continuationAndBulkConcretePointwiseBounds
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
      C2OddTailContinuedBalancingSeedBulkConcreteEstimates
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    offCriticalStripNonvanishing genuineFInfinite := by
  exact
    offCriticalStripNonvanishing_of_genuineFInfinite_of_continuationAndBulkConcreteMiddle
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      continuation (fun _ hs => hmiddle hs)

theorem
  mathlibRiemannHypothesis_of_genuineFInfiniteContinuationAndBulkConcretePointwiseBounds
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
      C2OddTailContinuedBalancingSeedBulkConcreteEstimates
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_genuineFInfiniteContinuationAndBulkConcreteMiddle
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    continuation (fun _ hs => hmiddle hs)
def C2CanonicalClosedScaledMiddleLocalData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData data

def RiemannHypothesisTerminalData.ofMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData
    (C2CanonicalClosedScaledMiddleLocalData.ofMiddleRegionData data)

def C2CanonicalClosedScaledMiddleRegionData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleRegionData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleRegionData data

def RiemannHypothesisTerminalData.ofMiddleCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData {
    near := data.near
    edge := data.edge
    middle_local := fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_mem_scaledRegion
        (data.middle_scaled hs)
  }

def C2CanonicalClosedScaledMiddleCoverData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledMiddleCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleCoverData data

def RiemannHypothesisTerminalData.ofCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData {
    near := data.near
    edge := data.edge
    middle_local := fun s hs => by
      rcases data.cover s hs.1 with hnear | hmiddle | hedge
      · exact False.elim (hs.2.1 hnear)
      · exact C2CanonicalClosedScaledLocalData.of_mem_scaledRegion hmiddle
      · exact False.elim (hs.2.2 hedge)
  }

def C2CanonicalClosedScaledCoverData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2CanonicalClosedScaledCoverData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofCoverData data

def RiemannHypothesisTerminalData.ofExpandedScalarMiddleRegionData
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
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData
    (C2CanonicalClosedScaledMiddleLocalData.ofExpandedScalarMiddleRegionData data)

def C2ExpandedScalarMiddleRegionData.toTerminalData
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
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofExpandedScalarMiddleRegionData data

def RiemannHypothesisTerminalData.ofExpandedScalarCanonicalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofMiddleLocalData {
    near := data.near
    edge := data.edge
    middle_local := fun s hs => by
      rcases data.cover s hs.1 with hnear | hbulk | hedge
      · exact False.elim (hs.2.1 hnear)
      · exact
          C2ExpandedScalarLocalBulkData.toCanonicalClosedScaledLocalData
            (C2ExpandedScalarLocalBulkData.of_mem_scalarRegion
              (c2ExpandedExactZetaScalarRegion_mem_of_mem_localBulkRegion hbulk))
      · exact False.elim (hs.2.2 hedge)
  }

def C2ExpandedScalarCanonicalCoverData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedScalarCanonicalCoverData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  RiemannHypothesisTerminalData.ofExpandedScalarCanonicalCoverData data

/--
Regional middle-strip package directly in the explicit-scalar exact-zeta route.
This is the strongest concrete middle target that already descends automatically
to the preferred terminal RH package.
-/
structure C2ExplicitScalarExactZetaMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem C2ExplicitScalarExactZetaMiddleRegionData.mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  data.middle_local hs

def C2ExplicitScalarExactZetaMiddleRegionData.toExpandedScalarMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    C2ExpandedScalarLocalBulkData.of_mem_explicitScalarExactZetaRegion
      (data.mem_explicitScalarExactZetaRegion hs)

theorem offCriticalStripNonvanishing_of_explicitScalarExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegionData
    data.toExpandedScalarMiddleRegionData

theorem mathlibRiemannHypothesis_of_explicitScalarExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegionData
    data.toExpandedScalarMiddleRegionData

def C2ExplicitScalarExactZetaMiddleRegionData.toCanonicalClosedScaledMiddleLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  C2CanonicalClosedScaledMiddleLocalData.ofExplicitScalarExactZetaMiddleRegion
    data.near data.edge (fun _ hs => data.mem_explicitScalarExactZetaRegion hs)

def C2ExplicitScalarExactZetaMiddleRegionData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  data.toCanonicalClosedScaledMiddleLocalData.toTerminalData

/--
Regional middle-strip package directly in the expanded exact-zeta route.
It is equivalent pointwise to the explicit-scalar exact-zeta package and can be
used as an alternative strong endpoint for the remaining analytic work.
-/
structure C2ExpandedExactZetaMiddleRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  middle_local : ∀ ⦃s : ℂ⦄,
    s ∈ c2ExpandedScalarMiddleRegion near edge →
    C2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaEstimates
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

theorem C2ExpandedExactZetaMiddleRegionData.mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    {s : ℂ}
    (hs : s ∈ c2ExpandedScalarMiddleRegion data.near data.edge) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  data.middle_local hs

def C2ExpandedExactZetaMiddleRegionData.toExpandedScalarMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedScalarMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    C2ExpandedScalarLocalBulkData.of_mem_expandedExactZetaRegion
      (data.mem_expandedExactZetaRegion hs)

theorem offCriticalStripNonvanishing_of_expandedExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :=
  offCriticalStripNonvanishing_of_expandedScalarMiddleRegionData
    data.toExpandedScalarMiddleRegionData

theorem mathlibRiemannHypothesis_of_expandedExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_expandedScalarMiddleRegionData
    data.toExpandedScalarMiddleRegionData

def C2ExpandedExactZetaMiddleRegionData.toExplicitScalarExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    c2ExpandedExactZeta_mem_explicitScalarExactZetaRegion
      (data.mem_expandedExactZetaRegion hs)

def C2ExplicitScalarExactZetaMiddleRegionData.toExpandedExactZetaMiddleRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (data : C2ExplicitScalarExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale where
  near := data.near
  edge := data.edge
  middle_local := fun _ hs =>
    c2ExplicitScalarExactZeta_mem_expandedExactZetaRegion
      (data.mem_explicitScalarExactZetaRegion hs)

noncomputable def C2ExpandedExactZetaMiddleRegionData.toCanonicalClosedScaledMiddleLocalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    C2CanonicalClosedScaledMiddleLocalData
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  C2ExplicitScalarExactZetaMiddleRegionData.toCanonicalClosedScaledMiddleLocalData
    (data.toExplicitScalarExactZetaMiddleRegionData)

noncomputable def C2ExpandedExactZetaMiddleRegionData.toTerminalData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (data : C2ExpandedExactZetaMiddleRegionData
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  data.toCanonicalClosedScaledMiddleLocalData.toTerminalData

noncomputable def RiemannHypothesisTerminalData.ofExpandedExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
        coreCutoff K M
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  (C2ExpandedExactZetaMiddleRegionData.toTerminalData {
    near := near
    edge := edge
    middle_local := fun _ hs => hmiddle hs
  })

def RiemannHypothesisTerminalData.ofZetaDepthCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper oddFactorUpper zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
        coreCutoff K M
        depthUpper coreUpper oddFactorUpper zetaUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  (C2CanonicalClosedScaledMiddleLocalData.ofZetaDepthCoreMiddleRegion
    near edge hmiddle).toTerminalData

def RiemannHypothesisTerminalData.ofExplicitFiniteCoreMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
        coreCutoff K M zetaUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  (C2CanonicalClosedScaledMiddleLocalData.ofExplicitFiniteCoreMiddleRegion
    near edge hmiddle).toTerminalData

def RiemannHypothesisTerminalData.ofExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion near edge →
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ))
        horizontalConstant horizontalScale horizontalRatio
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ))) :
    RiemannHypothesisTerminalData :=
  (C2CanonicalClosedScaledMiddleLocalData.ofExplicitScalarExactZetaMiddleRegion
    near edge hmiddle).toTerminalData

noncomputable def
    RiemannHypothesisTerminalData.ofGenuineFInfiniteNearAxisAndExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (near : GenuineFInfiniteNearAxisData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M) continuation near)
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
    RiemannHypothesisTerminalData := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M) continuation near
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact RiemannHypothesisTerminalData.ofExplicitScalarExactZetaMiddleRegion
    nearC2 edgeC2 (fun _ hs => hmiddle hs)

theorem
    mathlibRiemannHypothesis_of_genuineFInfiniteNearAxisAndExplicitScalarExactZetaMiddleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    (continuation : GenuineFInfiniteContinuationData)
    (near : GenuineFInfiniteNearAxisData)
    (hmiddle : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M) continuation near)
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
    RiemannHypothesisTerminalData.ofGenuineFInfiniteNearAxisAndExplicitScalarExactZetaMiddleRegion
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      continuation near hmiddle
  exact mathlibRiemannHypothesis_of_terminalData terminalData

noncomputable def RiemannHypothesisTerminalData.ofContinuationAndMiddleLocal
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
      C2CanonicalClosedScaledLocalData
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesisTerminalData := by
  let nearC2 :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
      (coreCutoff := coreCutoff) (K := K) (M := M)
      continuation
      (GenuineFInfiniteNearAxisData.of_continuation continuation)
  let edgeC2 :=
    C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
      (coreCutoff := coreCutoff) (K := K) (M := M)
  exact (RiemannHypothesisTerminalData.ofMiddleLocalData {
    near := nearC2
    edge := edgeC2
    middle_local := fun _ hs => hmiddle hs
  })

theorem mathlibRiemannHypothesis_of_continuationAndMiddleLocal
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
      C2CanonicalClosedScaledLocalData
        coreCutoff K M horizontalConstant horizontalScale horizontalRatio s) :
    RiemannHypothesis := by
  let terminalData :=
    RiemannHypothesisTerminalData.ofContinuationAndMiddleLocal
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      continuation hmiddle
  exact mathlibRiemannHypothesis_of_terminalData terminalData

theorem offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
            (c2TiltAnalyticRegularizedUpper
              (c2CanonicalClosedTiltConstant
                K M horizontalConstant horizontalScale horizontalRatio)
              (fun _ => (1 : ℝ)))
            (c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio)) s +
        c2BulkEUpper
          (c2CutoffUpperFromScale
            (c2CanonicalClosedCutoffConstant K M)
            (fun _ => (1 : ℝ))) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_canonicalClosedScaledMiddleLocalData {
    near :=
      C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
        (coreCutoff := coreCutoff) (K := K) (M := M)
        continuation
        (GenuineFInfiniteNearAxisData.of_continuation continuation)
    edge :=
      C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
        (coreCutoff := coreCutoff) (K := K) (M := M)
    middle_local := fun _ hs => {
      horizontalScale_pos := hscale_pos hs
      horizontalConstant_nonneg := hconstant_nonneg hs
      horizontalRatio_nonneg := hratio_nonneg hs
      horizontalRatio_lt_one := hratio_lt_one hs
      horizontalLayer_bound := (hhorizontal hs).layer_bound
      quartet_dominance := hdominance hs
    }
  }

theorem mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
            (c2TiltAnalyticRegularizedUpper
              (c2CanonicalClosedTiltConstant
                K M horizontalConstant horizontalScale horizontalRatio)
              (fun _ => (1 : ℝ)))
            (c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio)) s +
        c2BulkEUpper
          (c2CutoffUpperFromScale
            (c2CanonicalClosedCutoffConstant K M)
            (fun _ => (1 : ℝ))) s <
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_canonicalClosedScaledMiddleLocalData {
    near :=
      C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
        (coreCutoff := coreCutoff) (K := K) (M := M)
        continuation
        (GenuineFInfiniteNearAxisData.of_continuation continuation)
    edge :=
      C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
        (coreCutoff := coreCutoff) (K := K) (M := M)
    middle_local := fun _ hs => {
      horizontalScale_pos := hscale_pos hs
      horizontalConstant_nonneg := hconstant_nonneg hs
      horizontalRatio_nonneg := hratio_nonneg hs
      horizontalRatio_lt_one := hratio_lt_one hs
      horizontalLayer_bound := (hhorizontal hs).layer_bound
      quartet_dominance := hdominance hs
    }
  }

theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleSeparatedDominanceBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {quartetTailBudget tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
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
    (hquartetTail : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2QuartetVerticalTailUpper s ≤ quartetTailBudget s)
    (htilt : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2TiltAnalyticRegularizedUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ)) s ≤ tiltBudget s)
    (hhorizontal_upper : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CutoffUpperFromScale
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s ≤ cutoffBudget s)
    (hbudgetDominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      quartetTailBudget s + tiltBudget s + horizontalBudget s + cutoffBudget s <
        c2ExpandedQuartetK2Margin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      c2ExpandedQuartetDominance_of_budgetBounds
        (hquartetTail hs)
        (htilt hs)
        (hhorizontal_upper hs)
        (hcutoff hs)
        (hbudgetDominance hs))

theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualDominanceBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
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
    (htilt : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2TiltAnalyticRegularizedUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ)) s ≤ tiltBudget s)
    (hhorizontal_upper : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CutoffUpperFromScale
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s ≤ cutoffBudget s)
    (hbudgetDominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      tiltBudget s + horizontalBudget s + cutoffBudget s <
        c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      c2ExpandedQuartetDominance_of_residualBudgetBounds
        (htilt hs)
        (hhorizontal_upper hs)
        (hcutoff hs)
        (hbudgetDominance hs))

theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualPointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2ExpandedQuartetResidualMargin s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_residualDominance
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs)).quartet_dominance)

theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualAnalyticBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_analyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs)).quartet_dominance)

theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleSeparatedDominanceBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {quartetTailBudget tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
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
    (hquartetTail : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2QuartetVerticalTailUpper s ≤ quartetTailBudget s)
    (htilt : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2TiltAnalyticRegularizedUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ)) s ≤ tiltBudget s)
    (hhorizontal_upper : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CutoffUpperFromScale
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s ≤ cutoffBudget s)
    (hbudgetDominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      quartetTailBudget s + tiltBudget s + horizontalBudget s + cutoffBudget s <
        c2ExpandedQuartetK2Margin s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      c2ExpandedQuartetDominance_of_budgetBounds
        (hquartetTail hs)
        (htilt hs)
        (hhorizontal_upper hs)
        (hcutoff hs)
        (hbudgetDominance hs))

theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualDominanceBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {tiltBudget horizontalBudget cutoffBudget : ℂ → ℝ}
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
    (htilt : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2TiltAnalyticRegularizedUpper
        (c2CanonicalClosedTiltConstant
          K M horizontalConstant horizontalScale horizontalRatio)
        (fun _ => (1 : ℝ)) s ≤ tiltBudget s)
    (hhorizontal_upper : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget s)
    (hcutoff : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CutoffUpperFromScale
        (c2CanonicalClosedCutoffConstant K M)
        (fun _ => (1 : ℝ)) s ≤ cutoffBudget s)
    (hbudgetDominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      tiltBudget s + horizontalBudget s + cutoffBudget s <
        c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      c2ExpandedQuartetDominance_of_residualBudgetBounds
        (htilt hs)
        (hhorizontal_upper hs)
        (hcutoff hs)
        (hbudgetDominance hs))

theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualPointwiseBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2ExpandedQuartetResidualMargin s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_residualDominance
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs))

theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualAnalyticBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_analyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs))

theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualMajorantBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_majorantAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs)).quartet_dominance)

theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualMajorantBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_majorantAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs))


theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hvertical : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hvertical hs)
        (hdominance hs)).quartet_dominance)


theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hvertical : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_verticalBudgetAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hvertical hs)
        (hdominance hs))


theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetTruncationBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hvertical : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact
    offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (verticalUpper := verticalUpper)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one
      (fun _ hs => (htruncation hs).toHorizontalLayerBudget)
      hvertical hdominance


theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetTruncationBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalUpper : ℂ → ℝ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hvertical : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s)
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualVerticalBudgetBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (verticalUpper := verticalUpper)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one
      (fun _ hs => (htruncation hs).toHorizontalLayerBudget)
      hvertical hdominance


theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualFiniteExactZetaVerticalBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M (c2CanonicalClosedVerticalFiniteExactZetaUpper K M)
        horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_finiteExactZetaVerticalAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs)).quartet_dominance)


theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualFiniteExactZetaVerticalBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M (c2CanonicalClosedVerticalFiniteExactZetaUpper K M)
        horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_finiteExactZetaVerticalAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs))


theorem
  offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddleResidualFiniteExactZetaBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  exact offCriticalStripNonvanishing_of_continuationAndCanonicalClosedScaledMiddlePointwiseBounds
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation hscale_pos hconstant_nonneg hratio_nonneg hratio_lt_one hhorizontal
    (fun _ hs =>
      (C2CanonicalClosedScaledLocalData.of_finiteExactZetaAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs)).quartet_dominance)


theorem
  mathlibRiemannHypothesis_of_continuationAndCanonicalClosedScaledMiddleResidualFiniteExactZetaBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
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
    (hdominance : ∀ ⦃s : ℂ⦄,
      s ∈ c2ExpandedScalarMiddleRegion
        (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
          (coreCutoff := coreCutoff) (K := K) (M := M)
          continuation
          (GenuineFInfiniteNearAxisData.of_continuation continuation))
        (C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
          (coreCutoff := coreCutoff) (K := K) (M := M)) →
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_continuationAndMiddleLocal
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    continuation
    (fun _ hs =>
      C2CanonicalClosedScaledLocalData.of_finiteExactZetaAnalyticResidualDominance
        hs.1
        (hscale_pos hs)
        (hconstant_nonneg hs)
        (hratio_nonneg hs)
        (hratio_lt_one hs)
        (hhorizontal hs)
        (hdominance hs))

end C2
