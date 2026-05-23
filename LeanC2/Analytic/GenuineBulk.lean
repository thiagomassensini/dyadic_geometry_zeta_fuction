import LeanC2.Analytic.GenuineCover

namespace C2

/-!
Bulk bounds data with the numerator fixed to `genuineFInfinite`.

This is the bulk analogue of `GenuineCover.lean`: the generic roadmap structure
`RegionalVerticalBulkBoundsData` is still the execution target, but this file gives
the future quantitative bulk decomposition a direct place to land.
-/

/-- Route-level regional bulk data whose target is definitionally `genuineFInfinite`. -/
structure GenuineFInfiniteRegionalBulkRouteData where
  bulkRegion : Set ℂ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion → genuineFInfinite s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion → Kdelta s = K2 s / (1 - q s) + Gdelta s
  dominance :
    ∀ s : ℂ, s ∈ bulkRegion → ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

/-- Bound-level regional bulk data whose target is definitionally `genuineFInfinite`. -/
structure GenuineFInfiniteRegionalBulkBoundsData where
  bulkRegion : Set ℂ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  K2Lower : ℂ → ℝ
  GUpper : ℂ → ℝ
  EUpper : ℂ → ℝ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion → genuineFInfinite s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion → Kdelta s = K2 s / (1 - q s) + Gdelta s
  K2_lower : ∀ s : ℂ, s ∈ bulkRegion → K2Lower s ≤ ‖K2 s‖
  G_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Gdelta s‖ ≤ GUpper s
  E_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Edelta s‖ ≤ EUpper s
  dominance_bounds :
    ∀ s : ℂ, s ∈ bulkRegion → GUpper s + EUpper s < K2Lower s / (1 + ‖q s‖)

noncomputable def RegionalVerticalBulkRouteData.restrict
    (data : RegionalVerticalBulkRouteData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion) :
    RegionalVerticalBulkRouteData where
  F := data.F
  bulkRegion := subRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := by
    intro _s hs
    exact data.bulk_offCritical (hsub hs)
  decomposition := by
    intro s hs
    exact data.decomposition s (hsub hs)
  resolvent_shape := by
    intro s hs
    exact data.resolvent_shape s (hsub hs)
  dominance := by
    intro s hs
    exact data.dominance s (hsub hs)

noncomputable def RegionalVerticalBulkBoundsData.restrict
    (data : RegionalVerticalBulkBoundsData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion) :
    RegionalVerticalBulkBoundsData where
  F := data.F
  bulkRegion := subRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  K2Lower := data.K2Lower
  GUpper := data.GUpper
  EUpper := data.EUpper
  bulk_offCritical := by
    intro _s hs
    exact data.bulk_offCritical (hsub hs)
  decomposition := by
    intro s hs
    exact data.decomposition s (hsub hs)
  resolvent_shape := by
    intro s hs
    exact data.resolvent_shape s (hsub hs)
  K2_lower := by
    intro s hs
    exact data.K2_lower s (hsub hs)
  G_upper := by
    intro s hs
    exact data.G_upper s (hsub hs)
  E_upper := by
    intro s hs
    exact data.E_upper s (hsub hs)
  dominance_bounds := by
    intro s hs
    exact data.dominance_bounds s (hsub hs)

noncomputable def GenuineFInfiniteRegionalBulkRouteData.ofRegionalVerticalBulkRouteData
    (data : RegionalVerticalBulkRouteData)
    (hF : ∀ s : ℂ, s ∈ data.bulkRegion → genuineFInfinite s = data.F s) :
    GenuineFInfiniteRegionalBulkRouteData where
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := by
    intro s hs
    rw [hF s hs]
    exact data.decomposition s hs
  resolvent_shape := data.resolvent_shape
  dominance := data.dominance

noncomputable def GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    (data : RegionalVerticalBulkBoundsData)
    (hF : ∀ s : ℂ, s ∈ data.bulkRegion → genuineFInfinite s = data.F s) :
    GenuineFInfiniteRegionalBulkBoundsData where
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  K2Lower := data.K2Lower
  GUpper := data.GUpper
  EUpper := data.EUpper
  bulk_offCritical := data.bulk_offCritical
  decomposition := by
    intro s hs
    rw [hF s hs]
    exact data.decomposition s hs
  resolvent_shape := data.resolvent_shape
  K2_lower := data.K2_lower
  G_upper := data.G_upper
  E_upper := data.E_upper
  dominance_bounds := data.dominance_bounds

noncomputable def GenuineFInfiniteRegionalBulkRouteData.ofRegionalVerticalBulkRouteDataOn
    (data : RegionalVerticalBulkRouteData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion)
    (hF : ∀ s : ℂ, s ∈ subRegion → genuineFInfinite s = data.F s) :
    GenuineFInfiniteRegionalBulkRouteData :=
  GenuineFInfiniteRegionalBulkRouteData.ofRegionalVerticalBulkRouteData
    (data.restrict subRegion hsub)
    (by
      intro s hs
      exact hF s hs)

noncomputable def GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsDataOn
    (data : RegionalVerticalBulkBoundsData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion)
    (hF : ∀ s : ℂ, s ∈ subRegion → genuineFInfinite s = data.F s) :
    GenuineFInfiniteRegionalBulkBoundsData :=
  GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    (data.restrict subRegion hsub)
    (by
      intro s hs
      exact hF s hs)

noncomputable def GenuineFInfiniteRegionalBulkRouteData.toRegionalVerticalBulkRouteData
    (data : GenuineFInfiniteRegionalBulkRouteData) : RegionalVerticalBulkRouteData where
  F := genuineFInfinite
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  dominance := data.dominance

noncomputable def GenuineFInfiniteRegionalBulkBoundsData.toRegionalVerticalBulkBoundsData
    (data : GenuineFInfiniteRegionalBulkBoundsData) : RegionalVerticalBulkBoundsData where
  F := genuineFInfinite
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  K2Lower := data.K2Lower
  GUpper := data.GUpper
  EUpper := data.EUpper
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  K2_lower := data.K2_lower
  G_upper := data.G_upper
  E_upper := data.E_upper
  dominance_bounds := data.dominance_bounds

noncomputable def GenuineFInfiniteRegionalBulkBoundsData.toRegionalBulkRouteData
    (data : GenuineFInfiniteRegionalBulkBoundsData) : GenuineFInfiniteRegionalBulkRouteData where
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  dominance := by
    intro s hs
    exact regionalVerticalBulk_dominance_of_bounds
      data.toRegionalVerticalBulkBoundsData hs

noncomputable def GenuineFInfiniteRegionalBulkRouteData.toPinnedBulkRouteData
    (data : GenuineFInfiniteRegionalBulkRouteData) : GenuineFInfiniteBulkRouteData where
  route := data.toRegionalVerticalBulkRouteData
  F_eq := rfl

noncomputable def GenuineFInfiniteRegionalBulkBoundsData.toPinnedBulkBoundsData
    (data : GenuineFInfiniteRegionalBulkBoundsData) : GenuineFInfiniteBulkBoundsData where
  bounds := data.toRegionalVerticalBulkBoundsData
  F_eq := rfl

theorem genuineFInfinite_nonvanishing_of_regionalBulkRouteData
    (data : GenuineFInfiniteRegionalBulkRouteData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    genuineFInfinite s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing data.toRegionalVerticalBulkRouteData hs

theorem genuineFInfinite_nonvanishing_of_regionalBulkBoundsData
    (data : GenuineFInfiniteRegionalBulkBoundsData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    genuineFInfinite s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    data.toRegionalVerticalBulkBoundsData hs

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_regionalBulkCover
    (continuation : GenuineFInfiniteContinuationData)
    (near : GenuineFInfiniteNearAxisData)
    (bulk : GenuineFInfiniteRegionalBulkRouteData)
    (edge : GenuineFInfiniteEdgeData)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_pinnedNearBulkEdge
    continuation
    { near := near
      bulk := bulk.toPinnedBulkRouteData
      edge := edge
      cover := cover }

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_regionalBulkBoundsCover
    (continuation : GenuineFInfiniteContinuationData)
    (near : GenuineFInfiniteNearAxisData)
    (bulk : GenuineFInfiniteRegionalBulkBoundsData)
    (edge : GenuineFInfiniteEdgeData)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_pinnedNearBulkBoundsEdge
    continuation
    { near := near
      bulk := bulk.toPinnedBulkBoundsData
      edge := edge
      cover := cover }

end C2
