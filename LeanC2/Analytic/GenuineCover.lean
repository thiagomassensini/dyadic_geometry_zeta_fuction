import LeanC2.Analytic.GenuineContinuation

namespace C2

/-!
Near/bulk/edge cover data pinned to the complete infinite genuine operator.

The generic roadmap allows an arbitrary numerator `F`.  This file gives the same
interfaces with `F` fixed to `genuineFInfinite`, so later concrete route packages
can feed the continuation bridge without carrying repeated equality arguments.
-/

/-- Near-axis route data specialized to the complete infinite genuine operator. -/
structure GenuineFInfiniteNearAxisData where
  near_axis : NearAxisCertificate genuineFInfinite riemannZeta

noncomputable def GenuineFInfiniteNearAxisData.toNearAxisRouteData
    (data : GenuineFInfiniteNearAxisData) : NearAxisRouteData where
  F := genuineFInfinite
  near_axis := data.near_axis

/-- Regional bulk route data whose numerator is identified with `genuineFInfinite`. -/
structure GenuineFInfiniteBulkRouteData where
  route : RegionalVerticalBulkRouteData
  F_eq : route.F = genuineFInfinite

/-- Bound-level bulk route data whose numerator is identified with `genuineFInfinite`. -/
structure GenuineFInfiniteBulkBoundsData where
  bounds : RegionalVerticalBulkBoundsData
  F_eq : bounds.F = genuineFInfinite

noncomputable def GenuineFInfiniteBulkBoundsData.toBulkRouteData
    (data : GenuineFInfiniteBulkBoundsData) : GenuineFInfiniteBulkRouteData where
  route := data.bounds.toRouteData
  F_eq := data.F_eq

/-- Edge route data specialized to the complete infinite genuine operator. -/
structure GenuineFInfiniteEdgeData where
  edgeRegion : Set ℂ
  edge_nonvanishing : ∀ {s : ℂ}, s ∈ edgeRegion → genuineFInfinite s ≠ 0

noncomputable def GenuineFInfiniteEdgeData.toEdgeRouteData
    (data : GenuineFInfiniteEdgeData) : EdgeRouteData where
  F := genuineFInfinite
  edgeRegion := data.edgeRegion
  edge_nonvanishing := data.edge_nonvanishing

/-- Near/bulk/edge cover package with route-level bulk data pinned to `genuineFInfinite`. -/
structure GenuineFInfiniteNearBulkEdgeData where
  near : GenuineFInfiniteNearAxisData
  bulk : GenuineFInfiniteBulkRouteData
  edge : GenuineFInfiniteEdgeData
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion

/-- Near/bulk/edge cover package with bound-level bulk data pinned to `genuineFInfinite`. -/
structure GenuineFInfiniteNearBulkBoundsEdgeData where
  near : GenuineFInfiniteNearAxisData
  bulk : GenuineFInfiniteBulkBoundsData
  edge : GenuineFInfiniteEdgeData
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion

noncomputable def GenuineFInfiniteNearBulkEdgeData.toOffCriticalCoverData
    (data : GenuineFInfiniteNearBulkEdgeData) : OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkEdge
    data.near.toNearAxisRouteData
    data.bulk.route
    data.edge.toEdgeRouteData
    (by
      simpa [GenuineFInfiniteNearAxisData.toNearAxisRouteData] using data.bulk.F_eq)
    rfl
    data.cover

noncomputable def GenuineFInfiniteNearBulkBoundsEdgeData.toOffCriticalCoverData
    (data : GenuineFInfiniteNearBulkBoundsEdgeData) : OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkBoundsEdge
    data.near.toNearAxisRouteData
    data.bulk.bounds
    data.edge.toEdgeRouteData
    (by
      simpa [GenuineFInfiniteNearAxisData.toNearAxisRouteData] using data.bulk.F_eq)
    rfl
    data.cover

theorem offCriticalStripNonvanishing_of_genuineFInfiniteNearBulkEdgeData
    (data : GenuineFInfiniteNearBulkEdgeData) :
    offCriticalStripNonvanishing genuineFInfinite := by
  simpa [GenuineFInfiniteNearBulkEdgeData.toOffCriticalCoverData,
    GenuineFInfiniteNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem offCriticalStripNonvanishing_of_genuineFInfiniteNearBulkBoundsEdgeData
    (data : GenuineFInfiniteNearBulkBoundsEdgeData) :
    offCriticalStripNonvanishing genuineFInfinite := by
  simpa [GenuineFInfiniteNearBulkBoundsEdgeData.toOffCriticalCoverData,
    GenuineFInfiniteNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_pinnedNearBulkEdge
    (continuation : GenuineFInfiniteContinuationData)
    (data : GenuineFInfiniteNearBulkEdgeData) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation continuation
    (offCriticalStripNonvanishing_of_genuineFInfiniteNearBulkEdgeData data)

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_pinnedNearBulkBoundsEdge
    (continuation : GenuineFInfiniteContinuationData)
    (data : GenuineFInfiniteNearBulkBoundsEdgeData) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation continuation
    (offCriticalStripNonvanishing_of_genuineFInfiniteNearBulkBoundsEdgeData data)

end C2
