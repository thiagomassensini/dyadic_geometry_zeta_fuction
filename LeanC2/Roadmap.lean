import LeanC2.Foundations.Dyadic
import LeanC2.Operators.VerticalResolvent
import LeanC2.Operators.Tilt
import LeanC2.Route.Dominance
import LeanC2.Route.NearAxis
import LeanC2.Route.Transfer

namespace C2

/-!
Lean-facing roadmap for `rota_c_2_rh_referencia_lean.md`.

This file is intentionally small: it wires the route as interfaces instead of smuggling in
legacy-generated certificates.  The main work items are the fields of `GenuineRouteData`.
-/

/-- Abstract numerator named `F` in the notes: `F = D∞ - B∞`. -/
abbrev GenuineNumerator := Complex -> Complex

/--
Near-axis package before the bulk and edge steps are wired in.

This isolates the local transversal/Taylor/G11 output as a small interface over the
critical-line zeros of `riemannZeta`.
-/
structure NearAxisRouteData where
  F : GenuineNumerator
  near_axis : NearAxisCertificate F riemannZeta

theorem nearAxis_nonvanishing_of_nearAxisRouteData
    (data : NearAxisRouteData) {s : Complex}
    (hs : s ∈ nearAxisRegion riemannZeta data.near_axis.radius) :
    data.F s ≠ 0 := by
  exact data.near_axis.nonvanishing_of_mem hs

theorem offCriticalStrip_of_nearAxisRouteData
    (data : NearAxisRouteData) {s : Complex}
    (hs : s ∈ nearAxisRegion riemannZeta data.near_axis.radius) :
    offCriticalStrip s := by
  exact data.near_axis.offCriticalStrip_of_mem hs

/--
Bulk package for the resolvent non-cancellation stage.

This keeps the bulk step abstract: a resolvent-shaped decomposition plus a dominance
inequality already suffice to certify off-critical nonvanishing.
-/
structure BulkRouteData where
  F : GenuineNumerator
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  q : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  decomposition : ∀ s : Complex, F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : Complex, Kdelta s = K2 s / (1 - q s) + Gdelta s
  resolvent_lower :
    ∀ s : Complex, offCriticalStrip s → ‖K2 s‖ / (1 + ‖q s‖) ≤ ‖K2 s / (1 - q s)‖
  dominance :
    ∀ s : Complex, offCriticalStrip s → ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

theorem bulk_nonvanishing_of_bulkRouteData
    (data : BulkRouteData) {s : Complex} (hs : offCriticalStrip s) :
    data.F s ≠ 0 := by
  exact no_zero_of_resolvent_dominance_at s
    (F := data.F) (Kdelta := data.Kdelta) (K2 := data.K2) (q := data.q)
    (Gdelta := data.Gdelta) (Edelta := data.Edelta)
    (data.decomposition s) (data.resolvent_shape s) (data.resolvent_lower s hs)
    (data.dominance s hs)

theorem offCriticalStripNonvanishing_of_bulkRouteData
    (data : BulkRouteData) :
    offCriticalStripNonvanishing data.F := by
  intro s hs
  exact bulk_nonvanishing_of_bulkRouteData data hs

/--
Bulk package specialized to the vertical C2 resolvent already formalized in
`VerticalResolvent.lean`.

Compared to `BulkRouteData`, this structure no longer asks the caller to provide the
resolvent lower bound: it is supplied by `resolvent_lower_bound_of_offCriticalStrip`.
-/
structure VerticalBulkRouteData where
  F : GenuineNumerator
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  decomposition : ∀ s : Complex, F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : Complex, Kdelta s = K2 s / (1 - q s) + Gdelta s
  dominance :
    ∀ s : Complex, offCriticalStrip s → ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

noncomputable def VerticalBulkRouteData.toBulkRouteData
    (data : VerticalBulkRouteData) :
    BulkRouteData where
  F := data.F
  Kdelta := data.Kdelta
  K2 := data.K2
  q := q
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  resolvent_lower := by
    intro s hs
    have hbase := resolvent_lower_bound_of_offCriticalStrip s hs
    calc
      ‖data.K2 s‖ / (1 + ‖q s‖)
          = ‖data.K2 s‖ * (1 / (1 + ‖q s‖)) := by ring
      _ ≤ ‖data.K2 s‖ * ‖1 / (1 - q s)‖ := by
          exact mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
      _ = ‖data.K2 s / (1 - q s)‖ := by
          simp [div_eq_mul_inv]
  dominance := data.dominance

theorem verticalBulk_nonvanishing_of_verticalBulkRouteData
    (data : VerticalBulkRouteData) {s : Complex} (hs : offCriticalStrip s) :
    data.F s ≠ 0 := by
  exact bulk_nonvanishing_of_bulkRouteData data.toBulkRouteData hs

theorem offCriticalStripNonvanishing_of_verticalBulkRouteData
    (data : VerticalBulkRouteData) :
    offCriticalStripNonvanishing data.F := by
  intro s hs
  exact verticalBulk_nonvanishing_of_verticalBulkRouteData data hs

/--
Regional version of the vertical bulk package.

This is closer to the final near/bulk/edge route: the resolvent dominance only needs to
hold on the bulk region, not on the whole off-critical strip.
-/
structure RegionalVerticalBulkRouteData where
  F : GenuineNumerator
  bulkRegion : Set Complex
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  bulk_offCritical : ∀ {s : Complex}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : Complex, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : Complex, s ∈ bulkRegion → Kdelta s = K2 s / (1 - q s) + Gdelta s
  dominance :
    ∀ s : Complex, s ∈ bulkRegion → ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

theorem regionalVerticalBulk_nonvanishing
    (data : RegionalVerticalBulkRouteData) {s : Complex} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 := by
  refine no_zero_of_resolvent_dominance_at s
    (F := data.F) (Kdelta := data.Kdelta) (K2 := data.K2) (q := q)
    (Gdelta := data.Gdelta) (Edelta := data.Edelta)
    (data.decomposition s hs) (data.resolvent_shape s hs) ?_ (data.dominance s hs)
  have hbase := resolvent_lower_bound_of_offCriticalStrip s (data.bulk_offCritical hs)
  calc
    ‖data.K2 s‖ / (1 + ‖q s‖)
        = ‖data.K2 s‖ * (1 / (1 + ‖q s‖)) := by ring
    _ ≤ ‖data.K2 s‖ * ‖1 / (1 - q s)‖ := by
        exact mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
    _ = ‖data.K2 s / (1 - q s)‖ := by
        simp [div_eq_mul_inv]

/--
Bound-level regional bulk package.

Analytic estimates usually arrive as scalar lower/upper bounds. This structure records
that form and converts it into `RegionalVerticalBulkRouteData`.
-/
structure RegionalVerticalBulkBoundsData where
  F : GenuineNumerator
  bulkRegion : Set Complex
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  K2Lower : Complex → ℝ
  GUpper : Complex → ℝ
  EUpper : Complex → ℝ
  bulk_offCritical : ∀ {s : Complex}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : Complex, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : Complex, s ∈ bulkRegion → Kdelta s = K2 s / (1 - q s) + Gdelta s
  K2_lower : ∀ s : Complex, s ∈ bulkRegion → K2Lower s ≤ ‖K2 s‖
  G_upper : ∀ s : Complex, s ∈ bulkRegion → ‖Gdelta s‖ ≤ GUpper s
  E_upper : ∀ s : Complex, s ∈ bulkRegion → ‖Edelta s‖ ≤ EUpper s
  dominance_bounds :
    ∀ s : Complex, s ∈ bulkRegion → GUpper s + EUpper s < K2Lower s / (1 + ‖q s‖)

theorem regionalVerticalBulk_dominance_of_bounds
    (data : RegionalVerticalBulkBoundsData) {s : Complex} (hs : s ∈ data.bulkRegion) :
    ‖data.K2 s‖ / (1 + ‖q s‖) > ‖data.Gdelta s‖ + ‖data.Edelta s‖ := by
  have hden_nonneg : 0 ≤ 1 + ‖q s‖ := by positivity
  have hK :
      data.K2Lower s / (1 + ‖q s‖) ≤ ‖data.K2 s‖ / (1 + ‖q s‖) :=
    div_le_div_of_nonneg_right (data.K2_lower s hs) hden_nonneg
  have hGE : ‖data.Gdelta s‖ + ‖data.Edelta s‖ ≤ data.GUpper s + data.EUpper s :=
    add_le_add (data.G_upper s hs) (data.E_upper s hs)
  have hdom := data.dominance_bounds s hs
  linarith

noncomputable def RegionalVerticalBulkBoundsData.toRouteData
    (data : RegionalVerticalBulkBoundsData) :
    RegionalVerticalBulkRouteData where
  F := data.F
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
    exact regionalVerticalBulk_dominance_of_bounds data hs

theorem regionalVerticalBulk_nonvanishing_of_bounds
    (data : RegionalVerticalBulkBoundsData) {s : Complex} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing data.toRouteData hs

structure RegionalVerticalQuartetBulkRouteData where
  F : GenuineNumerator
  bulkRegion : Set Complex
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  bulk_offCritical : ∀ {s : Complex}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : Complex, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  quartet_shape :
    ∀ s : Complex, s ∈ bulkRegion →
      Kdelta s = K2 s * verticalQuartetPrefix (q s) + Gdelta s
  dominance :
    ∀ s : Complex, s ∈ bulkRegion →
      ‖K2 s‖ * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) > ‖Gdelta s‖ + ‖Edelta s‖

theorem regionalVerticalQuartetBulk_nonvanishing
    (data : RegionalVerticalQuartetBulkRouteData)
    {s : Complex} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 := by
  have hsOff : offCriticalStrip s := data.bulk_offCritical hs
  have hmainLower :
      ‖data.K2 s‖ * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) ≤
        ‖data.K2 s * verticalQuartetPrefix (q s)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (verticalQuartetPrefix_norm_lower_bound_of_offCriticalStrip s hsOff)
      (norm_nonneg _)
  have hdom :
      ‖data.Gdelta s‖ + ‖data.Edelta s‖ <
        ‖data.K2 s‖ * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) := by
    linarith [data.dominance s hs]
  have hmain :
      ‖data.Gdelta s‖ + ‖data.Edelta s‖ <
        ‖data.K2 s * verticalQuartetPrefix (q s)‖ := by
    exact lt_of_lt_of_le hdom hmainLower
  have hKG :
      ‖data.K2 s * verticalQuartetPrefix (q s)‖ - ‖data.Gdelta s‖ ≤ ‖data.Kdelta s‖ := by
    have hshape' :
        data.K2 s * verticalQuartetPrefix (q s) = data.Kdelta s - data.Gdelta s := by
      rw [data.quartet_shape s hs]
      ring
    have htri :
        ‖data.K2 s * verticalQuartetPrefix (q s)‖ ≤ ‖data.Kdelta s‖ + ‖data.Gdelta s‖ := by
      rw [hshape']
      simpa [sub_eq_add_neg, norm_neg] using norm_add_le (data.Kdelta s) (-data.Gdelta s)
    linarith
  have hE_lt_K : ‖data.Edelta s‖ < ‖data.Kdelta s‖ := by
    linarith
  exact no_zero_of_dominance
    (F := data.F s) (K := data.Kdelta s) (E := data.Edelta s)
    (L := ‖data.Kdelta s‖) (R := ‖data.Edelta s‖)
    (data.decomposition s hs) le_rfl le_rfl hE_lt_K

structure RegionalVerticalQuartetBulkBoundsData where
  F : GenuineNumerator
  bulkRegion : Set Complex
  Kdelta : Complex → Complex
  K2 : Complex → Complex
  Gdelta : Complex → Complex
  Edelta : Complex → Complex
  K2Lower : Complex → ℝ
  GUpper : Complex → ℝ
  EUpper : Complex → ℝ
  bulk_offCritical : ∀ {s : Complex}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : Complex, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  quartet_shape :
    ∀ s : Complex, s ∈ bulkRegion →
      Kdelta s = K2 s * verticalQuartetPrefix (q s) + Gdelta s
  K2_lower : ∀ s : Complex, s ∈ bulkRegion → K2Lower s ≤ ‖K2 s‖
  G_upper : ∀ s : Complex, s ∈ bulkRegion → ‖Gdelta s‖ ≤ GUpper s
  E_upper : ∀ s : Complex, s ∈ bulkRegion → ‖Edelta s‖ ≤ EUpper s
  dominance_bounds :
    ∀ s : Complex, s ∈ bulkRegion →
      GUpper s + EUpper s < K2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

theorem regionalVerticalQuartetBulk_dominance_of_bounds
    (data : RegionalVerticalQuartetBulkBoundsData)
    {s : Complex} (hs : s ∈ data.bulkRegion) :
    ‖data.K2 s‖ * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) > ‖data.Gdelta s‖ + ‖data.Edelta s‖ := by
  have hsOff : offCriticalStrip s := data.bulk_offCritical hs
  have hfloor_nonneg : 0 ≤ (1 - ‖q s‖) * (1 + ‖q s‖ ^ 2) := by
    have hq_lt_one : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hsOff
    have h1 : 0 ≤ 1 - ‖q s‖ := by linarith
    positivity
  have hK :
      data.K2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) ≤
        ‖data.K2 s‖ * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) := by
    exact mul_le_mul_of_nonneg_right (data.K2_lower s hs) hfloor_nonneg
  have hGE :
      ‖data.Gdelta s‖ + ‖data.Edelta s‖ ≤ data.GUpper s + data.EUpper s :=
    add_le_add (data.G_upper s hs) (data.E_upper s hs)
  have hdom :
      ‖data.Gdelta s‖ + ‖data.Edelta s‖ <
        data.K2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) :=
    lt_of_le_of_lt hGE (data.dominance_bounds s hs)
  exact lt_of_lt_of_le hdom hK

noncomputable def RegionalVerticalQuartetBulkBoundsData.toRouteData
    (data : RegionalVerticalQuartetBulkBoundsData) :
    RegionalVerticalQuartetBulkRouteData where
  F := data.F
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  quartet_shape := data.quartet_shape
  dominance := by
    intro s hs
    exact regionalVerticalQuartetBulk_dominance_of_bounds data hs

theorem regionalVerticalQuartetBulk_nonvanishing_of_bounds
    (data : RegionalVerticalQuartetBulkBoundsData)
    {s : Complex} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 := by
  exact regionalVerticalQuartetBulk_nonvanishing data.toRouteData hs

/-- Edge package for whatever edge/outer-strip argument is chosen later. -/
structure EdgeRouteData where
  F : GenuineNumerator
  edgeRegion : Set Complex
  edge_nonvanishing : ∀ {s : Complex}, s ∈ edgeRegion → F s ≠ 0

structure BulkRegionRouteData where
  F : GenuineNumerator
  bulkRegion : Set Complex
  bulk_nonvanishing : ∀ {s : Complex}, s ∈ bulkRegion → F s ≠ 0

def RegionalVerticalBulkRouteData.toBulkRegionRouteData
    (data : RegionalVerticalBulkRouteData) :
    BulkRegionRouteData where
  F := data.F
  bulkRegion := data.bulkRegion
  bulk_nonvanishing := by
    intro s hs
    exact regionalVerticalBulk_nonvanishing data hs

noncomputable def RegionalVerticalBulkBoundsData.toBulkRegionRouteData
    (data : RegionalVerticalBulkBoundsData) :
    BulkRegionRouteData :=
  data.toRouteData.toBulkRegionRouteData

def RegionalVerticalQuartetBulkRouteData.toBulkRegionRouteData
    (data : RegionalVerticalQuartetBulkRouteData) :
    BulkRegionRouteData where
  F := data.F
  bulkRegion := data.bulkRegion
  bulk_nonvanishing := by
    intro s hs
    exact regionalVerticalQuartetBulk_nonvanishing data hs

noncomputable def RegionalVerticalQuartetBulkBoundsData.toBulkRegionRouteData
    (data : RegionalVerticalQuartetBulkBoundsData) :
    BulkRegionRouteData :=
  data.toRouteData.toBulkRegionRouteData

/--
Abstract gluing package for the near-axis, bulk, and edge regions.

The heavy analytic work is reduced to two kinds of fields: the regions cover the
off-critical strip, and `F` is nonzero on each region.
-/
structure OffCriticalCoverData where
  F : GenuineNumerator
  nearRegion : Set Complex
  bulkRegion : Set Complex
  edgeRegion : Set Complex
  cover : ∀ s : Complex, offCriticalStrip s →
    s ∈ nearRegion ∨ s ∈ bulkRegion ∨ s ∈ edgeRegion
  near_nonvanishing : ∀ {s : Complex}, s ∈ nearRegion → F s ≠ 0
  bulk_nonvanishing : ∀ {s : Complex}, s ∈ bulkRegion → F s ≠ 0
  edge_nonvanishing : ∀ {s : Complex}, s ∈ edgeRegion → F s ≠ 0

theorem offCriticalStripNonvanishing_of_coverData
    (data : OffCriticalCoverData) :
    offCriticalStripNonvanishing data.F := by
  intro s hs
  rcases data.cover s hs with hNear | hBulk | hEdge
  · exact data.near_nonvanishing hNear
  · exact data.bulk_nonvanishing hBulk
  · exact data.edge_nonvanishing hEdge

def OffCriticalCoverData.ofNearBulkRegionEdge
    (near : NearAxisRouteData)
    (bulk : BulkRegionRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData where
  F := near.F
  nearRegion := nearAxisRegion riemannZeta near.near_axis.radius
  bulkRegion := bulk.bulkRegion
  edgeRegion := edge.edgeRegion
  cover := hcover
  near_nonvanishing := by
    intro s hs
    exact near.near_axis.nonvanishing_of_mem hs
  bulk_nonvanishing := by
    intro s hs
    simpa [hBulkF] using bulk.bulk_nonvanishing hs
  edge_nonvanishing := by
    intro s hs
    simpa [hEdgeF] using edge.edge_nonvanishing hs

def OffCriticalCoverData.ofNearBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

noncomputable def OffCriticalCoverData.ofNearBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

def OffCriticalCoverData.ofNearQuartetBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

noncomputable def OffCriticalCoverData.ofNearQuartetBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

theorem offCriticalStripNonvanishing_of_nearBulkRegionEdge
    (near : NearAxisRouteData)
    (bulk : BulkRegionRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing near.F := by
  exact offCriticalStripNonvanishing_of_coverData
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk edge hBulkF hEdgeF hcover)

theorem offCriticalStripNonvanishing_of_nearBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing near.F := by
  exact offCriticalStripNonvanishing_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

theorem offCriticalStripNonvanishing_of_nearBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing near.F := by
  exact offCriticalStripNonvanishing_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

theorem offCriticalStripNonvanishing_of_nearQuartetBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing near.F := by
  exact offCriticalStripNonvanishing_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

theorem offCriticalStripNonvanishing_of_nearQuartetBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    offCriticalStripNonvanishing near.F := by
  exact offCriticalStripNonvanishing_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover

/--
Minimal route package from the genuine numerator to RH.

The hard C2 work is `genuine_nonvanishing`; the analytic continuation identity is a named
interface and should later be supplied by the algebra/continuation modules.
-/
structure GenuineRouteData where
  F : GenuineNumerator
  identity : FundamentalIdentityOnRightHalfPlane F riemannZeta
  genuine_nonvanishing : offCriticalStripNonvanishing F

theorem mathlibRiemannHypothesis_of_genuineRouteData
    (data : GenuineRouteData) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_F_nonvanishing data.identity data.genuine_nonvanishing

def BulkRouteData.toGenuineRouteData
    (data : BulkRouteData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    GenuineRouteData where
  F := data.F
  identity := identity
  genuine_nonvanishing := offCriticalStripNonvanishing_of_bulkRouteData data

theorem mathlibRiemannHypothesis_of_bulkRouteData
    (data : BulkRouteData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData (data.toGenuineRouteData identity)

def VerticalBulkRouteData.toGenuineRouteData
    (data : VerticalBulkRouteData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    GenuineRouteData where
  F := data.F
  identity := identity
  genuine_nonvanishing := offCriticalStripNonvanishing_of_verticalBulkRouteData data

theorem mathlibRiemannHypothesis_of_verticalBulkRouteData
    (data : VerticalBulkRouteData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData (data.toGenuineRouteData identity)

def OffCriticalCoverData.toGenuineRouteData
    (data : OffCriticalCoverData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    GenuineRouteData where
  F := data.F
  identity := identity
  genuine_nonvanishing := offCriticalStripNonvanishing_of_coverData data

theorem mathlibRiemannHypothesis_of_coverData
    (data : OffCriticalCoverData)
    (identity : FundamentalIdentityOnRightHalfPlane data.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData (data.toGenuineRouteData identity)

theorem mathlibRiemannHypothesis_of_coverData_offCriticalIdentity
    (data : OffCriticalCoverData)
    (identity : FundamentalIdentityOnOffCriticalStrip data.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity
    identity (offCriticalStripNonvanishing_of_coverData data)

theorem mathlibRiemannHypothesis_of_nearBulkRegionEdge
    (near : NearAxisRouteData)
    (bulk : BulkRegionRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnRightHalfPlane near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk edge hBulkF hEdgeF hcover)
    identity

theorem mathlibRiemannHypothesis_of_nearBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnRightHalfPlane near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover
    identity

theorem mathlibRiemannHypothesis_of_nearBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnRightHalfPlane near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover
    identity

theorem mathlibRiemannHypothesis_of_nearQuartetBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnRightHalfPlane near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover identity

theorem mathlibRiemannHypothesis_of_nearQuartetBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnRightHalfPlane near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkRegionEdge near bulk.toBulkRegionRouteData edge
    hBulkF hEdgeF hcover identity

theorem mathlibRiemannHypothesis_of_nearBulkEdge_offCriticalIdentity
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnOffCriticalStrip near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
      hBulkF hEdgeF hcover)
    identity

theorem mathlibRiemannHypothesis_of_nearBulkBoundsEdge_offCriticalIdentity
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnOffCriticalStrip near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
      hBulkF hEdgeF hcover)
    identity

theorem mathlibRiemannHypothesis_of_nearQuartetBulkEdge_offCriticalIdentity
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnOffCriticalStrip near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
      hBulkF hEdgeF hcover)
    identity

theorem mathlibRiemannHypothesis_of_nearQuartetBulkBoundsEdge_offCriticalIdentity
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalQuartetBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion)
    (identity : FundamentalIdentityOnOffCriticalStrip near.F riemannZeta) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity
    (OffCriticalCoverData.ofNearBulkRegionEdge near bulk.toBulkRegionRouteData edge
      hBulkF hEdgeF hcover)
    identity

end C2
