import LeanC2.Roadmap

namespace C2

/-!
Part VII of `rota_c_2_rh_referencia_lean.md`: bulk resolvent non-cancellation via tilt.

This file isolates the route-level endpoint of the tilt argument.  The hard analytic
estimates still enter as explicit fields of the data structures below; once supplied,
Lean derives the nonvanishing statement from the tilt curvature, the vertical
resolvent, and the strict dominance inequality.
-/

/-- Roadmap notation `Θ_δ(c) = Δ²[n ↦ n^{-δ}](c)`. -/
noncomputable abbrev tiltTheta (δ c : ℝ) : ℝ :=
  bracket2 (tilt δ) c

theorem tiltTheta_zero (c : ℝ) :
    tiltTheta 0 c = 0 := by
  simpa [tiltTheta] using bracket_tilt_zero c

theorem tiltTheta_pos {δ c : ℝ} (hδ : 0 < δ) (hc : 1 < c) :
    0 < tiltTheta δ c := by
  simpa [tiltTheta] using bracket_tilt_pos (δ := δ) (c := c) hδ hc

theorem tiltTheta_neg {δ c : ℝ} (hδ1 : -1 < δ) (hδ2 : δ < 0) (hc : 1 < c) :
    tiltTheta δ c < 0 := by
  simpa [tiltTheta] using bracket_tilt_neg (δ := δ) (c := c) hδ1 hδ2 hc

theorem tiltTheta_zero_iff_delta_zero {δ c : ℝ} (hδlow : -1 < δ) (hc : 1 < c) :
    tiltTheta δ c = 0 ↔ δ = 0 := by
  simpa [tiltTheta] using bracket_tilt_zero_iff_delta_zero (δ := δ) (c := c) hδlow hc

/-- Bulk tilt displacement from the critical line. -/
noncomputable abbrev bulkTiltDelta (s : ℂ) : ℝ :=
  criticalOffset s

theorem bulkTiltDelta_gt_neg_one_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    -1 < bulkTiltDelta s := by
  simp [bulkTiltDelta, criticalOffset]
  linarith

theorem bulkTiltDelta_ne_zero_of_offCriticalStrip {s : ℂ} (hs : offCriticalStrip s) :
    bulkTiltDelta s ≠ 0 := by
  intro hδ
  apply hs.2.2
  have hδ' : s.re - (1 : ℝ) / 2 = 0 := by
    simpa [bulkTiltDelta, criticalOffset] using hδ
  linarith

theorem tiltTheta_ne_zero_of_offCriticalStrip {s : ℂ} {c : ℝ}
    (hs : offCriticalStrip s) (hc : 1 < c) :
    tiltTheta (bulkTiltDelta s) c ≠ 0 := by
  intro hzero
  have hδlow : -1 < bulkTiltDelta s :=
    bulkTiltDelta_gt_neg_one_of_re_pos hs.1
  have hδ0 := (tiltTheta_zero_iff_delta_zero (δ := bulkTiltDelta s) (c := c)
    hδlow hc).mp hzero
  exact bulkTiltDelta_ne_zero_of_offCriticalStrip hs hδ0

theorem tiltTheta_pos_of_re_gt_half {s : ℂ} {c : ℝ}
    (hs : (1 : ℝ) / 2 < s.re) (hc : 1 < c) :
    0 < tiltTheta (bulkTiltDelta s) c := by
  have hδ : 0 < bulkTiltDelta s := by
    simp [bulkTiltDelta, criticalOffset]
    linarith
  exact tiltTheta_pos hδ hc

theorem tiltTheta_neg_of_re_pos_of_re_lt_half {s : ℂ} {c : ℝ}
    (hs0 : 0 < s.re) (hs : s.re < (1 : ℝ) / 2) (hc : 1 < c) :
    tiltTheta (bulkTiltDelta s) c < 0 := by
  have hδlow : -1 < bulkTiltDelta s :=
    bulkTiltDelta_gt_neg_one_of_re_pos hs0
  have hδneg : bulkTiltDelta s < 0 := by
    simp [bulkTiltDelta, criticalOffset]
    linarith
  exact tiltTheta_neg hδlow hδneg hc

/--
Limit resolvent non-cancellation in the route notation.

Compared with `no_zero_of_resolvent_dominance_at`, this version supplies the
resolvent lower bound automatically from the off-critical-strip hypothesis and the
canonical C2 ratio `q`.
-/
theorem no_zero_of_resolvent_dominance_limit
    (s : ℂ) (hoff : offCriticalStrip s)
    {F Kdelta K2 Gdelta Edelta : ℂ → ℂ}
    (hdec : F s = Kdelta s + Edelta s)
    (hres : Kdelta s = K2 s / (1 - q s) + Gdelta s)
    (hdom : ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖) :
    F s ≠ 0 := by
  refine no_zero_of_resolvent_dominance_at s hdec hres ?_ hdom
  have hbase := resolvent_lower_bound_of_offCriticalStrip s hoff
  calc
    ‖K2 s‖ / (1 + ‖q s‖)
        = ‖K2 s‖ * (1 / (1 + ‖q s‖)) := by ring
    _ ≤ ‖K2 s‖ * ‖1 / (1 - q s)‖ := by
        exact mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
    _ = ‖K2 s / (1 - q s)‖ := by
        simp [div_eq_mul_inv]

/--
Regional bulk certificate for the tilt resolvent non-cancellation stage.

The `center` field identifies the real center `c` where the tilt curvature is
activated.  The nonvanishing proof below uses the resolvent and dominance fields;
the separate curvature theorem records that the tilt bracket cannot vanish at any
certified off-critical bulk point.
-/
structure BulkResolventNonCancellationTiltData where
  F : GenuineNumerator
  bulkRegion : Set ℂ
  center : ℂ → ℝ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  center_gt_one : ∀ {s : ℂ}, s ∈ bulkRegion → 1 < center s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion →
    Kdelta s = K2 s / (1 - q s) + Gdelta s
  dominance :
    ∀ s : ℂ, s ∈ bulkRegion → ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

theorem BulkResolventNonCancellationTiltData.tilt_curvature_ne_zero
    (data : BulkResolventNonCancellationTiltData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    tiltTheta (bulkTiltDelta s) (data.center s) ≠ 0 :=
  tiltTheta_ne_zero_of_offCriticalStrip (data.bulk_offCritical hs) (data.center_gt_one hs)

theorem BulkResolventNonCancellationTiltData.tilt_curvature_pos_of_re_gt_half
    (data : BulkResolventNonCancellationTiltData) {s : ℂ} (hs : s ∈ data.bulkRegion)
    (hhalf : (1 : ℝ) / 2 < s.re) :
    0 < tiltTheta (bulkTiltDelta s) (data.center s) :=
  tiltTheta_pos_of_re_gt_half hhalf (data.center_gt_one hs)

theorem BulkResolventNonCancellationTiltData.tilt_curvature_neg_of_re_lt_half
    (data : BulkResolventNonCancellationTiltData) {s : ℂ} (hs : s ∈ data.bulkRegion)
    (hhalf : s.re < (1 : ℝ) / 2) :
    tiltTheta (bulkTiltDelta s) (data.center s) < 0 :=
  tiltTheta_neg_of_re_pos_of_re_lt_half
    (data.bulk_offCritical hs).1 hhalf (data.center_gt_one hs)

noncomputable def BulkResolventNonCancellationTiltData.toRegionalVerticalBulkRouteData
    (data : BulkResolventNonCancellationTiltData) : RegionalVerticalBulkRouteData where
  F := data.F
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  dominance := data.dominance

theorem BulkResolventNonCancellationTiltData.nonvanishing
    (data : BulkResolventNonCancellationTiltData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 :=
  no_zero_of_resolvent_dominance_limit s (data.bulk_offCritical hs)
    (data.decomposition s hs) (data.resolvent_shape s hs) (data.dominance s hs)

/-- Roadmap spelling for the bulk zero-free conclusion from tilt resolvent non-cancellation data. -/
theorem bulk_nonzero_of_resolventNonCancellationTilt
    (data : BulkResolventNonCancellationTiltData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 :=
  data.nonvanishing hs

/-- Bound-level version of the same regional tilt resolvent non-cancellation certificate. -/
structure BulkResolventNonCancellationTiltBoundsData where
  F : GenuineNumerator
  bulkRegion : Set ℂ
  center : ℂ → ℝ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  K2Lower : ℂ → ℝ
  GUpper : ℂ → ℝ
  EUpper : ℂ → ℝ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  center_gt_one : ∀ {s : ℂ}, s ∈ bulkRegion → 1 < center s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion → F s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion →
    Kdelta s = K2 s / (1 - q s) + Gdelta s
  K2_lower : ∀ s : ℂ, s ∈ bulkRegion → K2Lower s ≤ ‖K2 s‖
  G_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Gdelta s‖ ≤ GUpper s
  E_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Edelta s‖ ≤ EUpper s
  dominance_bounds :
    ∀ s : ℂ, s ∈ bulkRegion → GUpper s + EUpper s < K2Lower s / (1 + ‖q s‖)

theorem BulkResolventNonCancellationTiltBoundsData.dominance
    (data : BulkResolventNonCancellationTiltBoundsData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    ‖data.K2 s‖ / (1 + ‖q s‖) > ‖data.Gdelta s‖ + ‖data.Edelta s‖ := by
  have hden_nonneg : 0 ≤ 1 + ‖q s‖ := by positivity
  have hK :
      data.K2Lower s / (1 + ‖q s‖) ≤ ‖data.K2 s‖ / (1 + ‖q s‖) :=
    div_le_div_of_nonneg_right (data.K2_lower s hs) hden_nonneg
  have hGE : ‖data.Gdelta s‖ + ‖data.Edelta s‖ ≤ data.GUpper s + data.EUpper s :=
    add_le_add (data.G_upper s hs) (data.E_upper s hs)
  have hdom := data.dominance_bounds s hs
  linarith

noncomputable def BulkResolventNonCancellationTiltBoundsData.toTiltData
    (data : BulkResolventNonCancellationTiltBoundsData) : BulkResolventNonCancellationTiltData where
  F := data.F
  bulkRegion := data.bulkRegion
  center := data.center
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  center_gt_one := data.center_gt_one
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  dominance := by
    intro s hs
    exact data.dominance hs

noncomputable def BulkResolventNonCancellationTiltBoundsData.toRegionalVerticalBulkBoundsData
    (data : BulkResolventNonCancellationTiltBoundsData) : RegionalVerticalBulkBoundsData where
  F := data.F
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

theorem BulkResolventNonCancellationTiltBoundsData.tilt_curvature_ne_zero
    (data : BulkResolventNonCancellationTiltBoundsData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    tiltTheta (bulkTiltDelta s) (data.center s) ≠ 0 :=
  data.toTiltData.tilt_curvature_ne_zero hs

theorem BulkResolventNonCancellationTiltBoundsData.nonvanishing
    (data : BulkResolventNonCancellationTiltBoundsData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 :=
  data.toTiltData.nonvanishing hs

/-- Roadmap spelling for the bulk zero-free conclusion from scalar estimate data. -/
theorem bulk_nonzero_of_resolventNonCancellationTilt_bounds
    (data : BulkResolventNonCancellationTiltBoundsData) {s : ℂ} (hs : s ∈ data.bulkRegion) :
    data.F s ≠ 0 :=
  data.nonvanishing hs

end C2
