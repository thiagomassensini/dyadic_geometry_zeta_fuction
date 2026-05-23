import LeanC2.Route.BulkErrors

namespace C2

/-- Cutoff upper bound in the route form `C(s) / X(s)`. -/
noncomputable def c2CutoffUpperFromScale
    (cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s => cutoffConstant s / cutoffScale s

/-- Constant-scale specialization of the cutoff bound `C(s) / X`. -/
noncomputable def c2CutoffUpperFromX
    (cutoffConstant : ℂ → ℝ) (X : ℝ) : ℂ → ℝ :=
  fun s => cutoffConstant s / X

theorem c2CutoffUpperFromScale_const
    (cutoffConstant : ℂ → ℝ) (X : ℝ) :
    c2CutoffUpperFromScale cutoffConstant (fun _ => X) =
      c2CutoffUpperFromX cutoffConstant X := by
  rfl

theorem c2Cutoff_bound_from_scaled
    {cutoffError : ℂ → ℂ} {cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < cutoffScale s)
    (hscaled : ‖cutoffError s‖ * cutoffScale s ≤ cutoffConstant s) :
    ‖cutoffError s‖ ≤ c2CutoffUpperFromScale cutoffConstant cutoffScale s := by
  unfold c2CutoffUpperFromScale
  exact (le_div_iff₀ hscale).mpr hscaled

theorem c2Cutoff_bound_from_scaled_const
    {cutoffError : ℂ → ℂ} {cutoffConstant : ℂ → ℝ} {X : ℝ} {s : ℂ}
    (hX : 0 < X)
    (hscaled : ‖cutoffError s‖ * X ≤ cutoffConstant s) :
    ‖cutoffError s‖ ≤ c2CutoffUpperFromX cutoffConstant X s := by
  unfold c2CutoffUpperFromX
  exact (le_div_iff₀ hX).mpr hscaled

/--
Bulk region where the cutoff estimate is supplied in scaled form:
`‖cutoffError s‖ * X(s) ≤ C(s)`, hence `‖cutoffError s‖ ≤ C(s)/X(s)`.
-/
def c2BulkScaledCutoffRegion
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | offCriticalStrip s ∧
    ‖tiltResidual s‖ ≤ tiltUpper s ∧
    ‖horizontalDefect s‖ ≤ horizontalUpper s ∧
    0 < cutoffScale s ∧
    ‖cutoffError s‖ * cutoffScale s ≤ cutoffConstant s ∧
    tiltUpper s + horizontalUpper s + cutoffConstant s / cutoffScale s <
      c2AnalyticBulkAllowance s}

theorem c2BulkScaledCutoff_mem_error_region
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledCutoffRegion
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper cutoffConstant cutoffScale) :
    s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper
      (c2CutoffUpperFromScale cutoffConstant cutoffScale) := by
  exact ⟨hs.1, hs.2.1, hs.2.2.1,
    c2Cutoff_bound_from_scaled hs.2.2.2.1 hs.2.2.2.2.1,
    by
      simpa [c2CutoffUpperFromScale] using hs.2.2.2.2.2⟩

/--
Regional bulk bounds when the cutoff component is provided as a `C/X` estimate.
-/
noncomputable def c2BulkScaledCutoffBoundsData
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData where
  F := c2AnalyticBulkF
    (c2BulkGdelta tiltResidual horizontalDefect)
    (c2BulkEdelta cutoffError)
  bulkRegion := c2BulkScaledCutoffRegion
    tiltResidual horizontalDefect cutoffError
    tiltUpper horizontalUpper cutoffConstant cutoffScale
  Kdelta := c2AnalyticBulkKdelta (c2BulkGdelta tiltResidual horizontalDefect)
  K2 := c2AnalyticBulkK2
  Gdelta := c2BulkGdelta tiltResidual horizontalDefect
  Edelta := c2BulkEdelta cutoffError
  K2Lower := c2AnalyticBulkK2Lower
  GUpper := c2BulkGUpper tiltUpper horizontalUpper
  EUpper := c2CutoffUpperFromScale cutoffConstant cutoffScale
  bulk_offCritical := by
    intro _s hs
    exact hs.1
  decomposition := by
    intro s _hs
    exact c2AnalyticBulk_decomposition
      (c2BulkGdelta tiltResidual horizontalDefect) (c2BulkEdelta cutoffError) s
  resolvent_shape := by
    intro _s hs
    exact c2AnalyticBulk_resolvent_shape
      (c2BulkErrors_mem_analytic_region
        (c2BulkScaledCutoff_mem_error_region hs))
  K2_lower := by
    intro s _hs
    rw [c2AnalyticBulk_K2Lower_eq_norm]
  G_upper := by
    intro _s hs
    exact c2BulkErrors_G_bound_of_mem
      (c2BulkScaledCutoff_mem_error_region hs)
  E_upper := by
    intro _s hs
    exact c2BulkErrors_E_bound_of_mem
      (c2BulkScaledCutoff_mem_error_region hs)
  dominance_bounds := by
    intro _s hs
    exact c2BulkErrors_dominance_bounds_of_mem
      (c2BulkScaledCutoff_mem_error_region hs)

noncomputable def c2BulkScaledCutoffRouteData
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkScaledCutoffBoundsData
    tiltResidual horizontalDefect cutoffError
    tiltUpper horizontalUpper cutoffConstant cutoffScale).toRouteData

theorem c2BulkScaledCutoff_nonvanishing_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledCutoffRegion
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta tiltResidual horizontalDefect)
      (c2BulkEdelta cutoffError) s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    (c2BulkScaledCutoffBoundsData
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper cutoffConstant cutoffScale) hs

end C2
