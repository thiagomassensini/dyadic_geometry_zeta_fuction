import LeanC2.Route.BulkReal

namespace C2

/-- Bulk-side structural error: tilt residual plus horizontal defect in `m`. -/
noncomputable def c2BulkGdelta
    (tiltResidual horizontalDefect : ℂ → ℂ) : ℂ → ℂ :=
  fun s => tiltResidual s + horizontalDefect s

/-- External bulk error, reserved for the cutoff/certification residue. -/
noncomputable def c2BulkEdelta (cutoffError : ℂ → ℂ) : ℂ → ℂ :=
  cutoffError

/-- Scalar upper bound for the structural bulk error. -/
noncomputable def c2BulkGUpper
    (tiltUpper horizontalUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => tiltUpper s + horizontalUpper s

/-- Scalar upper bound for the cutoff/certification error. -/
noncomputable def c2BulkEUpper (cutoffUpper : ℂ → ℝ) : ℂ → ℝ :=
  cutoffUpper

/-- Positive margin after subtracting the three component bounds. -/
noncomputable def c2BulkErrorMargin
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) (s : ℂ) : ℝ :=
  c2AnalyticBulkAllowance s - (tiltUpper s + horizontalUpper s + cutoffUpper s)

/--
Bulk region with the real error bookkeeping split into the three components that
come from the route notes: tilt residual, horizontal defect in `m`, and cutoff error.
-/
def c2BulkErrorRegion
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) : Set ℂ :=
  {s | offCriticalStrip s ∧
    ‖tiltResidual s‖ ≤ tiltUpper s ∧
    ‖horizontalDefect s‖ ≤ horizontalUpper s ∧
    ‖cutoffError s‖ ≤ cutoffUpper s ∧
    tiltUpper s + horizontalUpper s + cutoffUpper s < c2AnalyticBulkAllowance s}

theorem c2BulkError_margin_pos_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    0 < c2BulkErrorMargin tiltUpper horizontalUpper cutoffUpper s := by
  unfold c2BulkErrorMargin
  linarith [hs.2.2.2.2]

theorem c2BulkErrors_G_bound_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    ‖c2BulkGdelta tiltResidual horizontalDefect s‖ ≤
      c2BulkGUpper tiltUpper horizontalUpper s := by
  unfold c2BulkGdelta c2BulkGUpper
  exact le_trans (norm_add_le (tiltResidual s) (horizontalDefect s))
    (add_le_add hs.2.1 hs.2.2.1)

theorem c2BulkErrors_E_bound_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    ‖c2BulkEdelta cutoffError s‖ ≤ c2BulkEUpper cutoffUpper s := by
  simpa [c2BulkEdelta, c2BulkEUpper] using hs.2.2.2.1

theorem c2BulkErrors_dominance_bounds_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    c2BulkGUpper tiltUpper horizontalUpper s + c2BulkEUpper cutoffUpper s <
      c2AnalyticBulkK2Lower s / (1 + ‖q s‖) := by
  simpa [c2BulkGUpper, c2BulkEUpper, c2AnalyticBulkK2Lower,
    c2AnalyticBulkAllowance] using hs.2.2.2.2

theorem c2BulkErrors_mem_analytic_region
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    s ∈ c2AnalyticBulkRegion
      (c2BulkGdelta tiltResidual horizontalDefect)
      (c2BulkEdelta cutoffError)
      (c2BulkGUpper tiltUpper horizontalUpper)
      (c2BulkEUpper cutoffUpper) := by
  exact ⟨hs.1, c2BulkErrors_G_bound_of_mem hs,
    c2BulkErrors_E_bound_of_mem hs,
    c2BulkErrors_dominance_bounds_of_mem hs⟩

/--
Concrete bulk-bounds package after splitting the analytic error into route-level
components: tilt residual, horizontal defect in `m`, and cutoff error.
-/
noncomputable def c2BulkErrorsBoundsData
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData where
  F := c2AnalyticBulkF
    (c2BulkGdelta tiltResidual horizontalDefect)
    (c2BulkEdelta cutoffError)
  bulkRegion := c2BulkErrorRegion
    tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper
  Kdelta := c2AnalyticBulkKdelta (c2BulkGdelta tiltResidual horizontalDefect)
  K2 := c2AnalyticBulkK2
  Gdelta := c2BulkGdelta tiltResidual horizontalDefect
  Edelta := c2BulkEdelta cutoffError
  K2Lower := c2AnalyticBulkK2Lower
  GUpper := c2BulkGUpper tiltUpper horizontalUpper
  EUpper := c2BulkEUpper cutoffUpper
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
      (c2BulkErrors_mem_analytic_region hs)
  K2_lower := by
    intro s _hs
    rw [c2AnalyticBulk_K2Lower_eq_norm]
  G_upper := by
    intro _s hs
    exact c2BulkErrors_G_bound_of_mem hs
  E_upper := by
    intro _s hs
    exact c2BulkErrors_E_bound_of_mem hs
  dominance_bounds := by
    intro _s hs
    exact c2BulkErrors_dominance_bounds_of_mem hs

noncomputable def c2BulkErrorsRouteData
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkErrorsBoundsData
    tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper).toRouteData

theorem c2BulkErrors_nonvanishing_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkErrorRegion
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) :
    c2AnalyticBulkF
      (c2BulkGdelta tiltResidual horizontalDefect)
      (c2BulkEdelta cutoffError) s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    (c2BulkErrorsBoundsData
      tiltResidual horizontalDefect cutoffError tiltUpper horizontalUpper cutoffUpper) hs

end C2
