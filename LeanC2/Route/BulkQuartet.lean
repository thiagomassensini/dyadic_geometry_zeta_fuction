import LeanC2.Route.BulkErrors

namespace C2

/-!
Quartet-shaped bulk data.

This module refines the vertical bulk model by splitting the infinite vertical
tail into the four-floor prefix certified in `VerticalResolvent.lean` plus a
remaining vertical debt. The debt is absorbed into `Gδ`, so the resulting package
feeds the quartet dominance interface from `Roadmap.lean`.
-/

/-- Vertical debt left after extracting the four-floor prefix from depth two. -/
noncomputable def c2QuartetVerticalTail (s : ℂ) : ℂ :=
  q s ^ 6 * verticalResolvent s

/-- Explicit upper bound for the quartet vertical debt. -/
noncomputable def c2QuartetVerticalTailUpper (s : ℂ) : ℝ :=
  ‖q s‖ ^ 6 * (1 - ‖q s‖)⁻¹

theorem c2QuartetVerticalTail_norm_le_upper_of_re_pos
    (s : ℂ) (hs : 0 < s.re) :
    ‖c2QuartetVerticalTail s‖ ≤ c2QuartetVerticalTailUpper s := by
  simpa [c2QuartetVerticalTail, c2QuartetVerticalTailUpper] using
    verticalQuartetTail_norm_le_geometric_upper_of_re_pos s hs

/-- Quartet bulk numerator `K₂ = q²`. -/
noncomputable def c2QuartetBulkK2 (s : ℂ) : ℂ :=
  q s ^ 2

/-- Sharp scalar lower envelope for `K₂`. -/
noncomputable def c2QuartetBulkK2Lower (s : ℂ) : ℝ :=
  ‖q s‖ ^ 2

theorem c2QuartetBulkK2Lower_eq_norm (s : ℂ) :
    c2QuartetBulkK2Lower s = ‖c2QuartetBulkK2 s‖ := by
  unfold c2QuartetBulkK2Lower c2QuartetBulkK2
  rw [norm_pow]

/-- Structural quartet error: vertical debt plus the supplied analytic `Gδ`. -/
noncomputable def c2QuartetBulkGdelta (Gdelta : ℂ → ℂ) : ℂ → ℂ :=
  fun s => c2QuartetVerticalTail s + Gdelta s

/-- Scalar upper envelope for the quartet structural error. -/
noncomputable def c2QuartetBulkGUpper (GUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => c2QuartetVerticalTailUpper s + GUpper s

/-- Quartet-shaped `Kδ`: four-floor vertical prefix plus structural debt. -/
noncomputable def c2QuartetBulkKdelta (Gdelta : ℂ → ℂ) : ℂ → ℂ :=
  fun s => c2QuartetBulkK2 s * verticalQuartetPrefix (q s) +
    c2QuartetBulkGdelta Gdelta s

theorem c2QuartetBulk_quartet_shape (Gdelta : ℂ → ℂ) (s : ℂ) :
    c2QuartetBulkKdelta Gdelta s =
      c2QuartetBulkK2 s * verticalQuartetPrefix (q s) +
        c2QuartetBulkGdelta Gdelta s := by
  rfl

theorem c2QuartetAnalyticBulk_decomposition
    (Gdelta Edelta : ℂ → ℂ) {s : ℂ}
    (hs : 0 < s.re) :
    c2AnalyticBulkF Gdelta Edelta s =
      c2QuartetBulkKdelta Gdelta s + Edelta s := by
  unfold c2AnalyticBulkF c2QuartetBulkKdelta c2QuartetBulkK2
    c2QuartetBulkGdelta c2QuartetVerticalTail
  rw [verticalDepthTailFromTwo_eq_quartet_add_tail s hs]
  ring

theorem c2QuartetBulkGdelta_norm_le_upper_of_re_pos
    {Gdelta : ℂ → ℂ} {GUpper : ℂ → ℝ} {s : ℂ}
    (hs : 0 < s.re)
    (hG : ‖Gdelta s‖ ≤ GUpper s) :
    ‖c2QuartetBulkGdelta Gdelta s‖ ≤ c2QuartetBulkGUpper GUpper s := by
  unfold c2QuartetBulkGdelta c2QuartetBulkGUpper
  exact le_trans (norm_add_le _ _)
    (add_le_add (c2QuartetVerticalTail_norm_le_upper_of_re_pos s hs) hG)

/--
Quartet bulk region: the supplied `Gδ/Eδ` are controlled, and the sum of the
quartet vertical debt, structural error, and external error is dominated by the
four-floor vertical lower bound.
-/
def c2QuartetAnalyticBulkRegion
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) : Set ℂ :=
  {s | offCriticalStrip s ∧
    ‖Gdelta s‖ ≤ GUpper s ∧
    ‖Edelta s‖ ≤ EUpper s ∧
    c2QuartetBulkGUpper GUpper s + EUpper s <
      c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))}

/-- Bounds package for the quartet-shaped analytic bulk. -/
noncomputable def c2QuartetAnalyticBulkBoundsData
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) :
    RegionalVerticalQuartetBulkBoundsData where
  F := c2AnalyticBulkF Gdelta Edelta
  bulkRegion := c2QuartetAnalyticBulkRegion Gdelta Edelta GUpper EUpper
  Kdelta := c2QuartetBulkKdelta Gdelta
  K2 := c2QuartetBulkK2
  Gdelta := c2QuartetBulkGdelta Gdelta
  Edelta := Edelta
  K2Lower := c2QuartetBulkK2Lower
  GUpper := c2QuartetBulkGUpper GUpper
  EUpper := EUpper
  bulk_offCritical := by
    intro _s hs
    exact hs.1
  decomposition := by
    intro s hs
    exact c2QuartetAnalyticBulk_decomposition Gdelta Edelta hs.1.1
  quartet_shape := by
    intro s _hs
    exact c2QuartetBulk_quartet_shape Gdelta s
  K2_lower := by
    intro s _hs
    rw [c2QuartetBulkK2Lower_eq_norm]
  G_upper := by
    intro s hs
    exact c2QuartetBulkGdelta_norm_le_upper_of_re_pos hs.1.1 hs.2.1
  E_upper := by
    intro _s hs
    exact hs.2.2.1
  dominance_bounds := by
    intro _s hs
    exact hs.2.2.2

theorem c2QuartetAnalyticBulk_nonvanishing_of_mem
    {Gdelta Edelta : ℂ → ℂ} {GUpper EUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2QuartetAnalyticBulkRegion Gdelta Edelta GUpper EUpper) :
    c2AnalyticBulkF Gdelta Edelta s ≠ 0 := by
  exact regionalVerticalQuartetBulk_nonvanishing_of_bounds
    (c2QuartetAnalyticBulkBoundsData Gdelta Edelta GUpper EUpper) hs

/-!
### Quartet package for the real bulk error split
-/

def c2QuartetBulkErrorRegion
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) : Set ℂ :=
  c2QuartetAnalyticBulkRegion
    (c2BulkGdelta tiltResidual horizontalDefect)
    (c2BulkEdelta cutoffError)
    (c2BulkGUpper tiltUpper horizontalUpper)
    (c2BulkEUpper cutoffUpper)

noncomputable def c2QuartetBulkErrorsBoundsData
    (tiltResidual horizontalDefect cutoffError : ℂ → ℂ)
    (tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ) :
    RegionalVerticalQuartetBulkBoundsData :=
  c2QuartetAnalyticBulkBoundsData
    (c2BulkGdelta tiltResidual horizontalDefect)
    (c2BulkEdelta cutoffError)
    (c2BulkGUpper tiltUpper horizontalUpper)
    (c2BulkEUpper cutoffUpper)

theorem c2QuartetBulkErrors_nonvanishing_of_mem
    {tiltResidual horizontalDefect cutoffError : ℂ → ℂ}
    {tiltUpper horizontalUpper cutoffUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2QuartetBulkErrorRegion
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper cutoffUpper) :
    c2AnalyticBulkF
      (c2BulkGdelta tiltResidual horizontalDefect)
      (c2BulkEdelta cutoffError) s ≠ 0 := by
  exact regionalVerticalQuartetBulk_nonvanishing_of_bounds
    (c2QuartetBulkErrorsBoundsData
      tiltResidual horizontalDefect cutoffError
      tiltUpper horizontalUpper cutoffUpper)
    hs

end C2
