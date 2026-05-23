import LeanC2.Route.BulkCutoff
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace C2

/-- Horizontal defect reconstructed from regularized layer errors in the `m` direction. -/
noncomputable def c2HorizontalRegularizedDefect
    (horizontalLayerDefect : ℂ → ℕ → ℂ) : ℂ → ℂ :=
  fun s => ∑' j : ℕ, horizontalLayerDefect s j

/-- Finite prefix of the horizontal layer-defect series. -/
noncomputable def c2HorizontalPartialSum
    (horizontalLayerDefect : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, horizontalLayerDefect s j

/-- Tail of the horizontal layer-defect series after the first `N` layers. -/
noncomputable def c2HorizontalTail
    (horizontalLayerDefect : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑' j : ℕ, horizontalLayerDefect s (j + N)

/-- Norm upper envelope of the horizontal tail after the first `N` layers. -/
noncomputable def c2HorizontalTailUpper
    (horizontalLayerDefect : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, ‖horizontalLayerDefect s (j + N)‖

/-- Concrete horizontal tail upper attached to a pointwise cutoff `horizontalCutoff s`. -/
noncomputable def c2ConcreteHorizontalTailUpper
    (horizontalLayerDefect : ℂ → ℕ → ℂ) (horizontalCutoff : ℂ → ℕ) : ℂ → ℝ :=
  fun s => c2HorizontalTailUpper horizontalLayerDefect s (horizontalCutoff s)

/-- Closed-form upper bound for a geometrically damped regularized horizontal defect. -/
noncomputable def c2HorizontalRegularizedUpper
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s => (horizontalConstant s / horizontalScale s) * (1 - horizontalRatio s)⁻¹

/-- Geometric upper bound for the horizontal tail past `horizontalCutoff s`. -/
noncomputable def c2HorizontalTailGeometricUpper
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (horizontalCutoff : ℂ → ℕ) : ℂ → ℝ :=
  fun s =>
    (horizontalConstant s / horizontalScale s) *
      horizontalRatio s ^ horizontalCutoff s * (1 - horizontalRatio s)⁻¹

/-- Constant-scale specialization of the regularized horizontal upper bound. -/
noncomputable def c2HorizontalRegularizedUpperFromX
    (horizontalConstant : ℂ → ℝ) (X r : ℝ) : ℂ → ℝ :=
  fun s => (horizontalConstant s / X) * (1 - r)⁻¹

theorem c2HorizontalRegularizedUpper_const
    (horizontalConstant : ℂ → ℝ) (X r : ℝ) :
    c2HorizontalRegularizedUpper horizontalConstant (fun _ => X) (fun _ => r) =
      c2HorizontalRegularizedUpperFromX horizontalConstant X r := by
  rfl

theorem c2HorizontalRegularizedDefect_eq_partial_add_tail_of_summable
    {horizontalLayerDefect : ℂ → ℕ → ℂ} {s : ℂ}
    (hsum : Summable fun j : ℕ => horizontalLayerDefect s j) (N : ℕ) :
    c2HorizontalRegularizedDefect horizontalLayerDefect s =
      c2HorizontalPartialSum horizontalLayerDefect s N +
        c2HorizontalTail horizontalLayerDefect s N := by
  unfold c2HorizontalRegularizedDefect c2HorizontalPartialSum c2HorizontalTail
  simpa using (hsum.sum_add_tsum_nat_add N).symm

theorem c2HorizontalTail_norm_le_upper
    {horizontalLayerDefect : ℂ → ℕ → ℂ} {s : ℂ}
    (hnorm : Summable fun j : ℕ => ‖horizontalLayerDefect s j‖) (N : ℕ) :
    ‖c2HorizontalTail horizontalLayerDefect s N‖ ≤
      c2HorizontalTailUpper horizontalLayerDefect s N := by
  unfold c2HorizontalTail c2HorizontalTailUpper
  have htail : Summable fun j : ℕ => ‖horizontalLayerDefect s (j + N)‖ :=
    hnorm.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa using norm_tsum_le_tsum_norm htail

theorem summable_norm_horizontalLayerDefect_of_geometric
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < horizontalScale s)
    (_hconstant : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖horizontalLayerDefect s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    Summable fun j : ℕ => ‖horizontalLayerDefect s j‖ := by
  have hgeom : Summable fun j : ℕ =>
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j := by
    have hbase := summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
    simpa using hbase.mul_left (horizontalConstant s / horizontalScale s)
  exact Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    hlayer
    hgeom

theorem summable_horizontalLayerDefect_of_geometric
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖horizontalLayerDefect s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    Summable fun j : ℕ => horizontalLayerDefect s j :=
  (summable_norm_horizontalLayerDefect_of_geometric
    hscale hconstant hratio_nonneg hratio_lt_one hlayer).of_norm

/--
Core regularized horizontal bound.

If each horizontal layer is bounded by `(C/X) * r^j`, with `0 ≤ r < 1`, then the
total horizontal defect is bounded by `(C/X) * (1-r)⁻¹`.
-/
theorem c2HorizontalRegularizedDefect_bound
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < horizontalScale s)
    (_hconstant : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖horizontalLayerDefect s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    ‖c2HorizontalRegularizedDefect horizontalLayerDefect s‖ ≤
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s := by
  unfold c2HorizontalRegularizedDefect c2HorizontalRegularizedUpper
  have hgeom : Summable fun j : ℕ => horizontalRatio s ^ j :=
    summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
  have hmajor :
      HasSum
        (fun j : ℕ =>
          (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
        ((horizontalConstant s / horizontalScale s) * (1 - horizontalRatio s)⁻¹) := by
    have hmul := hgeom.hasSum.mul_left (horizontalConstant s / horizontalScale s)
    simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one] using hmul
  exact tsum_of_norm_bounded hmajor hlayer

theorem c2ConcreteHorizontalTailUpper_le_geometric
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {horizontalCutoff : ℂ → ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < horizontalScale s)
    (_hconstant : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖horizontalLayerDefect s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    c2ConcreteHorizontalTailUpper horizontalLayerDefect horizontalCutoff s ≤
      c2HorizontalTailGeometricUpper
        horizontalConstant horizontalScale horizontalRatio horizontalCutoff s := by
  unfold c2ConcreteHorizontalTailUpper c2HorizontalTailGeometricUpper c2HorizontalTailUpper
  let base :=
    (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ horizontalCutoff s
  have hgeom : Summable fun j : ℕ => horizontalRatio s ^ j :=
    summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
  have hmajor : HasSum (fun j : ℕ => base * horizontalRatio s ^ j)
      (base * (1 - horizontalRatio s)⁻¹) := by
    simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one,
      base, pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (hgeom.hasSum.mul_left base)
  have hbound : ∀ j : ℕ,
      ‖‖horizontalLayerDefect s (j + horizontalCutoff s)‖‖ ≤
        base * horizontalRatio s ^ j := by
    intro j
    have hj := hlayer (j + horizontalCutoff s)
    simpa [base, pow_add, Real.norm_eq_abs, abs_of_nonneg, mul_assoc, mul_left_comm,
      mul_comm, div_nonneg, hratio_nonneg] using hj
  have hnorm_le : ‖∑' j : ℕ, ‖horizontalLayerDefect s (j + horizontalCutoff s)‖‖ ≤
      base * (1 - horizontalRatio s)⁻¹ := by
    exact tsum_of_norm_bounded hmajor hbound
  have hnonneg : 0 ≤ ∑' j : ℕ, ‖horizontalLayerDefect s (j + horizontalCutoff s)‖ := by
    exact tsum_nonneg fun _ => norm_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm_le

/--
Named hypotheses for the bulk region where the horizontal defect is supplied as a
regularized geometric layer bound.
-/
structure C2BulkRegularizedHorizontalHypotheses
    (tiltResidual cutoffError : ℂ → ℂ)
    (horizontalLayerDefect : ℂ → ℕ → ℂ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tilt_bound : ‖tiltResidual s‖ ≤ tiltUpper s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖horizontalLayerDefect s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound : ‖cutoffError s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    tiltUpper s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/--
Bulk region with the horizontal defect regularized by a geometrically damped layer
estimate and the cutoff still supplied in scaled `C/X` form.
-/
def c2BulkRegularizedHorizontalRegion
    (tiltResidual cutoffError : ℂ → ℂ)
    (horizontalLayerDefect : ℂ → ℕ → ℂ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkRegularizedHorizontalHypotheses
    tiltResidual cutoffError horizontalLayerDefect
    tiltUpper horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkRegularizedHorizontal_mem_scaled_cutoff_region
    {tiltResidual cutoffError : ℂ → ℂ}
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkRegularizedHorizontalRegion
      tiltResidual cutoffError horizontalLayerDefect
      tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledCutoffRegion
      tiltResidual
      (c2HorizontalRegularizedDefect horizontalLayerDefect)
      cutoffError
      tiltUpper
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      cutoffConstant
      cutoffScale := by
  exact ⟨hs.offCritical, hs.tilt_bound,
    c2HorizontalRegularizedDefect_bound
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one
      hs.horizontalLayer_bound,
    hs.cutoffScale_pos, hs.cutoff_scaled_bound, hs.dominance⟩

/--
Bulk bounds package with a regularized horizontal defect and scaled cutoff. This is
the route-level form of the `m`-defect estimate.
-/
noncomputable def c2BulkRegularizedHorizontalBoundsData
    (tiltResidual cutoffError : ℂ → ℂ)
    (horizontalLayerDefect : ℂ → ℕ → ℂ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData where
  F := c2AnalyticBulkF
    (c2BulkGdelta tiltResidual
      (c2HorizontalRegularizedDefect horizontalLayerDefect))
    (c2BulkEdelta cutoffError)
  bulkRegion := c2BulkRegularizedHorizontalRegion
    tiltResidual cutoffError horizontalLayerDefect
    tiltUpper horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
  Kdelta := c2AnalyticBulkKdelta
    (c2BulkGdelta tiltResidual
      (c2HorizontalRegularizedDefect horizontalLayerDefect))
  K2 := c2AnalyticBulkK2
  Gdelta := c2BulkGdelta tiltResidual
    (c2HorizontalRegularizedDefect horizontalLayerDefect)
  Edelta := c2BulkEdelta cutoffError
  K2Lower := c2AnalyticBulkK2Lower
  GUpper := c2BulkGUpper tiltUpper
    (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
  EUpper := c2CutoffUpperFromScale cutoffConstant cutoffScale
  bulk_offCritical := by
    intro _s hs
    exact hs.offCritical
  decomposition := by
    intro s _hs
    exact c2AnalyticBulk_decomposition
      (c2BulkGdelta tiltResidual
        (c2HorizontalRegularizedDefect horizontalLayerDefect))
      (c2BulkEdelta cutoffError) s
  resolvent_shape := by
    intro _s hs
    exact c2AnalyticBulk_resolvent_shape
      (c2BulkErrors_mem_analytic_region
        (c2BulkScaledCutoff_mem_error_region
          (c2BulkRegularizedHorizontal_mem_scaled_cutoff_region hs)))
  K2_lower := by
    intro s _hs
    rw [c2AnalyticBulk_K2Lower_eq_norm]
  G_upper := by
    intro _s hs
    exact c2BulkErrors_G_bound_of_mem
      (c2BulkScaledCutoff_mem_error_region
        (c2BulkRegularizedHorizontal_mem_scaled_cutoff_region hs))
  E_upper := by
    intro _s hs
    exact c2BulkErrors_E_bound_of_mem
      (c2BulkScaledCutoff_mem_error_region
        (c2BulkRegularizedHorizontal_mem_scaled_cutoff_region hs))
  dominance_bounds := by
    intro _s hs
    exact c2BulkErrors_dominance_bounds_of_mem
      (c2BulkScaledCutoff_mem_error_region
        (c2BulkRegularizedHorizontal_mem_scaled_cutoff_region hs))

noncomputable def c2BulkRegularizedHorizontalRouteData
    (tiltResidual cutoffError : ℂ → ℂ)
    (horizontalLayerDefect : ℂ → ℕ → ℂ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkRegularizedHorizontalBoundsData
    tiltResidual cutoffError horizontalLayerDefect
    tiltUpper horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkRegularizedHorizontal_nonvanishing_of_mem
    {tiltResidual cutoffError : ℂ → ℂ}
    {horizontalLayerDefect : ℂ → ℕ → ℂ}
    {tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkRegularizedHorizontalRegion
      tiltResidual cutoffError horizontalLayerDefect
      tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta tiltResidual
        (c2HorizontalRegularizedDefect horizontalLayerDefect))
      (c2BulkEdelta cutoffError) s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    (c2BulkRegularizedHorizontalBoundsData
      tiltResidual cutoffError horizontalLayerDefect
      tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) hs

end C2
