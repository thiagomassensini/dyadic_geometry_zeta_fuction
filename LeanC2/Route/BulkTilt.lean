import LeanC2.Route.BulkConcrete
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace C2

/-- Tilt residual reconstructed from regularized layer residuals. -/
noncomputable def c2TiltRegularizedResidual
    (tiltLayerResidual : ℂ → ℕ → ℂ) : ℂ → ℂ :=
  fun s => ∑' j : ℕ, tiltLayerResidual s j

/-- Finite prefix of the tilt layer residual series. -/
noncomputable def c2TiltPartialSum
    (tiltLayerResidual : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, tiltLayerResidual s j

/-- Tail of the tilt layer residual series after the first `N` layers. -/
noncomputable def c2TiltTail
    (tiltLayerResidual : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑' j : ℕ, tiltLayerResidual s (j + N)

/-- Norm upper envelope of the tilt tail after the first `N` layers. -/
noncomputable def c2TiltTailUpper
    (tiltLayerResidual : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, ‖tiltLayerResidual s (j + N)‖

/-- Truncation error left after removing the first `N` tilt layers. -/
noncomputable def c2TiltTruncationError
    (tiltLayerResidual : ℂ → ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  c2TiltRegularizedResidual tiltLayerResidual s - c2TiltPartialSum tiltLayerResidual s N

/-- Concrete finite tilt residual obtained by truncating the layer sum at `tiltCutoff s`. -/
noncomputable def c2ConcreteTiltPartialResidual
    (tiltLayerResidual : ℂ → ℕ → ℂ) (tiltCutoff : ℂ → ℕ) : ℂ → ℂ :=
  fun s => c2TiltPartialSum tiltLayerResidual s (tiltCutoff s)

/-- Base tilt seed extracted from the zeroth layer `j = 0`. -/
noncomputable def c2TiltBaseSeed
    (tiltLayerResidual : ℂ → ℕ → ℂ) : ℂ → ℂ :=
  fun s => tiltLayerResidual s 0

/-- Concrete tilt tail error left after truncating the layer sum at `tiltCutoff s`. -/
noncomputable def c2ConcreteTiltTailError
    (tiltLayerResidual : ℂ → ℕ → ℂ) (tiltCutoff : ℂ → ℕ) : ℂ → ℂ :=
  fun s => c2TiltTruncationError tiltLayerResidual s (tiltCutoff s)

/-- Canonical tail upper bound attached to the concrete tilt truncation `tiltCutoff s`. -/
noncomputable def c2ConcreteTiltTailUpper
    (tiltLayerResidual : ℂ → ℕ → ℂ) (tiltCutoff : ℂ → ℕ) : ℂ → ℝ :=
  fun s => c2TiltTailUpper tiltLayerResidual s (tiltCutoff s)

@[simp] theorem c2ConcreteTiltPartialResidual_one_eq_baseSeed
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ} :
    c2ConcreteTiltPartialResidual tiltLayerResidual (fun _ => 1) s =
      c2TiltBaseSeed tiltLayerResidual s := by
  simp [c2ConcreteTiltPartialResidual, c2TiltPartialSum, c2TiltBaseSeed]

@[simp] theorem c2TiltBaseSeed_norm_eq_partialResidual_one
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ} :
    ‖c2TiltBaseSeed tiltLayerResidual s‖ =
      ‖c2ConcreteTiltPartialResidual tiltLayerResidual (fun _ => 1) s‖ := by
  simp

theorem c2TiltBaseSeed_scaled_bound_of_partialResidual_one
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hpartial :
      ‖c2ConcreteTiltPartialResidual tiltLayerResidual (fun _ => 1) s‖ *
        tiltScale s ≤ tiltConstant s) :
    ‖c2TiltBaseSeed tiltLayerResidual s‖ * tiltScale s ≤ tiltConstant s := by
  simpa using hpartial

/-- Geometric upper bound for the finite tilt prefix up to `tiltCutoff s`. -/
noncomputable def c2TiltPartialGeometricUpper
    (tiltConstant tiltScale tiltRatio : ℂ → ℝ)
    (tiltCutoff : ℂ → ℕ) : ℂ → ℝ :=
  fun s =>
    ∑ j ∈ Finset.range (tiltCutoff s),
      (tiltConstant s / tiltScale s) * tiltRatio s ^ j

/-- Geometric upper bound for the tilt tail past `tiltCutoff s`. -/
noncomputable def c2TiltTailGeometricUpper
    (tiltConstant tiltScale tiltRatio : ℂ → ℝ)
    (tiltCutoff : ℂ → ℕ) : ℂ → ℝ :=
  fun s =>
    (tiltConstant s / tiltScale s) * tiltRatio s ^ tiltCutoff s * (1 - tiltRatio s)⁻¹

/-- Closed-form upper bound for a geometrically damped tilt residual. -/
noncomputable def c2TiltRegularizedUpper
    (tiltConstant tiltScale tiltRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s => (tiltConstant s / tiltScale s) * (1 - tiltRatio s)⁻¹

/-- Constant-scale specialization of the tilt residual upper bound. -/
noncomputable def c2TiltRegularizedUpperFromX
    (tiltConstant : ℂ → ℝ) (X r : ℝ) : ℂ → ℝ :=
  fun s => (tiltConstant s / X) * (1 - r)⁻¹

theorem c2TiltRegularizedUpper_const
    (tiltConstant : ℂ → ℝ) (X r : ℝ) :
    c2TiltRegularizedUpper tiltConstant (fun _ => X) (fun _ => r) =
      c2TiltRegularizedUpperFromX tiltConstant X r := by
  rfl

theorem c2TiltRegularizedResidual_eq_partial_add_tail_of_summable
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ}
    (hsum : Summable fun j : ℕ => tiltLayerResidual s j) (N : ℕ) :
    c2TiltRegularizedResidual tiltLayerResidual s =
      c2TiltPartialSum tiltLayerResidual s N + c2TiltTail tiltLayerResidual s N := by
  unfold c2TiltRegularizedResidual c2TiltPartialSum c2TiltTail
  simpa using (hsum.sum_add_tsum_nat_add N).symm

theorem c2TiltTruncationError_eq_tail_of_summable
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ}
    (hsum : Summable fun j : ℕ => tiltLayerResidual s j) (N : ℕ) :
    c2TiltTruncationError tiltLayerResidual s N = c2TiltTail tiltLayerResidual s N := by
  unfold c2TiltTruncationError
  rw [c2TiltRegularizedResidual_eq_partial_add_tail_of_summable hsum N]
  ring

theorem c2TiltTail_norm_le_upper
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ}
    (hnorm : Summable fun j : ℕ => ‖tiltLayerResidual s j‖) (N : ℕ) :
    ‖c2TiltTail tiltLayerResidual s N‖ ≤ c2TiltTailUpper tiltLayerResidual s N := by
  unfold c2TiltTail c2TiltTailUpper
  have htail : Summable fun j : ℕ => ‖tiltLayerResidual s (j + N)‖ :=
    hnorm.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa using norm_tsum_le_tsum_norm htail

theorem c2TiltTruncationError_norm_le_tailUpper_of_summable
    {tiltLayerResidual : ℂ → ℕ → ℂ} {s : ℂ}
    (hsum : Summable fun j : ℕ => tiltLayerResidual s j)
    (hnorm : Summable fun j : ℕ => ‖tiltLayerResidual s j‖) (N : ℕ) :
    ‖c2TiltTruncationError tiltLayerResidual s N‖ ≤
      c2TiltTailUpper tiltLayerResidual s N := by
  rw [c2TiltTruncationError_eq_tail_of_summable hsum N]
  exact c2TiltTail_norm_le_upper hnorm N

theorem c2TiltTruncationError_bound_of_tailUpper
    {tiltLayerResidual : ℂ → ℕ → ℂ} {tiltTruncationUpper : ℂ → ℕ → ℝ} {s : ℂ}
    (hsum : Summable fun j : ℕ => tiltLayerResidual s j)
    (hnorm : Summable fun j : ℕ => ‖tiltLayerResidual s j‖)
    (htail : ∀ N : ℕ,
      c2TiltTailUpper tiltLayerResidual s N ≤ tiltTruncationUpper s N) :
    ∀ N : ℕ,
      ‖c2TiltTruncationError tiltLayerResidual s N‖ ≤ tiltTruncationUpper s N := by
  intro N
  exact le_trans
    (c2TiltTruncationError_norm_le_tailUpper_of_summable hsum hnorm N)
    (htail N)

theorem c2ConcreteTiltPartialResidual_norm_le_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < tiltScale s)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * tiltRatio s ^ j) :
    ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s‖ ≤
      c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s := by
  unfold c2ConcreteTiltPartialResidual c2TiltPartialGeometricUpper c2TiltPartialSum
  calc
    ‖∑ j ∈ Finset.range (tiltCutoff s), tiltLayerResidual s j‖
      ≤ ∑ j ∈ Finset.range (tiltCutoff s), ‖tiltLayerResidual s j‖ := by
          simpa using
            (norm_sum_le (Finset.range (tiltCutoff s)) (fun j => tiltLayerResidual s j))
    _ ≤ ∑ j ∈ Finset.range (tiltCutoff s),
          (tiltConstant s / tiltScale s) * tiltRatio s ^ j := by
            exact Finset.sum_le_sum fun j _hj => hlayer j
    _ = c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s := by
          rfl

theorem c2ConcreteTiltTailUpper_le_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < tiltScale s)
    (_hconstant : 0 ≤ tiltConstant s)
    (hratio_nonneg : 0 ≤ tiltRatio s)
    (hratio_lt_one : tiltRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * tiltRatio s ^ j) :
    c2ConcreteTiltTailUpper tiltLayerResidual tiltCutoff s ≤
      c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s := by
  unfold c2ConcreteTiltTailUpper c2TiltTailGeometricUpper c2TiltTailUpper
  let base := (tiltConstant s / tiltScale s) * tiltRatio s ^ tiltCutoff s
  have hgeom : Summable fun j : ℕ => tiltRatio s ^ j :=
    summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
  have hmajor : HasSum (fun j : ℕ => base * tiltRatio s ^ j)
      (base * (1 - tiltRatio s)⁻¹) := by
    simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one,
      base, pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (hgeom.hasSum.mul_left base)
  have hbound : ∀ j : ℕ,
      ‖‖tiltLayerResidual s (j + tiltCutoff s)‖‖ ≤ base * tiltRatio s ^ j := by
    intro j
    have hj := hlayer (j + tiltCutoff s)
    simpa [base, pow_add, Real.norm_eq_abs, abs_of_nonneg, mul_assoc, mul_left_comm, mul_comm,
      div_nonneg, hratio_nonneg] using hj
  have hnorm_le : ‖∑' j : ℕ, ‖tiltLayerResidual s (j + tiltCutoff s)‖‖ ≤
      base * (1 - tiltRatio s)⁻¹ := by
    exact tsum_of_norm_bounded hmajor hbound
  have hnonneg : 0 ≤ ∑' j : ℕ, ‖tiltLayerResidual s (j + tiltCutoff s)‖ := by
    exact tsum_nonneg fun _ => norm_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm_le

theorem c2TiltPartialGeometricUpper_add_tail_eq_regularized
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (hratio_nonneg : 0 ≤ tiltRatio s)
    (hratio_lt_one : tiltRatio s < 1) :
    c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s +
      c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s =
        c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s := by
  let coeff : ℝ := tiltConstant s / tiltScale s
  have hgeom : Summable (fun j : ℕ => coeff * tiltRatio s ^ j) := by
    simpa [coeff] using
      (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left coeff
  have htotal :
      HasSum (fun j : ℕ => coeff * tiltRatio s ^ j) (coeff * (1 - tiltRatio s)⁻¹) := by
    simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one] using
      ((summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).hasSum.mul_left coeff)
  have hsplit := (hgeom.sum_add_tsum_nat_add (tiltCutoff s)).symm
  have htail :
      (∑' j : ℕ, coeff * tiltRatio s ^ (j + tiltCutoff s)) =
        coeff * tiltRatio s ^ tiltCutoff s * (1 - tiltRatio s)⁻¹ := by
    have htail_hasSum :
        HasSum
          (fun j : ℕ => (coeff * tiltRatio s ^ tiltCutoff s) * tiltRatio s ^ j)
          ((coeff * tiltRatio s ^ tiltCutoff s) * (1 - tiltRatio s)⁻¹) := by
      simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one] using
        ((summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).hasSum.mul_left
          (coeff * tiltRatio s ^ tiltCutoff s))
    simpa [coeff, pow_add, mul_assoc, mul_left_comm, mul_comm] using htail_hasSum.tsum_eq
  unfold c2TiltPartialGeometricUpper c2TiltTailGeometricUpper c2TiltRegularizedUpper
  change (∑ j ∈ Finset.range (tiltCutoff s), coeff * tiltRatio s ^ j) +
      coeff * tiltRatio s ^ tiltCutoff s * (1 - tiltRatio s)⁻¹ =
        coeff * (1 - tiltRatio s)⁻¹
  rw [← htail, ← hsplit]
  simpa [coeff] using htotal.tsum_eq

theorem summable_norm_tiltLayerResidual_of_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < tiltScale s)
    (_hconstant : 0 ≤ tiltConstant s)
    (hratio_nonneg : 0 ≤ tiltRatio s)
    (hratio_lt_one : tiltRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * tiltRatio s ^ j) :
    Summable fun j : ℕ => ‖tiltLayerResidual s j‖ := by
  have hgeom : Summable fun j : ℕ =>
      (tiltConstant s / tiltScale s) * tiltRatio s ^ j := by
    have hbase := summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
    simpa using hbase.mul_left (tiltConstant s / tiltScale s)
  exact Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    hlayer
    hgeom

theorem summable_tiltLayerResidual_of_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < tiltScale s)
    (hconstant : 0 ≤ tiltConstant s)
    (hratio_nonneg : 0 ≤ tiltRatio s)
    (hratio_lt_one : tiltRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * tiltRatio s ^ j) :
    Summable fun j : ℕ => tiltLayerResidual s j :=
  (summable_norm_tiltLayerResidual_of_geometric
    hscale hconstant hratio_nonneg hratio_lt_one hlayer).of_norm

theorem c2TiltRegularizedResidual_eq_concrete_partial_add_tail
    {tiltLayerResidual : ℂ → ℕ → ℂ} {tiltCutoff : ℂ → ℕ} {s : ℂ} :
    c2TiltRegularizedResidual tiltLayerResidual s =
      c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s +
        c2ConcreteTiltTailError tiltLayerResidual tiltCutoff s := by
  unfold c2ConcreteTiltPartialResidual c2ConcreteTiltTailError c2TiltTruncationError
  ring

theorem c2TiltRegularizedResidual_bound_of_partial_and_tail
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {tiltPartialUpper tiltTailUpper : ℂ → ℝ} {s : ℂ}
    (hsum : Summable fun j : ℕ => tiltLayerResidual s j)
    (hnorm : Summable fun j : ℕ => ‖tiltLayerResidual s j‖)
    (hpartial : ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s‖ ≤
      tiltPartialUpper s)
    (htail : c2ConcreteTiltTailUpper tiltLayerResidual tiltCutoff s ≤ tiltTailUpper s) :
    ‖c2TiltRegularizedResidual tiltLayerResidual s‖ ≤ tiltPartialUpper s + tiltTailUpper s := by
  rw [c2TiltRegularizedResidual_eq_concrete_partial_add_tail]
  calc
    ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s +
        c2ConcreteTiltTailError tiltLayerResidual tiltCutoff s‖
      ≤ ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s‖ +
          ‖c2ConcreteTiltTailError tiltLayerResidual tiltCutoff s‖ :=
            norm_add_le _ _
    _ ≤ tiltPartialUpper s + c2ConcreteTiltTailUpper tiltLayerResidual tiltCutoff s := by
          gcongr
          exact c2TiltTruncationError_norm_le_tailUpper_of_summable hsum hnorm (tiltCutoff s)
    _ ≤ tiltPartialUpper s + tiltTailUpper s := by gcongr

/--
Concrete bulk hypotheses where the tilt input is split into a finite partial sum plus
an explicit tail upper bound at a truncation `tiltCutoff s`.
-/
structure C2BulkConcreteTruncatedTiltHypotheses
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltSummable : Summable fun j : ℕ => tiltLayerResidual s j
  tiltNormSummable : Summable fun j : ℕ => ‖tiltLayerResidual s j‖
  tiltPartial_bound :
    ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s‖ ≤ tiltPartialUpper s
  tiltTail_bound :
    c2ConcreteTiltTailUpper tiltLayerResidual tiltCutoff s ≤ tiltTailUpper s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    (tiltPartialUpper s + tiltTailUpper s) +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/--
Bulk region where the tilt residual is supplied through a concrete truncation in `j`
plus a certified tail bound.
-/
def c2BulkConcreteTruncatedTiltRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteTruncatedTiltHypotheses
    tiltLayerResidual tiltCutoff coreCutoff K M
    tiltPartialUpper tiltTailUpper
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteTruncatedTilt_mem_regularized_horizontal_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkRegularizedHorizontalRegion
      (c2TiltRegularizedResidual tiltLayerResidual)
      (c2ConcreteCutoffError K M)
      (c2ConcreteOddHorizontalLayerDefect coreCutoff)
      (fun s => tiltPartialUpper s + tiltTailUpper s)
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tilt_bound := c2TiltRegularizedResidual_bound_of_partial_and_tail
      hs.tiltSummable hs.tiltNormSummable hs.tiltPartial_bound hs.tiltTail_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

/--
Concrete bulk bounds data where the tilt source is provided via a finite truncation plus
an explicit tail certificate.
-/
noncomputable def c2BulkConcreteTruncatedTiltBoundsData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
  (_tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2ConcreteOperatorBulkBoundsData
    (c2TiltRegularizedResidual tiltLayerResidual)
    coreCutoff K M
    (fun s => tiltPartialUpper s + tiltTailUpper s)
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteTruncatedTiltRouteData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
  (_tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteTruncatedTiltBoundsData
    tiltLayerResidual _tiltCutoff coreCutoff K M
    tiltPartialUpper tiltTailUpper
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteTruncatedTilt_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltPartialUpper tiltTailUpper
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2ConcreteOperatorBulk_nonvanishing_of_mem
    (c2BulkConcreteTruncatedTilt_mem_regularized_horizontal_region hs)

/--
Concrete bulk hypotheses where the tilt truncation bounds are supplied by the same geometric
layer control already used for the full regularized tilt residual.
-/
structure C2BulkConcreteGeometricTruncatedTiltHypotheses
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tiltRatio_nonneg : 0 ≤ tiltRatio s
  tiltRatio_lt_one : tiltRatio s < 1
  tiltLayer_bound : ∀ j : ℕ,
    ‖tiltLayerResidual s j‖ ≤
      (tiltConstant s / tiltScale s) * tiltRatio s ^ j
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s +
      c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/--
Bulk region where the truncated tilt split is bounded by the canonical geometric prefix/tail
estimates induced by the layer bound.
-/
def c2BulkConcreteGeometricTruncatedTiltRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteGeometricTruncatedTiltHypotheses
    tiltLayerResidual tiltCutoff coreCutoff K M
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteGeometricTruncatedTilt_mem_truncated_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      (c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff)
      (c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff)
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltSummable := summable_tiltLayerResidual_of_geometric
      hs.tiltScale_pos hs.tiltConstant_nonneg hs.tiltRatio_nonneg hs.tiltRatio_lt_one
      hs.tiltLayer_bound
    tiltNormSummable := summable_norm_tiltLayerResidual_of_geometric
      hs.tiltScale_pos hs.tiltConstant_nonneg hs.tiltRatio_nonneg hs.tiltRatio_lt_one
      hs.tiltLayer_bound
    tiltPartial_bound := c2ConcreteTiltPartialResidual_norm_le_geometric
      hs.tiltScale_pos hs.tiltLayer_bound
    tiltTail_bound := c2ConcreteTiltTailUpper_le_geometric
      hs.tiltScale_pos hs.tiltConstant_nonneg hs.tiltRatio_nonneg hs.tiltRatio_lt_one
      hs.tiltLayer_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

noncomputable def c2BulkConcreteGeometricTruncatedTiltBoundsData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkConcreteTruncatedTiltBoundsData
    tiltLayerResidual tiltCutoff coreCutoff K M
    (c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff)
    (c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff)
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteGeometricTruncatedTiltRouteData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (tiltCutoff : ℂ → ℕ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteGeometricTruncatedTiltBoundsData
    tiltLayerResidual tiltCutoff coreCutoff K M
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteGeometricTruncatedTilt_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteTruncatedTilt_nonvanishing_of_mem
    (c2BulkConcreteGeometricTruncatedTilt_mem_truncated_region hs)

/--
Core tilt residual bound.

If each tilt residual layer is bounded by `(C/X) * r^j`, with `0 ≤ r < 1`,
then the total tilt residual is bounded by `(C/X) * (1-r)⁻¹`.
-/
theorem c2TiltRegularizedResidual_bound
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale tiltRatio : ℂ → ℝ} {s : ℂ}
    (_hscale : 0 < tiltScale s)
    (_hconstant : 0 ≤ tiltConstant s)
    (hratio_nonneg : 0 ≤ tiltRatio s)
    (hratio_lt_one : tiltRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * tiltRatio s ^ j) :
    ‖c2TiltRegularizedResidual tiltLayerResidual s‖ ≤
      c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s := by
  unfold c2TiltRegularizedResidual c2TiltRegularizedUpper
  have hgeom : Summable fun j : ℕ => tiltRatio s ^ j :=
    summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
  have hmajor :
      HasSum
        (fun j : ℕ => (tiltConstant s / tiltScale s) * tiltRatio s ^ j)
        ((tiltConstant s / tiltScale s) * (1 - tiltRatio s)⁻¹) := by
    have hmul := hgeom.hasSum.mul_left (tiltConstant s / tiltScale s)
    simpa [tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one] using hmul
  exact tsum_of_norm_bounded hmajor hlayer

/--
Fully concrete bulk hypotheses now used by the route:

* tilt residual is supplied by a regularized layer estimate;
* horizontal defect is the concrete odd-core cutoff layer defect;
* cutoff error is the concrete rectangular finite operator against the analytic target.
-/
structure C2BulkConcreteRegularizedHypotheses
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tiltRatio_nonneg : 0 ≤ tiltRatio s
  tiltRatio_lt_one : tiltRatio s < 1
  tiltLayer_bound : ∀ j : ℕ,
    ‖tiltLayerResidual s j‖ ≤
      (tiltConstant s / tiltScale s) * tiltRatio s ^ j
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/-- Fully concrete bulk region with tilt, horizontal, and cutoff estimates split by source. -/
def c2BulkConcreteRegularizedRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteRegularizedHypotheses
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteRegularized_mem_regularized_horizontal_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkRegularizedHorizontalRegion
      (c2TiltRegularizedResidual tiltLayerResidual)
      (c2ConcreteCutoffError K M)
      (c2ConcreteOddHorizontalLayerDefect coreCutoff)
      (c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio)
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tilt_bound := c2TiltRegularizedResidual_bound
      hs.tiltScale_pos hs.tiltConstant_nonneg
      hs.tiltRatio_nonneg hs.tiltRatio_lt_one
      hs.tiltLayer_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

/-- Concrete bulk bounds data after also regularizing the tilt residual. -/
noncomputable def c2BulkConcreteRegularizedBoundsData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2ConcreteOperatorBulkBoundsData
    (c2TiltRegularizedResidual tiltLayerResidual)
    coreCutoff K M
    (c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio)
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteRegularizedRouteData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteRegularizedBoundsData
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteRegularized_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2ConcreteOperatorBulk_nonvanishing_of_mem
    (c2BulkConcreteRegularized_mem_regularized_horizontal_region hs)

theorem c2BulkConcreteRegularized_mem_geometric_truncated_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  refine {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tiltRatio_nonneg := hs.tiltRatio_nonneg
    tiltRatio_lt_one := hs.tiltRatio_lt_one
    tiltLayer_bound := hs.tiltLayer_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := ?_
  }
  have htilt :
      c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s +
        c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s ≤
          c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s := by
    rw [c2TiltPartialGeometricUpper_add_tail_eq_regularized
      hs.tiltRatio_nonneg hs.tiltRatio_lt_one]
  let extra :=
    c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s
  have hdom :
      (c2TiltPartialGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s +
          c2TiltTailGeometricUpper tiltConstant tiltScale tiltRatio tiltCutoff s) +
        extra ≤
      c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s +
        extra :=
    add_le_add htilt le_rfl
  exact lt_of_le_of_lt (by simpa [extra, add_assoc] using hdom) hs.dominance

theorem c2BulkConcreteRegularized_nonvanishing_of_mem_geometric_truncated
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteGeometricTruncatedTilt_nonvanishing_of_mem
    (c2BulkConcreteRegularized_mem_geometric_truncated_region
      (tiltCutoff := tiltCutoff) hs)

/-- Canonical analytic tilt ratio supplied by the C2 vertical resolvent. -/
noncomputable def c2TiltAnalyticRatio : ℂ → ℝ :=
  fun s => ‖q s‖

/-- Regularized tilt upper bound specialized to the analytic ratio `‖q s‖`. -/
noncomputable def c2TiltAnalyticRegularizedUpper
    (tiltConstant tiltScale : ℂ → ℝ) : ℂ → ℝ :=
  c2TiltRegularizedUpper tiltConstant tiltScale c2TiltAnalyticRatio

/-- Finite prefix upper bound specialized to the analytic ratio `‖q s‖`. -/
noncomputable def c2TiltAnalyticPartialGeometricUpper
    (tiltConstant tiltScale : ℂ → ℝ)
    (tiltCutoff : ℂ → ℕ) : ℂ → ℝ :=
  c2TiltPartialGeometricUpper tiltConstant tiltScale c2TiltAnalyticRatio tiltCutoff

/-- Tail upper bound specialized to the analytic ratio `‖q s‖`. -/
noncomputable def c2TiltAnalyticTailGeometricUpper
    (tiltConstant tiltScale : ℂ → ℝ)
    (tiltCutoff : ℂ → ℕ) : ℂ → ℝ :=
  c2TiltTailGeometricUpper tiltConstant tiltScale c2TiltAnalyticRatio tiltCutoff

lemma c2TiltAnalyticRatio_nonneg (s : ℂ) : 0 ≤ c2TiltAnalyticRatio s := by
  simp [c2TiltAnalyticRatio]

lemma c2TiltAnalyticRatio_lt_one_of_re_pos {s : ℂ}
    (hs : 0 < s.re) :
    c2TiltAnalyticRatio s < 1 := by
  simpa [c2TiltAnalyticRatio] using q_norm_lt_one_of_re_pos s hs

lemma c2TiltAnalyticRatio_lt_one_of_offCriticalStrip {s : ℂ}
    (hs : offCriticalStrip s) :
    c2TiltAnalyticRatio s < 1 := by
  simpa [c2TiltAnalyticRatio] using
    verticalRatio_norm_lt_one_of_offCriticalStrip s hs

theorem c2TiltRegularizedResidual_bound_of_analytic_geometric_of_re_pos
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hs : 0 < s.re)
    (hscale : 0 < tiltScale s)
    (hconstant : 0 ≤ tiltConstant s)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j) :
    ‖c2TiltRegularizedResidual tiltLayerResidual s‖ ≤
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s := by
  simpa [c2TiltAnalyticRegularizedUpper] using
    (c2TiltRegularizedResidual_bound
      (tiltLayerResidual := tiltLayerResidual)
      (tiltConstant := tiltConstant)
      (tiltScale := tiltScale)
      (tiltRatio := c2TiltAnalyticRatio)
      (s := s)
      hscale hconstant
      (c2TiltAnalyticRatio_nonneg s)
      (c2TiltAnalyticRatio_lt_one_of_re_pos hs)
      hlayer)

theorem c2TiltRegularizedResidual_bound_of_analytic_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale : 0 < tiltScale s)
    (hconstant : 0 ≤ tiltConstant s)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j) :
    ‖c2TiltRegularizedResidual tiltLayerResidual s‖ ≤
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s := by
  simpa [c2TiltAnalyticRegularizedUpper] using
    (c2TiltRegularizedResidual_bound
      (tiltLayerResidual := tiltLayerResidual)
      (tiltConstant := tiltConstant)
      (tiltScale := tiltScale)
      (tiltRatio := c2TiltAnalyticRatio)
      (s := s)
      hscale hconstant
      (c2TiltAnalyticRatio_nonneg s)
      (c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hoff)
      hlayer)

theorem c2ConcreteTiltPartialResidual_norm_le_analytic_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < tiltScale s)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j) :
    ‖c2ConcreteTiltPartialResidual tiltLayerResidual tiltCutoff s‖ ≤
      c2TiltAnalyticPartialGeometricUpper tiltConstant tiltScale tiltCutoff s := by
  simpa [c2TiltAnalyticPartialGeometricUpper] using
    (c2ConcreteTiltPartialResidual_norm_le_geometric
      (tiltLayerResidual := tiltLayerResidual)
      (tiltCutoff := tiltCutoff)
      (tiltConstant := tiltConstant)
      (tiltScale := tiltScale)
      (tiltRatio := c2TiltAnalyticRatio)
      (s := s)
      hscale hlayer)

theorem c2ConcreteTiltTailUpper_le_analytic_geometric
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hoff : offCriticalStrip s)
    (hscale : 0 < tiltScale s)
    (hconstant : 0 ≤ tiltConstant s)
    (hlayer : ∀ j : ℕ,
      ‖tiltLayerResidual s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j) :
    c2ConcreteTiltTailUpper tiltLayerResidual tiltCutoff s ≤
      c2TiltAnalyticTailGeometricUpper tiltConstant tiltScale tiltCutoff s := by
  simpa [c2TiltAnalyticTailGeometricUpper] using
    (c2ConcreteTiltTailUpper_le_geometric
      (tiltLayerResidual := tiltLayerResidual)
      (tiltCutoff := tiltCutoff)
      (tiltConstant := tiltConstant)
      (tiltScale := tiltScale)
      (tiltRatio := c2TiltAnalyticRatio)
      (s := s)
      hscale hconstant
      (c2TiltAnalyticRatio_nonneg s)
      (c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hoff)
      hlayer)

theorem c2TiltAnalyticPartialGeometricUpper_add_tail_eq_regularized
    {tiltCutoff : ℂ → ℕ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hoff : offCriticalStrip s) :
    c2TiltAnalyticPartialGeometricUpper tiltConstant tiltScale tiltCutoff s +
      c2TiltAnalyticTailGeometricUpper tiltConstant tiltScale tiltCutoff s =
        c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s := by
  simpa [c2TiltAnalyticPartialGeometricUpper, c2TiltAnalyticTailGeometricUpper,
    c2TiltAnalyticRegularizedUpper] using
    (c2TiltPartialGeometricUpper_add_tail_eq_regularized
      (tiltCutoff := tiltCutoff)
      (tiltConstant := tiltConstant)
      (tiltScale := tiltScale)
      (tiltRatio := c2TiltAnalyticRatio)
      (s := s)
      (c2TiltAnalyticRatio_nonneg s)
      (c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hoff))

/--
Concrete analytic tilt hypotheses: the layer decay is measured against the
canonical C2 ratio `‖q s‖`, so only the amplitude scale remains to be supplied.
-/
structure C2BulkConcreteAnalyticTiltHypotheses
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tiltLayer_bound : ∀ j : ℕ,
    ‖tiltLayerResidual s j‖ ≤
      (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/-- Concrete bulk region with the analytic tilt ratio fixed to `‖q s‖`. -/
def c2BulkConcreteAnalyticTiltRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteAnalyticTiltHypotheses
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteAnalyticTilt_mem_regularized_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteAnalyticTiltRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale c2TiltAnalyticRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tiltRatio_nonneg := c2TiltAnalyticRatio_nonneg s
    tiltRatio_lt_one := c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hs.offCritical
    tiltLayer_bound := hs.tiltLayer_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := by
      simpa [c2TiltAnalyticRegularizedUpper] using hs.dominance
  }

/-- Concrete bulk bounds data using the analytic tilt ratio `‖q s‖`. -/
noncomputable def c2BulkConcreteAnalyticTiltBoundsData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkConcreteRegularizedBoundsData
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale c2TiltAnalyticRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteAnalyticTiltRouteData
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteAnalyticTiltBoundsData
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteAnalyticTilt_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteAnalyticTiltRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteRegularized_nonvanishing_of_mem
    (c2BulkConcreteAnalyticTilt_mem_regularized_region hs)

theorem c2BulkConcreteAnalyticTilt_mem_geometric_truncated_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteAnalyticTiltRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      tiltLayerResidual tiltCutoff coreCutoff K M
      tiltConstant tiltScale c2TiltAnalyticRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact c2BulkConcreteRegularized_mem_geometric_truncated_region
    (tiltCutoff := tiltCutoff)
    (c2BulkConcreteAnalyticTilt_mem_regularized_region hs)

theorem c2BulkConcreteAnalyticTilt_nonvanishing_of_mem_geometric_truncated
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteAnalyticTiltRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteGeometricTruncatedTilt_nonvanishing_of_mem
    (c2BulkConcreteAnalyticTilt_mem_geometric_truncated_region
      (tiltCutoff := tiltCutoff) hs)

/-- A concrete analytic tilt-layer family obtained from one seed amplitude and the
canonical vertical ratio `q(s)^j`. -/
noncomputable def c2SeededTiltLayerResidual
    (tiltSeed : ℂ → ℂ) : ℂ → ℕ → ℂ :=
  fun s j => tiltSeed s * q s ^ j

theorem c2SeededTiltRegularized_eq_resolvent
    (tiltSeed : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s =
      tiltSeed s * (1 - q s)⁻¹ := by
  unfold c2TiltRegularizedResidual c2SeededTiltLayerResidual
  rw [tsum_mul_left]
  rw [geom_resolvent_of_re_pos s hs]
  simp [one_div]

theorem c2SeededTiltLayerResidual_bound
    {tiltSeed : ℂ → ℂ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s) :
    ∀ j : ℕ,
      ‖c2SeededTiltLayerResidual tiltSeed s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j := by
  intro j
  calc
    ‖c2SeededTiltLayerResidual tiltSeed s j‖
      = ‖tiltSeed s‖ * c2TiltAnalyticRatio s ^ j := by
          simp [c2SeededTiltLayerResidual, c2TiltAnalyticRatio, norm_pow]
    _ ≤ (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j := by
          exact mul_le_mul_of_nonneg_right hseed
            (pow_nonneg (c2TiltAnalyticRatio_nonneg s) j)

theorem c2TiltSeed_bound_from_scaled
    {tiltSeed : ℂ → ℂ} {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < tiltScale s)
    (hscaled : ‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s) :
    ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s := by
  exact (le_div_iff₀ hscale).mpr hscaled

/--
Seeded analytic tilt hypotheses: instead of giving a bound for every layer, it is
enough to bound a single seed amplitude whose descendants are propagated by `q^j`.
-/
structure C2BulkConcreteSeededAnalyticTiltHypotheses
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tiltSeed_bound : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/-- Seeded concrete bulk region using the analytic tilt ratio `‖q s‖`. -/
def c2BulkConcreteSeededAnalyticTiltRegion
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteSeededAnalyticTiltHypotheses
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteSeededAnalyticTilt_mem_region
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteAnalyticTiltRegion
      (c2SeededTiltLayerResidual tiltSeed) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tiltLayer_bound := c2SeededTiltLayerResidual_bound hs.tiltSeed_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

/-- Concrete bulk bounds data for a seeded geometric tilt family. -/
noncomputable def c2BulkConcreteSeededAnalyticTiltBoundsData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkConcreteAnalyticTiltBoundsData
    (c2SeededTiltLayerResidual tiltSeed)
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteSeededAnalyticTiltRouteData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteSeededAnalyticTiltBoundsData
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteSeededAnalyticTilt_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteAnalyticTilt_nonvanishing_of_mem
    (c2BulkConcreteSeededAnalyticTilt_mem_region hs)

theorem c2BulkConcreteSeededAnalyticTilt_mem_geometric_truncated_region
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      (c2SeededTiltLayerResidual tiltSeed) tiltCutoff coreCutoff K M
      tiltConstant tiltScale c2TiltAnalyticRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact c2BulkConcreteAnalyticTilt_mem_geometric_truncated_region
    (tiltCutoff := tiltCutoff)
    (c2BulkConcreteSeededAnalyticTilt_mem_region hs)

theorem c2BulkConcreteSeededAnalyticTilt_nonvanishing_of_mem_geometric_truncated
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteGeometricTruncatedTilt_nonvanishing_of_mem
    (c2BulkConcreteSeededAnalyticTilt_mem_geometric_truncated_region
      (tiltCutoff := tiltCutoff) hs)

/--
Scaled seeded analytic tilt hypotheses: the seed amplitude is supplied in the natural
route form `‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s`.
-/
structure C2BulkConcreteScaledSeededAnalyticTiltHypotheses
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound : ‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/-- Scaled seeded bulk region using the analytic tilt ratio `‖q s‖`. -/
def c2BulkConcreteScaledSeededAnalyticTiltRegion
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteScaledSeededAnalyticTiltHypotheses
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteScaledSeededAnalyticTilt_mem_region
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tiltSeed_bound := c2TiltSeed_bound_from_scaled hs.tiltScale_pos hs.tilt_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkConcreteScaledSeededAnalyticTilt_mem_region_of_baseSeed
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hoffCritical : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant : 0 ≤ tiltConstant s)
    (hseed :
      ‖c2ConcreteTiltPartialResidual tiltLayerResidual (fun _ => 1) s‖ *
        tiltScale s ≤ tiltConstant s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdominance :
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
        c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
        cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s) :
    s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      (c2TiltBaseSeed tiltLayerResidual) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hoffCritical
    tiltScale_pos := htiltScale
    tiltConstant_nonneg := htiltConstant
    tilt_scaled_bound :=
      c2TiltBaseSeed_scaled_bound_of_partialResidual_one hseed
    horizontalScale_pos := hhorizontalScale
    horizontalConstant_nonneg := hhorizontalConstant
    horizontalRatio_nonneg := hhorizontalRatio_nonneg
    horizontalRatio_lt_one := hhorizontalRatio_lt_one
    horizontalLayer_bound := hhorizontalLayer
    cutoffScale_pos := hcutoffScale
    cutoff_scaled_bound := hcutoff
    dominance := hdominance
  }

noncomputable def c2BulkConcreteScaledSeededAnalyticTiltBoundsData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkConcreteSeededAnalyticTiltBoundsData
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2BulkConcreteScaledSeededAnalyticTiltRouteData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2BulkConcreteScaledSeededAnalyticTiltBoundsData
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2BulkConcreteScaledSeededAnalyticTilt_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteSeededAnalyticTilt_nonvanishing_of_mem
    (c2BulkConcreteScaledSeededAnalyticTilt_mem_region hs)

theorem c2BulkConcreteScaledSeededAnalyticTilt_mem_geometric_truncated_region
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteGeometricTruncatedTiltRegion
      (c2SeededTiltLayerResidual tiltSeed) tiltCutoff coreCutoff K M
      tiltConstant tiltScale c2TiltAnalyticRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact c2BulkConcreteSeededAnalyticTilt_mem_geometric_truncated_region
    (tiltCutoff := tiltCutoff)
    (c2BulkConcreteScaledSeededAnalyticTilt_mem_region hs)

theorem c2BulkConcreteScaledSeededAnalyticTilt_nonvanishing_of_mem_geometric_truncated
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteSeededAnalyticTilt_nonvanishing_of_mem_geometric_truncated
    (tiltCutoff := tiltCutoff)
    (c2BulkConcreteScaledSeededAnalyticTilt_mem_region hs)

end C2
