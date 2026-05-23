import LeanC2.Route.BulkTilt

namespace C2

/-- Odd-channel truncation error at the horizontal cutoff attached to layer `j`. -/
noncomputable def c2OddTruncationError
    (ZoddRef : ℂ → ℂ) (coreCutoff : ℕ → ℕ) : ℂ → ℕ → ℂ :=
  fun s j => rectangularOddCoreSum s (coreCutoff j) - ZoddRef s

/-- Route specialization of the odd-channel truncation error. -/
noncomputable def c2ConcreteOddTruncationError
    (coreCutoff : ℕ → ℕ) : ℂ → ℕ → ℂ :=
  c2OddTruncationError oddDirichletChannel coreCutoff

theorem c2ConcreteHorizontalLayerDefect_eq_weighted_truncation_error
    (ZoddRef : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) (j : ℕ) :
    c2ConcreteHorizontalLayerDefect ZoddRef coreCutoff s j =
      (2 : ℂ) * q s ^ (j + 2) *
        c2OddTruncationError ZoddRef coreCutoff s j := by
  rw [c2ConcreteHorizontalLayerDefect_eq_weighted_odd_error]
  rfl

theorem c2ConcreteHorizontalLayerDefect_norm_eq
    (ZoddRef : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) (j : ℕ) :
    ‖c2ConcreteHorizontalLayerDefect ZoddRef coreCutoff s j‖ =
      2 * ‖q s‖ ^ (j + 2) *
        ‖c2OddTruncationError ZoddRef coreCutoff s j‖ := by
  rw [c2ConcreteHorizontalLayerDefect_eq_weighted_truncation_error]
  simp [norm_pow, c2OddTruncationError]

theorem c2ConcreteOddHorizontalLayerDefect_norm_eq
    (coreCutoff : ℕ → ℕ) (s : ℂ) (j : ℕ) :
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ =
      2 * ‖q s‖ ^ (j + 2) *
        ‖c2ConcreteOddTruncationError coreCutoff s j‖ := by
  exact c2ConcreteHorizontalLayerDefect_norm_eq oddDirichletChannel coreCutoff s j

theorem c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
    {coreCutoff : ℕ → ℕ} {oddTruncationUpper : ℂ → ℕ → ℝ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hodd : ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j)
    (hbudget : ∀ j : ℕ,
      2 * ‖q s‖ ^ (j + 2) * oddTruncationUpper s j ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j := by
  intro j
  rw [c2ConcreteOddHorizontalLayerDefect_norm_eq]
  have hfactor_nonneg : 0 ≤ 2 * ‖q s‖ ^ (j + 2) := by positivity
  exact le_trans
    (mul_le_mul_of_nonneg_left (hodd j) hfactor_nonneg)
    (hbudget j)

theorem c2ConcreteCutoff_scaled_bound_of_c0Zeta
    {K M : ℕ} {cutoffScale cutoffConstant : ℂ → ℝ} {s : ℂ}
    (hs : 1 < s.re)
    (hscaled :
      ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  rw [c2ConcreteCutoffError_eq_c0Zeta_of_one_lt_re K M hs]
  exact hscaled

/--
Scalar estimates for the fully concrete bulk, with the horizontal estimate reduced
to the odd-channel truncation error before the C2 layer weight is applied.
-/
structure C2BulkConcreteScalarEstimates
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
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
  oddTruncation_bound : ∀ j : ℕ,
    ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddTruncationUpper s j ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/-- Region carrying the scalar estimates after reducing the horizontal layer to odd truncation. -/
def c2BulkConcreteScalarEstimateRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkConcreteScalarEstimates
    tiltLayerResidual coreCutoff K M oddTruncationUpper
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkConcreteScalarEstimates_to_regularized
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScalarEstimateRegion
      tiltLayerResidual coreCutoff K M oddTruncationUpper
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteRegularizedRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
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
    horizontalLayer_bound :=
      c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
        hs.oddTruncation_bound hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkConcreteScalarEstimates_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkConcreteScalarEstimateRegion
      tiltLayerResidual coreCutoff K M oddTruncationUpper
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteRegularized_nonvanishing_of_mem
    (c2BulkConcreteScalarEstimates_to_regularized hs)

end C2
