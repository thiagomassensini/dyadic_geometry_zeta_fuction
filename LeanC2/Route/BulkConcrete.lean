import LeanC2.Route.BulkHorizontal
import LeanC2.Analytic.GenuineInfinite
import LeanC2.Operators.TruncatedGenuine

namespace C2

/-- Concrete cutoff layer of the horizontal odd channel at shifted depth `j`, i.e. `k = j + 2`. -/
noncomputable def c2HorizontalCutoffLayer
    (coreCutoff : ℕ → ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  (2 : ℂ) * q s ^ (j + 2) * rectangularOddCoreSum s (coreCutoff j)

/-- Reference horizontal layer with a supplied analytic odd channel. -/
noncomputable def c2HorizontalReferenceLayer
    (ZoddRef : ℂ → ℂ) (s : ℂ) (j : ℕ) : ℂ :=
  (2 : ℂ) * q s ^ (j + 2) * ZoddRef s

/--
Concrete horizontal layer defect: the truncated odd-core layer minus the reference
odd-channel layer.
-/
noncomputable def c2ConcreteHorizontalLayerDefect
    (ZoddRef : ℂ → ℂ) (coreCutoff : ℕ → ℕ) : ℂ → ℕ → ℂ :=
  fun s j =>
    c2HorizontalCutoffLayer coreCutoff s j -
      c2HorizontalReferenceLayer ZoddRef s j

theorem c2ConcreteHorizontalLayerDefect_eq_weighted_odd_error
    (ZoddRef : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) (j : ℕ) :
    c2ConcreteHorizontalLayerDefect ZoddRef coreCutoff s j =
      (2 : ℂ) * q s ^ (j + 2) *
        (rectangularOddCoreSum s (coreCutoff j) - ZoddRef s) := by
  unfold c2ConcreteHorizontalLayerDefect
    c2HorizontalCutoffLayer c2HorizontalReferenceLayer
  ring

/-- The route's concrete odd-channel horizontal layer defect. -/
noncomputable def c2ConcreteOddHorizontalLayerDefect
    (coreCutoff : ℕ → ℕ) : ℂ → ℕ → ℂ :=
  c2ConcreteHorizontalLayerDefect oddDirichletChannel coreCutoff

/-- Total concrete horizontal defect obtained from the regularized layer sum. -/
noncomputable def c2ConcreteOddHorizontalDefect
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  c2HorizontalRegularizedDefect (c2ConcreteOddHorizontalLayerDefect coreCutoff)

/-- Rectangular finite C2 genuine operator as a function of `s`. -/
noncomputable def c2RectangularGenuineOperator (K M : ℕ) : ℂ → ℂ :=
  fun s => rectangularGenuine s K M

/-- Note-style exponential finite C2 genuine operator as a function of `s`. -/
noncomputable def c2ExponentialGenuineOperator
    (K M : ℕ) (X : ℝ) : ℂ → ℂ :=
  fun s => rectangularExponentialGenuine s K M X

/-- Analytic central target already formalized for the infinite genuine route. -/
noncomputable def c2AnalyticCentralTarget : ℂ → ℂ :=
  genuineCentralDoubleSeries

/-- Cutoff error of a rectangular finite operator against a supplied analytic target. -/
noncomputable def c2ConcreteCutoffErrorFromTarget
    (targetF : ℂ → ℂ) (K M : ℕ) : ℂ → ℂ :=
  fun s => c2RectangularGenuineOperator K M s - targetF s

/-- Concrete cutoff error against the genuine central infinite target. -/
noncomputable def c2ConcreteCutoffError (K M : ℕ) : ℂ → ℂ :=
  c2ConcreteCutoffErrorFromTarget c2AnalyticCentralTarget K M

/-- Exponential cutoff error of the finite operator against a supplied target. -/
noncomputable def c2ExponentialCutoffErrorFromTarget
    (targetF : ℂ → ℂ) (K M : ℕ) (X : ℝ) : ℂ → ℂ :=
  fun s => c2ExponentialGenuineOperator K M X s - targetF s

/-- Exponential cutoff error against the genuine central infinite target. -/
noncomputable def c2ExponentialCutoffError (K M : ℕ) (X : ℝ) : ℂ → ℂ :=
  c2ExponentialCutoffErrorFromTarget c2AnalyticCentralTarget K M X

theorem c2ExponentialCutoffErrorFromTarget_eq_residual_add_concreteCutoffErrorFromTarget
    (targetF : ℂ → ℂ) (K M : ℕ) (X : ℝ) (s : ℂ) :
    c2ExponentialCutoffErrorFromTarget targetF K M X s =
      rectangularExponentialResidual s K M X +
        c2ConcreteCutoffErrorFromTarget targetF K M s := by
  unfold c2ExponentialCutoffErrorFromTarget c2ExponentialGenuineOperator
  rw [rectangularExponentialGenuine_eq_residual_add_rectangularGenuine]
  unfold c2ConcreteCutoffErrorFromTarget c2RectangularGenuineOperator
  ring

theorem c2ExponentialCutoffError_eq_residual_add_concreteCutoffError
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    c2ExponentialCutoffError K M X s =
      rectangularExponentialResidual s K M X + c2ConcreteCutoffError K M s := by
  simpa [c2ExponentialCutoffError, c2ConcreteCutoffError, c2AnalyticCentralTarget] using
    c2ExponentialCutoffErrorFromTarget_eq_residual_add_concreteCutoffErrorFromTarget
      c2AnalyticCentralTarget K M X s

theorem c2ConcreteCutoffErrorFromTarget_norm_le_exponentialFromTarget_add_pointwiseOscillatoryExpUpper
    (targetF : ℂ → ℂ) (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ConcreteCutoffErrorFromTarget targetF K M s‖ ≤
      ‖c2ExponentialCutoffErrorFromTarget targetF K M X s‖ +
        rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
  have hexact :
      c2ConcreteCutoffErrorFromTarget targetF K M s =
        c2ExponentialCutoffErrorFromTarget targetF K M X s -
          rectangularExponentialResidual s K M X := by
    rw [c2ExponentialCutoffErrorFromTarget_eq_residual_add_concreteCutoffErrorFromTarget
      targetF K M X s]
    ring
  rw [hexact]
  calc
    ‖c2ExponentialCutoffErrorFromTarget targetF K M X s -
        rectangularExponentialResidual s K M X‖ ≤
      ‖c2ExponentialCutoffErrorFromTarget targetF K M X s‖ +
        ‖rectangularExponentialResidual s K M X‖ := by
          exact norm_sub_le _ _
    _ ≤ ‖c2ExponentialCutoffErrorFromTarget targetF K M X s‖ +
        rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
          exact add_le_add le_rfl
            (rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper
              s K M J X hJ)

/-- Immediate exact-upper witness for the exponential cutoff error against the
infinite target: oscillatory finite residual plus the existing sharp cutoff
error. -/
noncomputable def c2ExponentialCutoffErrorPointwiseOscillatoryExactUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  fun s =>
    rectangularExponentialPointwiseOscillatoryExactUpper s K M J X +
      ‖c2ConcreteCutoffError K M s‖

/-- Explicit pointwise oscillatory witness for the exponential cutoff error
against the infinite target. -/
noncomputable def c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  fun s =>
    rectangularExponentialPointwiseOscillatoryExpUpper s K M J X +
      ‖c2ConcreteCutoffError K M s‖

/-- Default pointwise oscillatory witness for the exponential cutoff error. -/
noncomputable abbrev c2ExponentialCutoffErrorPointwiseOscillatoryUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper K M J X

theorem c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExactUpper
    (K M J : ℕ) (X : ℝ) (s : ℂ) :
    ‖c2ExponentialCutoffError K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryExactUpper K M J X s := by
  rw [c2ExponentialCutoffError_eq_residual_add_concreteCutoffError]
  calc
    ‖rectangularExponentialResidual s K M X + c2ConcreteCutoffError K M s‖ ≤
      ‖rectangularExponentialResidual s K M X‖ + ‖c2ConcreteCutoffError K M s‖ := by
        exact norm_add_le _ _
    _ ≤ rectangularExponentialPointwiseOscillatoryExactUpper s K M J X +
          ‖c2ConcreteCutoffError K M s‖ := by
        exact add_le_add
          (rectangularExponentialResidual_norm_le_pointwiseOscillatoryExactUpper s K M J X)
          le_rfl
    _ = c2ExponentialCutoffErrorPointwiseOscillatoryExactUpper K M J X s := by
        rfl

theorem c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExpUpper
    (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ExponentialCutoffError K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper K M J X s := by
  rw [c2ExponentialCutoffError_eq_residual_add_concreteCutoffError]
  calc
    ‖rectangularExponentialResidual s K M X + c2ConcreteCutoffError K M s‖ ≤
      ‖rectangularExponentialResidual s K M X‖ + ‖c2ConcreteCutoffError K M s‖ := by
        exact norm_add_le _ _
    _ ≤ rectangularExponentialPointwiseOscillatoryExpUpper s K M J X +
          ‖c2ConcreteCutoffError K M s‖ := by
        exact add_le_add
          (rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper s K M J X hJ)
          le_rfl
    _ = c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper K M J X s := by
        rfl

theorem c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExpUpper_24
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    ‖c2ExponentialCutoffError K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper K M 24 X s := by
  exact c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExpUpper
    K M 24 X s (by decide)

theorem c2ExponentialCutoffError_norm_le_pointwiseOscillatoryUpper
    (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ExponentialCutoffError K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s := by
  exact c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExpUpper
    K M J X s hJ

theorem c2ExponentialCutoffError_norm_le_pointwiseOscillatoryUpper_24
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    ‖c2ExponentialCutoffError K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M 24 X s := by
  exact c2ExponentialCutoffError_norm_le_pointwiseOscillatoryExpUpper_24
    K M X s

/-- The same rectangular cutoff error, rewritten against the `c0 * ζ` target. -/
noncomputable def c2ConcreteCutoffErrorC0Zeta (K M : ℕ) : ℂ → ℂ :=
  c2ConcreteCutoffErrorFromTarget (fun s => c0 s * riemannZeta s) K M

theorem c2ConcreteCutoffError_eq_c0Zeta_of_one_lt_re
    (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    c2ConcreteCutoffError K M s = c2ConcreteCutoffErrorC0Zeta K M s := by
  unfold c2ConcreteCutoffError c2ConcreteCutoffErrorC0Zeta
    c2ConcreteCutoffErrorFromTarget c2AnalyticCentralTarget
  rw [genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs]

/--
Bulk data with the horizontal and cutoff errors tied to the concrete finite/infinite
C2 operators already present in the project.
-/
noncomputable def c2ConcreteOperatorBulkBoundsData
    (tiltResidual : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkRegularizedHorizontalBoundsData
    tiltResidual
    (c2ConcreteCutoffError K M)
    (c2ConcreteOddHorizontalLayerDefect coreCutoff)
    tiltUpper horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2ConcreteOperatorBulkRouteData
    (tiltResidual : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2ConcreteOperatorBulkBoundsData
    tiltResidual coreCutoff K M
    tiltUpper horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale).toRouteData

theorem c2ConcreteOperatorBulk_nonvanishing_of_mem
    {tiltResidual : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkRegularizedHorizontalRegion
      tiltResidual
      (c2ConcreteCutoffError K M)
      (c2ConcreteOddHorizontalLayerDefect coreCutoff)
      tiltUpper horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta tiltResidual
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkRegularizedHorizontal_nonvanishing_of_mem hs

end C2
