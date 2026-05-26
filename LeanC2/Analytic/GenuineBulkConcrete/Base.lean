import LeanC2.Analytic.GenuineBulk
import LeanC2.Analytic.GenuineContinuation
import LeanC2.Analytic.GenuineG11
import LeanC2.Route.BulkOddTail
import LeanC2.Route.BulkQuartet

namespace C2

/-!
Adapters from the concrete C2 bulk packages to the `genuineFInfinite`-pinned bulk
interface.

The remaining analytic obligation is isolated as a regional model identity: on the
chosen bulk region, the concrete quantitative bulk model must equal the complete
infinite genuine operator.
-/

/-- Concrete bulk model attached to the scaled seeded tilt and odd-tail cutoff data. -/
noncomputable def c2ScaledSeededExplicitOddTailBulkModel
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  c2AnalyticBulkF
    (c2BulkGdelta
      (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
      (c2ConcreteOddHorizontalDefect coreCutoff))
    (c2BulkEdelta (c2ConcreteCutoffError K M))

/-- Pointwise residual of the concrete bulk model against the complete genuine operator. -/
noncomputable def c2ScaledSeededExplicitOddTailBulkModelResidual
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s => c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s -
    genuineFInfinite s

/-- Note-aligned finite model `F_X` from `notas/teorema_resolvent_non_cancellation.md`. -/
noncomputable abbrev c2ConcreteResolventNonCancellationFiniteModel := c2ScaledSeededExplicitOddTailBulkModel

/-- Note-aligned cutoff residual `F_X - F_∞`. -/
noncomputable abbrev c2ConcreteResolventNonCancellationResidual :=
  c2ScaledSeededExplicitOddTailBulkModelResidual

/-- Note-aligned quartet `Q_{4,X}`: the extracted four-floor vertical prefix. -/
noncomputable def c2ConcreteResolventNonCancellationQuartet : ℂ → ℂ :=
  fun s => c2QuartetBulkK2 s * verticalQuartetPrefix (q s)

/--
Note-aligned tail `T_{4,X}`: the vertical debt plus the regularized and cutoff
corrections left after extracting `Q_{4,X}`.
-/
noncomputable def c2ConcreteResolventNonCancellationTail
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    c2QuartetBulkGdelta
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff)) s +
      c2BulkEdelta (c2ConcreteCutoffError K M) s

theorem c2ConcreteResolventNonCancellationTail_eq_expanded
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationTail tiltSeed coreCutoff K M s =
      c2QuartetVerticalTail s +
        c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
        c2ConcreteCutoffError K M s := by
  unfold c2ConcreteResolventNonCancellationTail c2QuartetBulkGdelta c2BulkGdelta c2BulkEdelta
  ring

theorem c2ConcreteResolventNonCancellationFiniteModel_eq_quartet_add_tail_of_re_pos
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s =
      c2ConcreteResolventNonCancellationQuartet s +
        c2ConcreteResolventNonCancellationTail tiltSeed coreCutoff K M s := by
  calc
    c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s =
        c2QuartetBulkKdelta
            (c2BulkGdelta
              (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
              (c2ConcreteOddHorizontalDefect coreCutoff)) s +
          c2BulkEdelta (c2ConcreteCutoffError K M) s := by
      simpa [c2ConcreteResolventNonCancellationFiniteModel, c2ScaledSeededExplicitOddTailBulkModel] using
        (c2QuartetAnalyticBulk_decomposition
          (c2BulkGdelta
            (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
            (c2ConcreteOddHorizontalDefect coreCutoff))
          (c2BulkEdelta (c2ConcreteCutoffError K M)) hs)
    _ = c2ConcreteResolventNonCancellationQuartet s +
          c2ConcreteResolventNonCancellationTail tiltSeed coreCutoff K M s := by
      unfold c2ConcreteResolventNonCancellationQuartet c2ConcreteResolventNonCancellationTail
        c2QuartetBulkKdelta c2QuartetBulkGdelta c2BulkGdelta c2BulkEdelta
      ring

/--
Concrete layer `F_{2+j,X}` for the current seeded bulk package: exact vertical
quartet floor, seeded tilt layer, and horizontal layer defect.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedLayer
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (j : ℕ) : ℂ → ℂ :=
  fun s =>
    c2QuartetBulkK2 s * q s ^ j +
      c2SeededTiltLayerResidual tiltSeed s j +
      c2ConcreteOddHorizontalLayerDefect coreCutoff s j

/-- Adjusted amplitude `A(s)` carried by the exact vertical plus seeded tilt part. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedAmplitude
    (tiltSeed : ℂ → ℂ) : ℂ → ℂ :=
  fun s => c2QuartetBulkK2 s + tiltSeed s

/-- Adjusted ratio `β(s)` for the current seeded bulk package. -/
noncomputable abbrev c2ConcreteResolventNonCancellationAdjustedRatio : ℂ → ℂ := q

/-- First horizontal error term `E₀(s)` in the adjusted quartet. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedError0
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => c2ConcreteOddHorizontalLayerDefect coreCutoff s 0

/-- Second horizontal error term `E₁(s)` in the adjusted quartet. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedError1
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => c2ConcreteOddHorizontalLayerDefect coreCutoff s 1

/-- Third horizontal error term `E₂(s)` in the adjusted quartet. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedError2
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => c2ConcreteOddHorizontalLayerDefect coreCutoff s 2

/-- Fourth horizontal error term `E₃(s)` in the adjusted quartet. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedError3
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => c2ConcreteOddHorizontalLayerDefect coreCutoff s 3

/-- Concrete quartet `Q_{4,X}` in the adjusted note language. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedQuartet
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => ∑ j ∈ Finset.range 4, c2ConcreteResolventNonCancellationAdjustedLayer tiltSeed coreCutoff j s

/-- Horizontal quartet contribution `Σ_{j=0}^3 Eⱼ(s)`. -/
noncomputable def c2ConcreteResolventNonCancellationHorizontalQuartet
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => ∑ j ∈ Finset.range 4, c2ConcreteOddHorizontalLayerDefect coreCutoff s j

/-- Horizontal tail past the quartet levels `j = 0,1,2,3`. -/
noncomputable def c2ConcreteResolventNonCancellationHorizontalTail
    (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s => ∑' j : ℕ, c2ConcreteOddHorizontalLayerDefect coreCutoff s (j + 4)

/-- Geometric upper bound for the horizontal tail `j ≥ 4`. -/
noncomputable def c2ConcreteResolventNonCancellationHorizontalTailUpper
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  c2HorizontalTailGeometricUpper horizontalConstant horizontalScale horizontalRatio (fun _ => 4)

/--
Tail left after removing the concrete adjusted quartet from the current finite
bulk model. This tail still contains the global cutoff contribution.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedTail
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s -
      c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s

/-- Main adjusted lower term `|A(s)| |P₄(β(s))|` for the current seeded package. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedMain
    (tiltSeed : ℂ → ℂ) : ℂ → ℝ :=
  fun s =>
    ‖c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s *
      verticalQuartetPrefix (c2ConcreteResolventNonCancellationAdjustedRatio s)‖

/-- Error sum `Σ |Eⱼ(s)|` for the current seeded package. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedDefect
    (coreCutoff : ℕ → ℕ) : ℂ → ℝ :=
  fun s =>
    ‖c2ConcreteResolventNonCancellationAdjustedError0 coreCutoff s‖ +
      ‖c2ConcreteResolventNonCancellationAdjustedError1 coreCutoff s‖ +
      ‖c2ConcreteResolventNonCancellationAdjustedError2 coreCutoff s‖ +
      ‖c2ConcreteResolventNonCancellationAdjustedError3 coreCutoff s‖

theorem c2ConcreteResolventNonCancellationAdjustedLayer_eq_amplitude_ratio_add_error
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (j : ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationAdjustedLayer tiltSeed coreCutoff j s =
      c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s *
          c2ConcreteResolventNonCancellationAdjustedRatio s ^ j +
        c2ConcreteOddHorizontalLayerDefect coreCutoff s j := by
  unfold c2ConcreteResolventNonCancellationAdjustedLayer c2ConcreteResolventNonCancellationAdjustedAmplitude
    c2ConcreteResolventNonCancellationAdjustedRatio c2SeededTiltLayerResidual c2QuartetBulkK2
  ring

theorem c2ConcreteResolventNonCancellationAdjustedQuartet_eq_errorSplit
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s =
      (c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s +
        c2ConcreteResolventNonCancellationAdjustedError0 coreCutoff s) +
      (c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s *
          c2ConcreteResolventNonCancellationAdjustedRatio s +
        c2ConcreteResolventNonCancellationAdjustedError1 coreCutoff s) +
      (c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s *
          c2ConcreteResolventNonCancellationAdjustedRatio s ^ 2 +
        c2ConcreteResolventNonCancellationAdjustedError2 coreCutoff s) +
      (c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s *
          c2ConcreteResolventNonCancellationAdjustedRatio s ^ 3 +
        c2ConcreteResolventNonCancellationAdjustedError3 coreCutoff s) := by
  unfold c2ConcreteResolventNonCancellationAdjustedQuartet c2ConcreteResolventNonCancellationAdjustedLayer
    c2ConcreteResolventNonCancellationAdjustedAmplitude c2ConcreteResolventNonCancellationAdjustedRatio
    c2ConcreteResolventNonCancellationAdjustedError0 c2ConcreteResolventNonCancellationAdjustedError1
    c2ConcreteResolventNonCancellationAdjustedError2 c2ConcreteResolventNonCancellationAdjustedError3
    c2SeededTiltLayerResidual c2QuartetBulkK2
  simp [Finset.sum_range_succ]
  ring

theorem c2ConcreteResolventNonCancellationAdjustedQuartet_eq_quartet_add_tiltPrefix_add_horizontalQuartet
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s =
      c2ConcreteResolventNonCancellationQuartet s +
        c2ConcreteTiltPartialResidual (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
        c2ConcreteResolventNonCancellationHorizontalQuartet coreCutoff s := by
  unfold c2ConcreteResolventNonCancellationAdjustedQuartet c2ConcreteResolventNonCancellationAdjustedLayer
    c2ConcreteResolventNonCancellationQuartet c2ConcreteTiltPartialResidual c2TiltPartialSum
    c2ConcreteResolventNonCancellationHorizontalQuartet c2QuartetBulkK2 c2SeededTiltLayerResidual
    verticalQuartetPrefix
  simp [Finset.sum_range_succ]
  ring

theorem c2ConcreteOddHorizontalDefect_eq_quartet_add_tail
    (coreCutoff : ℕ → ℕ) {s : ℂ}
    (hsum : Summable fun j : ℕ => c2ConcreteOddHorizontalLayerDefect coreCutoff s j) :
    c2ConcreteOddHorizontalDefect coreCutoff s =
      c2ConcreteResolventNonCancellationHorizontalQuartet coreCutoff s +
        c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s := by
  unfold c2ConcreteOddHorizontalDefect c2HorizontalRegularizedDefect
    c2ConcreteResolventNonCancellationHorizontalQuartet c2ConcreteResolventNonCancellationHorizontalTail
  simpa using (hsum.sum_add_tsum_nat_add 4).symm

theorem summable_c2SeededTiltLayerResidual_of_re_pos
    (tiltSeed : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    Summable fun j : ℕ => c2SeededTiltLayerResidual tiltSeed s j := by
  refine summable_tiltLayerResidual_of_geometric
    (s := s)
    (tiltConstant := fun _ => ‖tiltSeed s‖)
    (tiltScale := fun _ => 1)
    (tiltRatio := c2TiltAnalyticRatio)
    zero_lt_one (norm_nonneg _) (c2TiltAnalyticRatio_nonneg s)
    (c2TiltAnalyticRatio_lt_one_of_re_pos hs) ?_
  have hseed : ‖tiltSeed s‖ ≤ (fun _ => ‖tiltSeed s‖) s / (fun _ => (1 : ℝ)) s := by
    simp
  exact c2SeededTiltLayerResidual_bound
    (tiltConstant := fun _ => ‖tiltSeed s‖)
    (tiltScale := fun _ => 1)
    (s := s)
    hseed

theorem c2ConcreteResolventNonCancellationFiniteModel_eq_adjustedQuartet_add_tail
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s =
      c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s +
        c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s := by
  unfold c2ConcreteResolventNonCancellationAdjustedTail
  ring

theorem c2ConcreteResolventNonCancellationAdjustedTail_eq_expanded_of_re_pos
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ}
    (hs : 0 < s.re)
    (hhorizontal : Summable fun j : ℕ => c2ConcreteOddHorizontalLayerDefect coreCutoff s j) :
    c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s =
      c2QuartetVerticalTail s +
        c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
        c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
        c2ConcreteCutoffError K M s := by
  have htilt :
      c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s =
        c2ConcreteTiltPartialResidual (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
          c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s := by
    exact c2TiltRegularizedResidual_eq_concrete_partial_add_tail
      (tiltLayerResidual := c2SeededTiltLayerResidual tiltSeed)
      (tiltCutoff := fun _ => 4)
      (s := s)
  have hhorizontal_split :
      c2ConcreteOddHorizontalDefect coreCutoff s =
        c2ConcreteResolventNonCancellationHorizontalQuartet coreCutoff s +
          c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s := by
    exact c2ConcreteOddHorizontalDefect_eq_quartet_add_tail coreCutoff hhorizontal
  calc
    c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s =
        c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s -
          c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s := by
      rfl
    _ = (verticalDepthTailFromTwo s +
          c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
          c2ConcreteOddHorizontalDefect coreCutoff s +
          c2ConcreteCutoffError K M s) -
          c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s := by
      unfold c2ConcreteResolventNonCancellationFiniteModel c2ScaledSeededExplicitOddTailBulkModel
        c2AnalyticBulkF c2BulkGdelta c2BulkEdelta
      ring
    _ = (c2ConcreteResolventNonCancellationQuartet s + c2QuartetVerticalTail s) +
          (c2ConcreteTiltPartialResidual (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
            c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s) +
          (c2ConcreteResolventNonCancellationHorizontalQuartet coreCutoff s +
            c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s) +
          c2ConcreteCutoffError K M s -
          c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s := by
      rw [verticalDepthTailFromTwo_eq_quartet_add_tail s hs, htilt, hhorizontal_split]
      simp [c2ConcreteResolventNonCancellationQuartet, c2QuartetBulkK2, c2QuartetVerticalTail]
    _ = c2QuartetVerticalTail s +
          c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
          c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
          c2ConcreteCutoffError K M s := by
      rw [c2ConcreteResolventNonCancellationAdjustedQuartet_eq_quartet_add_tiltPrefix_add_horizontalQuartet]
      ring

/-- The concrete bulk model expanded into the four route-level analytic pieces. -/
theorem c2ScaledSeededExplicitOddTailBulkModel_eq_expanded
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s =
      verticalDepthTailFromTwo s +
        c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
        c2ConcreteCutoffError K M s := by
  unfold c2ScaledSeededExplicitOddTailBulkModel c2AnalyticBulkF c2BulkGdelta
    c2BulkEdelta
  ring

/-- The residual expanded before rewriting the cutoff target. -/
theorem c2ScaledSeededExplicitOddTailBulkModelResidual_eq_expanded
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ScaledSeededExplicitOddTailBulkModelResidual tiltSeed coreCutoff K M s =
      verticalDepthTailFromTwo s +
        c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
        c2ConcreteCutoffError K M s -
        genuineFInfinite s := by
  unfold c2ScaledSeededExplicitOddTailBulkModelResidual
  rw [c2ScaledSeededExplicitOddTailBulkModel_eq_expanded]

/--
The residual after using the already-formalized infinite lateral cancellation on
`Re(s) > 1`. This is the exact algebraic obstruction left by the concrete model.
-/
noncomputable def c2ScaledSeededExplicitOddTailRectangularCentralResidual
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    verticalDepthTailFromTwo s +
      c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
      c2ConcreteOddHorizontalDefect coreCutoff s +
      rectangularGenuine s K M -
      (2 : ℂ) * genuineCentralDoubleSeries s

/-- Residual coming from the vertical resolvent and the rectangular truncation only. -/
noncomputable def c2ScaledSeededExplicitOddTailVerticalRectangularResidual
    (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    verticalDepthTailFromTwo s +
      rectangularGenuine s K M -
      (2 : ℂ) * genuineCentralDoubleSeries s

/-- Residual coming from the two regularized correction channels: tilt and horizontal. -/
noncomputable def c2ScaledSeededExplicitOddTailRegularizedResidual
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) : ℂ → ℂ :=
  fun s =>
    c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
      c2ConcreteOddHorizontalDefect coreCutoff s

theorem c2ScaledSeededExplicitOddTailRectangularCentralResidual_eq_split
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ScaledSeededExplicitOddTailRectangularCentralResidual tiltSeed coreCutoff K M s =
      c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s +
        c2ScaledSeededExplicitOddTailRegularizedResidual tiltSeed coreCutoff s := by
  unfold c2ScaledSeededExplicitOddTailRectangularCentralResidual
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual
    c2ScaledSeededExplicitOddTailRegularizedResidual
  ring

theorem c2ScaledSeededExplicitOddTailBulkModelResidual_eq_rectangularCentralResidual_of_one_lt_re
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    c2ScaledSeededExplicitOddTailBulkModelResidual tiltSeed coreCutoff K M s =
      c2ScaledSeededExplicitOddTailRectangularCentralResidual tiltSeed coreCutoff K M s := by
  unfold c2ScaledSeededExplicitOddTailBulkModelResidual
    c2ScaledSeededExplicitOddTailRectangularCentralResidual
    c2ScaledSeededExplicitOddTailBulkModel c2AnalyticBulkF c2BulkGdelta
    c2BulkEdelta c2ConcreteCutoffError c2ConcreteCutoffErrorFromTarget
    c2AnalyticCentralTarget c2RectangularGenuineOperator
  rw [genuineFInfinite_eq_central_of_one_lt_re s hs]
  ring

/--
Regional identity still needed to pin the concrete quantitative bulk model to the
complete infinite genuine operator.
-/
def C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Prop :=
  ∀ s : ℂ,
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale →
    genuineFInfinite s =
      c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s

/--
The same regional identity, expressed as vanishing of the concrete model residual.
-/
theorem c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_residual_zero
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale ↔
      ∀ s : ℂ,
        s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
          tiltSeed coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale →
        c2ScaledSeededExplicitOddTailBulkModelResidual tiltSeed coreCutoff K M s = 0 := by
  constructor
  · intro h s hs
    unfold c2ScaledSeededExplicitOddTailBulkModelResidual
    rw [h s hs]
    ring
  · intro h s hs
    have hres := h s hs
    unfold c2ScaledSeededExplicitOddTailBulkModelResidual at hres
    calc
      genuineFInfinite s =
          c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s -
            (c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s -
              genuineFInfinite s) := by
        ring
      _ = c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s - 0 := by
        rw [hres]
      _ = c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s := by
        ring

/--
Route-facing residual-zero obligation after the complete infinite genuine operator
has been rewritten to the central infinite series.
-/
def C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Prop :=
  ∀ s : ℂ,
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale →
    c2ScaledSeededExplicitOddTailRectangularCentralResidual tiltSeed coreCutoff K M s = 0

/--
Equivalent balance form: the regularized tilt/horizontal correction cancels the
vertical-rectangular deficit.
-/
def C2ScaledSeededExplicitOddTailResidualBalance
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Prop :=
  ∀ s : ℂ,
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale →
    c2ScaledSeededExplicitOddTailRegularizedResidual tiltSeed coreCutoff s =
      -c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s

theorem c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_of_residualBalance
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hbalance : C2ScaledSeededExplicitOddTailResidualBalance
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  intro s hs
  rw [c2ScaledSeededExplicitOddTailRectangularCentralResidual_eq_split]
  rw [hbalance s hs]
  ring

theorem c2ScaledSeededExplicitOddTailResidualBalance_of_rectangularCentralResidualZero
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hzero : C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ScaledSeededExplicitOddTailResidualBalance
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  intro s hs
  have hzero' := hzero s hs
  rw [c2ScaledSeededExplicitOddTailRectangularCentralResidual_eq_split] at hzero'
  calc
    c2ScaledSeededExplicitOddTailRegularizedResidual tiltSeed coreCutoff s =
        (c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s +
          c2ScaledSeededExplicitOddTailRegularizedResidual tiltSeed coreCutoff s) -
          c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s := by
      ring
    _ = 0 - c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s := by
      rw [hzero']
    _ = -c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s := by
      ring

theorem c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_iff_residualBalance
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale ↔
    C2ScaledSeededExplicitOddTailResidualBalance
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  constructor
  · exact
      c2ScaledSeededExplicitOddTailResidualBalance_of_rectangularCentralResidualZero
  · exact
      c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_of_residualBalance

/--
Exact seed that makes the seeded tilt resolvent cancel the remaining
vertical/rectangular plus horizontal defect.
-/
noncomputable def c2OddTailBalancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    (-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s -
      c2ConcreteOddHorizontalDefect coreCutoff s) *
      (1 - q s)

theorem c2OddTailBalancingSeed_norm_le
    (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      (‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
        ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
        ‖1 - q s‖ := by
  have hsum :
      ‖-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        ‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ := by
    simpa [sub_eq_add_neg] using
      norm_add_le
        (-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s)
        (-c2ConcreteOddHorizontalDefect coreCutoff s)
  unfold c2OddTailBalancingSeed
  calc
    ‖(-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s) *
        (1 - q s)‖ =
        ‖-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s‖ * ‖1 - q s‖ := by
      rw [norm_mul]
    _ ≤
        (‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
          ‖1 - q s‖ := by
      exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

def C2OddTailBalancingSeedScaledBound
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale : ℂ → ℝ) (s : ℂ) : Prop :=
  ((‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
      ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
      ‖1 - q s‖) *
    tiltScale s ≤ tiltConstant s

theorem c2OddTailBalancingSeed_scaled_bound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hscale_nonneg : 0 ≤ tiltScale s)
    (hbound : C2OddTailBalancingSeedScaledBound
      coreCutoff K M tiltConstant tiltScale s) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ * tiltScale s ≤
      tiltConstant s := by
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (c2OddTailBalancingSeed_norm_le coreCutoff K M s)
      hscale_nonneg)
    hbound

theorem c2OddTailRegularizedResidual_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ScaledSeededExplicitOddTailRegularizedResidual
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff s =
      -c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s := by
  have hden : 1 - q s ≠ 0 := by
    simpa [q] using verticalResolvent_den_ne_zero_of_re_pos s hs
  unfold c2ScaledSeededExplicitOddTailRegularizedResidual
  rw [c2SeededTiltRegularized_eq_resolvent _ hs]
  unfold c2OddTailBalancingSeed
  rw [mul_assoc, mul_inv_cancel₀ hden]
  ring

theorem c2OddTailResidualBalance_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailResidualBalance
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  intro s hs
  exact c2OddTailRegularizedResidual_balancingSeed coreCutoff K M
    (lt_trans zero_lt_one hs.one_lt_re)

theorem c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_of_rectangularCentralResidualZero
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hzero : C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  rw [c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_residual_zero]
  intro s hs
  rw [c2ScaledSeededExplicitOddTailBulkModelResidual_eq_rectangularCentralResidual_of_one_lt_re
    tiltSeed coreCutoff K M hs.one_lt_re]
  exact hzero s hs

theorem c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_of_C0ZetaCutoffGenuineIdentity
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmodel : C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  intro s hs
  rw [← c2ScaledSeededExplicitOddTailBulkModelResidual_eq_rectangularCentralResidual_of_one_lt_re
    tiltSeed coreCutoff K M hs.one_lt_re]
  exact
    (c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_residual_zero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale).mp hmodel s hs

theorem c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_rectangularCentralResidualZero
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale ↔
    C2ScaledSeededExplicitOddTailRectangularCentralResidualZero
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  constructor
  · exact
      c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_of_C0ZetaCutoffGenuineIdentity
  · exact
      c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_of_rectangularCentralResidualZero

theorem c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_residualBalance
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale ↔
    C2ScaledSeededExplicitOddTailResidualBalance
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  rw [c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_rectangularCentralResidualZero,
    c2ScaledSeededExplicitOddTailRectangularCentralResidualZero_iff_residualBalance]

theorem c2OddTailGenuineIdentity_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  rw [c2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity_iff_residualBalance]
  exact c2OddTailResidualBalance_balancingSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

theorem c2OddTailGenuineIdentity_balancingSeed_at_of_one_lt_re
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    genuineFInfinite s =
      c2ScaledSeededExplicitOddTailBulkModel
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s := by
  have hbalance :
      c2ScaledSeededExplicitOddTailRegularizedResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff s =
        -c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s :=
    c2OddTailRegularizedResidual_balancingSeed coreCutoff K M
      (lt_trans zero_lt_one hs)
  have hrect :
      c2ScaledSeededExplicitOddTailRectangularCentralResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s = 0 := by
    rw [c2ScaledSeededExplicitOddTailRectangularCentralResidual_eq_split]
    rw [hbalance]
    ring
  have hres :
      c2ScaledSeededExplicitOddTailBulkModelResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s = 0 := by
    rw [c2ScaledSeededExplicitOddTailBulkModelResidual_eq_rectangularCentralResidual_of_one_lt_re
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M hs]
    exact hrect
  unfold c2ScaledSeededExplicitOddTailBulkModelResidual at hres
  calc
    genuineFInfinite s =
        c2ScaledSeededExplicitOddTailBulkModel
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s -
          (c2ScaledSeededExplicitOddTailBulkModel
            (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s -
            genuineFInfinite s) := by
              ring
    _ = c2ScaledSeededExplicitOddTailBulkModel
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s - 0 := by
            rw [hres]
    _ = c2ScaledSeededExplicitOddTailBulkModel
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s := by
            ring

theorem c2OddTailBalancingSeedBulkModel_eq_central_of_re_pos
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ScaledSeededExplicitOddTailBulkModel
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
        genuineCentralDoubleSeries s := by
  rw [c2ScaledSeededExplicitOddTailBulkModel_eq_expanded]
  calc
    verticalDepthTailFromTwo s +
          c2TiltRegularizedResidual
            (c2SeededTiltLayerResidual (c2OddTailBalancingSeed coreCutoff K M)) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
      c2ConcreteCutoffError K M s
        = verticalDepthTailFromTwo s +
            c2ScaledSeededExplicitOddTailRegularizedResidual
              (c2OddTailBalancingSeed coreCutoff K M) coreCutoff s +
            c2ConcreteCutoffError K M s := by
              unfold c2ScaledSeededExplicitOddTailRegularizedResidual
              ring
    _ = verticalDepthTailFromTwo s +
          (-c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s) +
          c2ConcreteCutoffError K M s := by
            rw [c2OddTailRegularizedResidual_balancingSeed coreCutoff K M hs]
    _ = genuineCentralDoubleSeries s := by
          unfold c2ScaledSeededExplicitOddTailVerticalRectangularResidual
            c2ConcreteCutoffError c2ConcreteCutoffErrorFromTarget c2AnalyticCentralTarget
            c2RectangularGenuineOperator
          ring

/--
The bulk-right model obtained by inserting the balancing seed into the explicit
odd-tail bulk operator.
-/
noncomputable def c2OddTailBalancingSeedBulkModel
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  c2ScaledSeededExplicitOddTailBulkModel
    (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M

theorem c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    C2IdentityOn oneLtHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      riemannZeta := by
  intro s hs
  calc
    c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s := by
      symm
      simpa [c2OddTailBalancingSeedBulkModel] using
        (c2OddTailGenuineIdentity_balancingSeed_at_of_one_lt_re coreCutoff K M hs)
    _ = c0 s * riemannZeta s := by
      exact genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re s hs

theorem c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_oneLtHalfPlane
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    ∀ s : ℂ, s ∈ oneLtHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s := by
  intro s hs
  symm
  simpa [oneLtHalfPlane, c2OddTailBalancingSeedBulkModel] using
    (c2OddTailGenuineIdentity_balancingSeed_at_of_one_lt_re coreCutoff K M hs)

theorem c2OddTailBalancingSeedBulkModel_eq_continuedCentralOddChannel_on_oneLtHalfPlane
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    ∀ s : ℂ, s ∈ oneLtHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = continuedCentralOddChannel s := by
  intro s hs
  calc
    c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineCentralDoubleSeries s := by
      simpa [c2OddTailBalancingSeedBulkModel] using
        (c2OddTailBalancingSeedBulkModel_eq_central_of_re_pos coreCutoff K M
          (s := s) (lt_trans zero_lt_one hs))
    _ = continuedCentralOddChannel s := by
      symm
      exact continuedCentralOddChannel_eq_genuineCentralDoubleSeries_on_oneLtHalfPlane s hs

/--
Concrete bulk model obtained by calibrating the cutoff against the honest
continued central target instead of the literal `tsum` target.
-/
noncomputable def c2ScaledSeededExplicitOddTailContinuedBulkModel
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  c2AnalyticBulkF
    (c2BulkGdelta
      (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
      (c2ConcreteOddHorizontalDefect coreCutoff))
    (c2BulkEdelta
      (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M))

theorem c2ScaledSeededExplicitOddTailContinuedBulkModel_eq_expanded
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2ScaledSeededExplicitOddTailContinuedBulkModel tiltSeed coreCutoff K M s =
      verticalDepthTailFromTwo s +
        c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
        c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s := by
  unfold c2ScaledSeededExplicitOddTailContinuedBulkModel c2AnalyticBulkF
    c2BulkGdelta c2BulkEdelta
  ring

/--
Residual coming from the vertical resolvent and rectangular truncation relative
to the continued target.
-/
noncomputable def c2ScaledSeededExplicitOddTailContinuedVerticalResidual
    (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    verticalDepthTailFromTwo s +
      rectangularGenuine s K M -
      (2 : ℂ) * continuedCentralOddChannel s

/--
Balancing seed calibrated directly against the continued central target from the
continuation notes.
-/
noncomputable def c2OddTailContinuedBalancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  fun s =>
    (-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s -
      c2ConcreteOddHorizontalDefect coreCutoff s) *
      (1 - q s)

/--
Pointwise rebasing defect between the genuine central target and the continued
central target.
-/
noncomputable def c2ConcreteResolventNonCancellationCentralRebasingError : ℂ → ℂ :=
  fun s => (2 : ℂ) * (genuineCentralDoubleSeries s - continuedCentralOddChannel s)

theorem c2OddTailBalancingSeed_eq_continued_add_rebasingError
    (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    c2OddTailBalancingSeed coreCutoff K M s =
      c2OddTailContinuedBalancingSeed coreCutoff K M s +
        c2ConcreteResolventNonCancellationCentralRebasingError s * (1 - q s) := by
  unfold c2OddTailBalancingSeed c2OddTailContinuedBalancingSeed
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual
    c2ScaledSeededExplicitOddTailContinuedVerticalResidual
    c2ConcreteResolventNonCancellationCentralRebasingError
  ring

theorem c2OddTailBalancingSeed_norm_le_continued_add_centralDefect
    (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ +
        (2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖) *
          ‖1 - q s‖ := by
  rw [c2OddTailBalancingSeed_eq_continued_add_rebasingError coreCutoff K M s]
  have hrebaseNorm :
      ‖c2ConcreteResolventNonCancellationCentralRebasingError s‖ =
        2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
    unfold c2ConcreteResolventNonCancellationCentralRebasingError
    rw [norm_mul]
    simp
  calc
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s +
        c2ConcreteResolventNonCancellationCentralRebasingError s * (1 - q s)‖ ≤
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ +
        ‖c2ConcreteResolventNonCancellationCentralRebasingError s * (1 - q s)‖ := by
          exact norm_add_le _ _
    _ = ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ +
        ‖c2ConcreteResolventNonCancellationCentralRebasingError s‖ * ‖1 - q s‖ := by
          rw [norm_mul]
    _ = ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ +
        (2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖) *
          ‖1 - q s‖ := by
          rw [hrebaseNorm]

theorem c2OddTailBalancingSeed_scaled_bound_of_continued_and_centralDefect
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      continuedSeedUpper centralDefectUpper resolventGapUpper : ℂ → ℝ}
    {s : ℂ}
    (hscale_nonneg : 0 ≤ tiltScale s)
    (hcontinued :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        continuedSeedUpper s)
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hgap : ‖1 - q s‖ ≤ resolventGapUpper s)
    (hscaled :
      (continuedSeedUpper s +
          (2 * centralDefectUpper s) * resolventGapUpper s) *
        tiltScale s ≤
          tiltConstant s) :
    ‖c2OddTailBalancingSeed coreCutoff K M s‖ * tiltScale s ≤
      tiltConstant s := by
  have hfactor :
      2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        2 * centralDefectUpper s := by
    exact mul_le_mul_of_nonneg_left hcentralDefect (by norm_num : (0 : ℝ) ≤ 2)
  have hfactor_nonneg :
      0 ≤ 2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
    positivity
  have hgap_nonneg : 0 ≤ resolventGapUpper s :=
    le_trans (norm_nonneg _) hgap
  have hcentral_nonneg : 0 ≤ 2 * centralDefectUpper s := by
    nlinarith [norm_nonneg (genuineCentralDoubleSeries s - continuedCentralOddChannel s),
      hcentralDefect]
  have hprod :
      (2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖) *
          ‖1 - q s‖ ≤
        (2 * centralDefectUpper s) * resolventGapUpper s := by
    exact mul_le_mul hfactor hgap (norm_nonneg _) hcentral_nonneg
  have hseed :
      ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤
        continuedSeedUpper s +
          (2 * centralDefectUpper s) * resolventGapUpper s := by
    exact le_trans
      (c2OddTailBalancingSeed_norm_le_continued_add_centralDefect
        coreCutoff K M s)
      (add_le_add hcontinued hprod)
  exact le_trans (mul_le_mul_of_nonneg_right hseed hscale_nonneg) hscaled

theorem c2OddTailRegularizedResidual_eq_continued_add_rebasingError_of_re_pos
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ScaledSeededExplicitOddTailRegularizedResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff s =
      c2ScaledSeededExplicitOddTailRegularizedResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff s +
        c2ConcreteResolventNonCancellationCentralRebasingError s := by
  have hden : 1 - q s ≠ 0 := by
    simpa [q] using verticalResolvent_den_ne_zero_of_re_pos s hs
  unfold c2ScaledSeededExplicitOddTailRegularizedResidual
  rw [c2SeededTiltRegularized_eq_resolvent _ hs,
    c2SeededTiltRegularized_eq_resolvent _ hs,
    c2OddTailBalancingSeed_eq_continued_add_rebasingError]
  field_simp [hden]
  ring

theorem c2OddTailContinuedRegularizedResidual_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ScaledSeededExplicitOddTailRegularizedResidual
      (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff s =
      -c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s := by
  have hden : 1 - q s ≠ 0 := by
    simpa [q] using verticalResolvent_den_ne_zero_of_re_pos s hs
  unfold c2ScaledSeededExplicitOddTailRegularizedResidual
  rw [c2SeededTiltRegularized_eq_resolvent _ hs]
  unfold c2OddTailContinuedBalancingSeed
  rw [mul_assoc, mul_inv_cancel₀ hden]
  ring

lemma offCriticalStrip_mem_puncturedOpenRightHalfPlane {s : ℂ}
    (hs : offCriticalStrip s) :
    s ∈ puncturedOpenRightHalfPlane := by
  refine ⟨hs.1, ?_⟩
  intro h1
  have hre : s.re = 1 := by simp [h1]
  linarith [hs.2.1, hre]

theorem c2ConcreteResolventNonCancellationResidual_eq_centralDefect_of_continuation_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {s : ℂ} (hs : offCriticalStrip s) :
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
      genuineCentralDoubleSeries s - continuedCentralOddChannel s := by
  have hsPunct : s ∈ puncturedOpenRightHalfPlane :=
    offCriticalStrip_mem_puncturedOpenRightHalfPlane hs
  have hbulk : c2OddTailBalancingSeedBulkModel coreCutoff K M s =
      genuineCentralDoubleSeries s := by
    simpa [c2OddTailBalancingSeedBulkModel] using
      (c2OddTailBalancingSeedBulkModel_eq_central_of_re_pos coreCutoff K M hs.1)
  calc
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
      c2OddTailBalancingSeedBulkModel coreCutoff K M s - genuineFInfinite s := by
        rfl
    _ = genuineCentralDoubleSeries s - genuineFInfinite s := by
      rw [hbulk]
    _ = genuineCentralDoubleSeries s - continuedCentralOddChannel s := by
      rw [continuation.eq_continuedCentralOddChannel_on_punctured s hsPunct]

theorem c2ConcreteResolventNonCancellationResidual_norm_eq_centralDefect_of_continuation_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {s : ℂ} (hs : offCriticalStrip s) :
    ‖c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ =
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  rw [c2ConcreteResolventNonCancellationResidual_eq_centralDefect_of_continuation_offCritical
    continuation hs]

theorem c2ConcreteResolventNonCancellationResidual_eq_rebased_continuedSeed_of_re_pos
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s +
        c2ConcreteResolventNonCancellationCentralRebasingError s := by
  calc
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s =
      verticalDepthTailFromTwo s +
        c2ScaledSeededExplicitOddTailRegularizedResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff s +
        c2ConcreteCutoffError K M s - genuineFInfinite s := by
          unfold c2ConcreteResolventNonCancellationResidual
            c2ScaledSeededExplicitOddTailBulkModelResidual
          rw [c2ScaledSeededExplicitOddTailBulkModel_eq_expanded]
          unfold c2ScaledSeededExplicitOddTailRegularizedResidual
          ring
    _ = verticalDepthTailFromTwo s +
          (c2ScaledSeededExplicitOddTailRegularizedResidual
              (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff s +
            c2ConcreteResolventNonCancellationCentralRebasingError s) +
          c2ConcreteCutoffError K M s - genuineFInfinite s := by
            rw [c2OddTailRegularizedResidual_eq_continued_add_rebasingError_of_re_pos
              coreCutoff K M hs]
    _ = verticalDepthTailFromTwo s +
          c2ScaledSeededExplicitOddTailRegularizedResidual
            (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff s +
          c2ConcreteCutoffError K M s - genuineFInfinite s +
          c2ConcreteResolventNonCancellationCentralRebasingError s := by
            ring
    _ = c2ConcreteResolventNonCancellationResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s +
        c2ConcreteResolventNonCancellationCentralRebasingError s := by
          unfold c2ConcreteResolventNonCancellationResidual
            c2ScaledSeededExplicitOddTailBulkModelResidual
          rw [c2ScaledSeededExplicitOddTailBulkModel_eq_expanded]
          unfold c2ScaledSeededExplicitOddTailRegularizedResidual
          ring

theorem c2ConcreteResolventNonCancellationResidual_norm_le_rebased_continuedSeed_of_re_pos
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖c2ConcreteResolventNonCancellationResidual
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s‖ +
        2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  rw [c2ConcreteResolventNonCancellationResidual_eq_rebased_continuedSeed_of_re_pos
    coreCutoff K M hs]
  have hrebaseNorm :
      ‖c2ConcreteResolventNonCancellationCentralRebasingError s‖ =
        2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
    unfold c2ConcreteResolventNonCancellationCentralRebasingError
    rw [norm_mul]
    simp
  calc
    ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s +
        c2ConcreteResolventNonCancellationCentralRebasingError s‖ ≤
        ‖c2ConcreteResolventNonCancellationResidual
            (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s‖ +
          ‖c2ConcreteResolventNonCancellationCentralRebasingError s‖ := by
            exact norm_add_le _ _
    _ = ‖c2ConcreteResolventNonCancellationResidual
            (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s‖ +
          2 * ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
            rw [hrebaseNorm]

theorem c2ConcreteResolventNonCancellationResidual_eq_neg_centralDefect_of_continuation_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {s : ℂ} (hs : offCriticalStrip s) :
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s =
      continuedCentralOddChannel s - genuineCentralDoubleSeries s := by
  calc
    c2ConcreteResolventNonCancellationResidual
        (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s =
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s -
        c2ConcreteResolventNonCancellationCentralRebasingError s := by
          rw [c2ConcreteResolventNonCancellationResidual_eq_rebased_continuedSeed_of_re_pos
            coreCutoff K M hs.1]
          ring
    _ = (genuineCentralDoubleSeries s - continuedCentralOddChannel s) -
        c2ConcreteResolventNonCancellationCentralRebasingError s := by
          rw [c2ConcreteResolventNonCancellationResidual_eq_centralDefect_of_continuation_offCritical
            continuation hs]
    _ = continuedCentralOddChannel s - genuineCentralDoubleSeries s := by
          unfold c2ConcreteResolventNonCancellationCentralRebasingError
          ring

theorem c2ConcreteResolventNonCancellationResidual_norm_eq_centralDefect_of_continuedSeed_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {s : ℂ} (hs : offCriticalStrip s) :
    ‖c2ConcreteResolventNonCancellationResidual
        (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s‖ =
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  rw [c2ConcreteResolventNonCancellationResidual_eq_neg_centralDefect_of_continuation_offCritical
    continuation hs]
  have hsymm :
      continuedCentralOddChannel s - genuineCentralDoubleSeries s =
        -(genuineCentralDoubleSeries s - continuedCentralOddChannel s) := by
    ring
  rw [hsymm, norm_neg]

theorem c2ConcreteCutoffError_eq_continued_add_centralDefect
    (K M : ℕ) (s : ℂ) :
    c2ConcreteCutoffError K M s =
      c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s +
        (continuedCentralOddChannel s - genuineCentralDoubleSeries s) := by
  unfold c2ConcreteCutoffError c2ConcreteCutoffErrorFromTarget
    c2AnalyticCentralTarget
  ring

theorem c2ConcreteCutoffError_norm_le_continued_add_centralDefect
    (K M : ℕ) (s : ℂ) :
    ‖c2ConcreteCutoffError K M s‖ ≤
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  rw [c2ConcreteCutoffError_eq_continued_add_centralDefect K M s]
  have hsymm :
      continuedCentralOddChannel s - genuineCentralDoubleSeries s =
        -(genuineCentralDoubleSeries s - continuedCentralOddChannel s) := by
    ring
  calc
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s +
        (continuedCentralOddChannel s - genuineCentralDoubleSeries s)‖ ≤
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ +
        ‖continuedCentralOddChannel s - genuineCentralDoubleSeries s‖ := by
          exact norm_add_le _ _
    _ = ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
          rw [hsymm, norm_neg]

theorem c2ConcreteCutoffError_scaled_bound_of_continued_and_centralDefect
    {K M : ℕ}
    {cutoffConstant cutoffScale
      continuedCutoffUpper centralDefectUpper : ℂ → ℝ}
    {s : ℂ}
    (hscale_nonneg : 0 ≤ cutoffScale s)
    (hcontinued :
      ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
        continuedCutoffUpper s)
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hscaled :
      (continuedCutoffUpper s + centralDefectUpper s) * cutoffScale s ≤
        cutoffConstant s) :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s := by
  have hcutoff :
      ‖c2ConcreteCutoffError K M s‖ ≤
        continuedCutoffUpper s + centralDefectUpper s := by
    exact le_trans
      (c2ConcreteCutoffError_norm_le_continued_add_centralDefect K M s)
      (add_le_add hcontinued hcentralDefect)
  exact le_trans (mul_le_mul_of_nonneg_right hcutoff hscale_nonneg) hscaled

theorem c2ExponentialCutoffErrorFromTarget_continued_eq_exponential_add_centralDefect
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    c2ExponentialCutoffErrorFromTarget continuedCentralOddChannel K M X s =
      c2ExponentialCutoffError K M X s +
        (genuineCentralDoubleSeries s - continuedCentralOddChannel s) := by
  simp [c2ExponentialCutoffError, c2ExponentialCutoffErrorFromTarget,
    c2AnalyticCentralTarget]

theorem c2ExponentialCutoffErrorFromTarget_continued_norm_le_exponential_add_centralDefect
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    ‖c2ExponentialCutoffErrorFromTarget continuedCentralOddChannel K M X s‖ ≤
      ‖c2ExponentialCutoffError K M X s‖ +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  rw [c2ExponentialCutoffErrorFromTarget_continued_eq_exponential_add_centralDefect
    K M X s]
  exact norm_add_le _ _

theorem
    c2ExponentialCutoffErrorFromTarget_continued_norm_le_pointwiseOscillatoryUpper_add_centralDefect
    (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ExponentialCutoffErrorFromTarget continuedCentralOddChannel K M X s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  exact le_trans
    (c2ExponentialCutoffErrorFromTarget_continued_norm_le_exponential_add_centralDefect
      K M X s)
    (add_le_add
      (c2ExponentialCutoffError_norm_le_pointwiseOscillatoryUpper K M J X s hJ)
      le_rfl)

theorem
    c2ConcreteCutoffErrorFromTarget_continued_norm_le_exponentialFromTarget_add_residualWitness
    (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      ‖c2ExponentialCutoffErrorFromTarget continuedCentralOddChannel K M X s‖ +
        rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
  simpa using
    c2ConcreteCutoffErrorFromTarget_norm_le_exponentialFromTarget_add_pointwiseOscillatoryExpUpper
      continuedCentralOddChannel K M J X s hJ

theorem
    c2ConcreteCutoffErrorFromTarget_continued_norm_le_twoResidualWitness_add_concreteCutoff_add_centralDefect
    (K M J : ℕ) (X : ℝ) (s : ℂ) (hJ : 1 ≤ J) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      2 * rectangularExponentialPointwiseOscillatoryExpUpper s K M J X +
        ‖c2ConcreteCutoffError K M s‖ +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
  calc
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      ‖c2ExponentialCutoffErrorFromTarget continuedCentralOddChannel K M X s‖ +
        rectangularExponentialPointwiseOscillatoryExpUpper s K M J X :=
          c2ConcreteCutoffErrorFromTarget_continued_norm_le_exponentialFromTarget_add_residualWitness
            K M J X s hJ
    _ ≤
        (c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s +
          ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖) +
        rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
          exact add_le_add
            (c2ExponentialCutoffErrorFromTarget_continued_norm_le_pointwiseOscillatoryUpper_add_centralDefect
              K M J X s hJ)
            le_rfl
    _ = 2 * rectangularExponentialPointwiseOscillatoryExpUpper s K M J X +
        ‖c2ConcreteCutoffError K M s‖ +
        ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ := by
          unfold c2ExponentialCutoffErrorPointwiseOscillatoryUpper
            c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper
          ring

/--
The continued-target bulk model closes algebraically on the honest continued
central channel throughout the open right half-plane.
-/
theorem c2OddTailContinuedBalancingSeedBulkModel_eq_continuedCentral_of_re_pos
    (coreCutoff : ℕ → ℕ) (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    c2ScaledSeededExplicitOddTailContinuedBulkModel
      (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M s =
        continuedCentralOddChannel s := by
  rw [c2ScaledSeededExplicitOddTailContinuedBulkModel_eq_expanded]
  calc
    verticalDepthTailFromTwo s +
          c2TiltRegularizedResidual
            (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)) s +
        c2ConcreteOddHorizontalDefect coreCutoff s +
      c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s
        = verticalDepthTailFromTwo s +
            c2ScaledSeededExplicitOddTailRegularizedResidual
              (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff s +
            (rectangularGenuine s K M - continuedCentralOddChannel s) := by
              unfold c2ScaledSeededExplicitOddTailRegularizedResidual
                c2ConcreteCutoffErrorFromTarget c2RectangularGenuineOperator
              ring
    _ = verticalDepthTailFromTwo s +
          (-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s) +
          (rectangularGenuine s K M - continuedCentralOddChannel s) := by
            rw [c2OddTailContinuedRegularizedResidual_balancingSeed coreCutoff K M hs]
    _ = continuedCentralOddChannel s := by
          unfold c2ScaledSeededExplicitOddTailContinuedVerticalResidual
          ring

/-- Bulk-right model obtained by inserting the continued balancing seed. -/
noncomputable def c2OddTailContinuedBalancingSeedBulkModel
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  c2ScaledSeededExplicitOddTailContinuedBulkModel
    (c2OddTailContinuedBalancingSeed coreCutoff K M) coreCutoff K M

theorem c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) riemannZeta := by
  intro s hs
  calc
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s =
        continuedCentralOddChannel s := by
          simpa [c2OddTailContinuedBalancingSeedBulkModel] using
            (c2OddTailContinuedBalancingSeedBulkModel_eq_continuedCentral_of_re_pos
              coreCutoff K M (s := s) hs)
    _ = c0 s * riemannZeta s :=
      continuedCentralOddChannel_fundamentalIdentity s hs

theorem c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity_offCritical
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :
    FundamentalIdentityOnOffCriticalStrip
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  FundamentalIdentityOnRightHalfPlane.toOffCriticalStrip
    (c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity coreCutoff K M)

theorem mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_cover_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity cover
    (by
      simpa [hCoverF] using
        c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity_offCritical
          coreCutoff K M)

/-- Specialized near/bulk/edge cover instantiation for the continued bulk model. -/
noncomputable def c2OddTailContinuedBalancingSeedBulkModelCoverData_of_nearBulkEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkEdge near bulk edge hBulkF hEdgeF hcover

/-- Specialized near/bulk/edge cover instantiation for bound-level bulk data. -/
noncomputable def c2OddTailContinuedBalancingSeedBulkModelCoverData_of_nearBulkBoundsEdge
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    OffCriticalCoverData :=
  OffCriticalCoverData.ofNearBulkBoundsEdge near bulk edge hBulkF hEdgeF hcover

theorem mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_nearBulkEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkEdge_offCriticalIdentity
    near bulk edge hBulkF hEdgeF hcover
    (by
      simpa [hNearF] using
        c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity_offCritical
          coreCutoff K M)

theorem
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_nearBulkBoundsEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_nearBulkBoundsEdge_offCriticalIdentity
    near bulk edge hBulkF hEdgeF hcover
    (by
      simpa [hNearF] using
        c2OddTailContinuedBalancingSeedBulkModel_fundamentalIdentity_offCritical
          coreCutoff K M)

/-- Near-axis data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelNearAxisData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  near_axis :
    NearAxisCertificate
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
      riemannZeta

noncomputable def C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M) :
    NearAxisRouteData where
  F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
  near_axis := data.near_axis

noncomputable def C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofNearAxisRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (hF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M where
  near_axis :=
    {
      radius := near.near_axis.radius
      radius_pos := near.near_axis.radius_pos
      radius_le_half := near.near_axis.radius_le_half
      nonvanishing := by
        intro rho s hrho hs
        simpa [hF] using near.near_axis.nonvanishing hrho hs
    }

theorem c2OddTailContinuedBalancingSeedBulkModel_eq_genuineFInfinite_on_punctured
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData) :
    ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s := by
  intro s hs
  calc
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s =
        continuedCentralOddChannel s := by
          simpa [c2OddTailContinuedBalancingSeedBulkModel] using
            (c2OddTailContinuedBalancingSeedBulkModel_eq_continuedCentral_of_re_pos
              coreCutoff K M (s := s) hs.1)
    _ = genuineFInfinite s := by
          symm
          exact continuation.eq_continuedCentralOddChannel_on_punctured s hs

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofGenuineFInfiniteNearAxisData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (near : GenuineFInfiniteNearAxisData) :
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M where
  near_axis :=
    {
      radius := near.near_axis.radius
      radius_pos := near.near_axis.radius_pos
      radius_le_half := near.near_axis.radius_le_half
      nonvanishing := by
        intro rho s hrho hs
        have hsOff : offCriticalStrip s :=
          near.near_axis.offCriticalStrip_of_mem_transversalWindow hrho hs
        have hsPunct : s ∈ puncturedOpenRightHalfPlane := by
          refine ⟨hsOff.1, ?_⟩
          intro hOne
          have hre : s.re = 1 := by simp [hOne]
          linarith [hsOff.2.1, hre]
        rw [c2OddTailContinuedBalancingSeedBulkModel_eq_genuineFInfinite_on_punctured
          (coreCutoff := coreCutoff) (K := K) (M := M) continuation s hsPunct]
        exact near.near_axis.nonvanishing hrho hs
    }

/-- Route-level bulk data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelBulkRouteData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  route : RegionalVerticalBulkRouteData
  F_eq : route.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

/-- Bounds-level bulk data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  bounds : RegionalVerticalBulkBoundsData
  F_eq : bounds.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

/-- Nonvanishing bulk-region data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelBulkRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  bulk : BulkRegionRouteData
  F_eq : bulk.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

/-- Quartet route-level bulk data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  route : RegionalVerticalQuartetBulkRouteData
  F_eq : route.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

/-- Quartet bounds-level bulk data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  bounds : RegionalVerticalQuartetBulkBoundsData
  F_eq : bounds.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

noncomputable def C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData.toBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRouteData coreCutoff K M where
  route := data.bounds.toRouteData
  F_eq := data.F_eq

noncomputable def C2OddTailContinuedBalancingSeedBulkModelBulkRouteData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelBulkRouteData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M where
  bulk := data.route.toBulkRegionRouteData
  F_eq := by
    simpa [RegionalVerticalBulkRouteData.toBulkRegionRouteData] using data.F_eq

noncomputable def C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M :=
  data.toBulkRouteData.toBulkRegionData

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M where
  bulk := data.route.toBulkRegionRouteData
  F_eq := by
    simpa [RegionalVerticalQuartetBulkRouteData.toBulkRegionRouteData] using data.F_eq

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData.toQuartetBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData coreCutoff K M where
  route := data.bounds.toRouteData
  F_eq := by
    simpa [RegionalVerticalQuartetBulkBoundsData.toRouteData] using data.F_eq

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData.toBulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M :=
  data.toQuartetBulkRouteData.toBulkRegionData

/-- Edge data pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelEdgeData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  edgeRegion : Set ℂ
  edge_nonvanishing : ∀ {s : ℂ}, s ∈ edgeRegion →
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0

noncomputable def C2OddTailContinuedBalancingSeedBulkModelEdgeData.toEdgeRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M) :
    EdgeRouteData where
  F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
  edgeRegion := data.edgeRegion
  edge_nonvanishing := data.edge_nonvanishing

noncomputable def C2OddTailContinuedBalancingSeedBulkModelEdgeData.ofEdgeRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (edge : EdgeRouteData)
    (hF : edge.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M where
  edgeRegion := edge.edgeRegion
  edge_nonvanishing := by
    intro s hs
    simpa [hF] using edge.edge_nonvanishing hs

def C2OddTailContinuedBalancingSeedBulkModelEdgeData.empty
    {coreCutoff : ℕ → ℕ} {K M : ℕ} :
    C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M where
  edgeRegion := ∅
  edge_nonvanishing := by
    intro s hs
    cases hs

/-- Near/bulk/edge cover pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  bulk : C2OddTailContinuedBalancingSeedBulkModelBulkRouteData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion

/-- Bound-level near/bulk/edge cover pinned to the continued balancing-seed bulk model. -/
structure C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M
  bulk : C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData coreCutoff K M
  edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M
  cover : ∀ s : ℂ, offCriticalStrip s →
    s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
      s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion

noncomputable def C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData.ofNearBulkEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk : C2OddTailContinuedBalancingSeedBulkModelBulkRouteData coreCutoff K M)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hEdgeF : edge.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion) :
    C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData coreCutoff K M where
  near :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofNearAxisRouteData near hNearF
  bulk := bulk
  edge := C2OddTailContinuedBalancingSeedBulkModelEdgeData.ofEdgeRouteData edge hEdgeF
  cover := by
    change ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion
    exact hcover

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData.ofNearBulkBoundsEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk : C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData coreCutoff K M)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hEdgeF : edge.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion) :
    C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData coreCutoff K M where
  near :=
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofNearAxisRouteData near hNearF
  bulk := bulk
  edge := C2OddTailContinuedBalancingSeedBulkModelEdgeData.ofEdgeRouteData edge hEdgeF
  cover := by
    change ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion
    exact hcover

noncomputable def C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData.toOffCriticalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData coreCutoff K M) :
    OffCriticalCoverData :=
  c2OddTailContinuedBalancingSeedBulkModelCoverData_of_nearBulkEdge
    data.near.toNearAxisRouteData
    data.bulk.route
    data.edge.toEdgeRouteData
    (by
      simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
        data.bulk.F_eq)
    rfl
    data.cover

noncomputable def
    C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData.toOffCriticalCoverData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData coreCutoff K M) :
    OffCriticalCoverData :=
  c2OddTailContinuedBalancingSeedBulkModelCoverData_of_nearBulkBoundsEdge
    data.near.toNearAxisRouteData
    data.bulk.bounds
    data.edge.toEdgeRouteData
    (by
      simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
        data.bulk.F_eq)
    rfl
    data.cover

theorem offCriticalStripNonvanishing_of_oddTailContinuedBalancingSeedBulkModelNearBulkEdgeData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData coreCutoff K M) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  simpa [C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData.toOffCriticalCoverData,
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem
    offCriticalStripNonvanishing_of_oddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData coreCutoff K M) :
    offCriticalStripNonvanishing
      (c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M) := by
  simpa [C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData.toOffCriticalCoverData,
    C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData] using
    offCriticalStripNonvanishing_of_coverData data.toOffCriticalCoverData

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_pinnedNearBulkEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelNearBulkEdgeData coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_cover_offCritical
    data.toOffCriticalCoverData rfl

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_pinnedNearBulkBoundsEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelNearBulkBoundsEdgeData coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_cover_offCritical
    data.toOffCriticalCoverData rfl

/-!
Regional bulk data with the target fixed to the continued balancing-seed bulk
model.

This mirrors `Analytic/GenuineBulk.lean`: the generic roadmap structures remain
the execution target, but future quantitative bulk decompositions can now land
directly on `c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M`.
-/

/-- Route-level regional bulk data whose target is definitionally the continued model. -/
structure C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  bulkRegion : Set ℂ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion →
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion →
    Kdelta s = K2 s / (1 - q s) + Gdelta s
  dominance : ∀ s : ℂ, s ∈ bulkRegion →
    ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖

/-- Bound-level regional bulk data whose target is definitionally the continued model. -/
structure C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) where
  bulkRegion : Set ℂ
  Kdelta : ℂ → ℂ
  K2 : ℂ → ℂ
  Gdelta : ℂ → ℂ
  Edelta : ℂ → ℂ
  K2Lower : ℂ → ℝ
  GUpper : ℂ → ℝ
  EUpper : ℂ → ℝ
  bulk_offCritical : ∀ {s : ℂ}, s ∈ bulkRegion → offCriticalStrip s
  decomposition : ∀ s : ℂ, s ∈ bulkRegion →
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = Kdelta s + Edelta s
  resolvent_shape : ∀ s : ℂ, s ∈ bulkRegion →
    Kdelta s = K2 s / (1 - q s) + Gdelta s
  K2_lower : ∀ s : ℂ, s ∈ bulkRegion → K2Lower s ≤ ‖K2 s‖
  G_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Gdelta s‖ ≤ GUpper s
  E_upper : ∀ s : ℂ, s ∈ bulkRegion → ‖Edelta s‖ ≤ EUpper s
  dominance_bounds : ∀ s : ℂ, s ∈ bulkRegion →
    GUpper s + EUpper s < K2Lower s / (1 + ‖q s‖)

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData.ofRegionalVerticalBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : RegionalVerticalBulkRouteData)
    (hF : ∀ s : ℂ, s ∈ data.bulkRegion →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = data.F s) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M where
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := by
    intro s hs
    rw [hF s hs]
    exact data.decomposition s hs
  resolvent_shape := data.resolvent_shape
  dominance := data.dominance

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : RegionalVerticalBulkBoundsData)
    (hF : ∀ s : ℂ, s ∈ data.bulkRegion →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = data.F s) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M where
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  K2Lower := data.K2Lower
  GUpper := data.GUpper
  EUpper := data.EUpper
  bulk_offCritical := data.bulk_offCritical
  decomposition := by
    intro s hs
    rw [hF s hs]
    exact data.decomposition s hs
  resolvent_shape := data.resolvent_shape
  K2_lower := data.K2_lower
  G_upper := data.G_upper
  E_upper := data.E_upper
  dominance_bounds := data.dominance_bounds

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData.ofRegionalVerticalBulkRouteDataOn
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : RegionalVerticalBulkRouteData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion)
    (hF : ∀ s : ℂ, s ∈ subRegion →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = data.F s) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M :=
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData.ofRegionalVerticalBulkRouteData
    (data.restrict subRegion hsub)
    (by
      intro s hs
      exact hF s hs)

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsDataOn
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : RegionalVerticalBulkBoundsData)
    (subRegion : Set ℂ)
    (hsub : ∀ {s : ℂ}, s ∈ subRegion → s ∈ data.bulkRegion)
    (hF : ∀ s : ℂ, s ∈ subRegion →
      c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s = data.F s) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M :=
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    (data.restrict subRegion hsub)
    (by
      intro s hs
      exact hF s hs)

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData.toRegionalVerticalBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M) :
    RegionalVerticalBulkRouteData where
  F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
  bulkRegion := data.bulkRegion
  Kdelta := data.Kdelta
  K2 := data.K2
  Gdelta := data.Gdelta
  Edelta := data.Edelta
  bulk_offCritical := data.bulk_offCritical
  decomposition := data.decomposition
  resolvent_shape := data.resolvent_shape
  dominance := data.dominance

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.toRegionalVerticalBulkBoundsData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M) :
    RegionalVerticalBulkBoundsData where
  F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
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

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.toRegionalBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M where
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
    exact regionalVerticalBulk_dominance_of_bounds
      data.toRegionalVerticalBulkBoundsData hs

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData.toPinnedBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRouteData coreCutoff K M where
  route := data.toRegionalVerticalBulkRouteData
  F_eq := rfl

noncomputable def
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.toPinnedBulkBoundsData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M) :
    C2OddTailContinuedBalancingSeedBulkModelBulkBoundsData coreCutoff K M where
  bounds := data.toRegionalVerticalBulkBoundsData
  F_eq := rfl

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_regionalBulkRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M)
    {s : ℂ} (hs : s ∈ data.bulkRegion) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing data.toRegionalVerticalBulkRouteData hs

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_regionalBulkBoundsData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M)
    {s : ℂ} (hs : s ∈ data.bulkRegion) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    data.toRegionalVerticalBulkBoundsData hs

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_bulkRegionData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M)
    {s : ℂ} (hs : s ∈ data.bulk.bulkRegion) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  simpa [data.F_eq] using data.bulk.bulk_nonvanishing hs

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_quartetRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData coreCutoff K M)
    {s : ℂ} (hs : s ∈ data.route.bulkRegion) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  simpa [data.F_eq] using regionalVerticalQuartetBulk_nonvanishing data.route hs

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_quartetBoundsData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData coreCutoff K M)
    {s : ℂ} (hs : s ∈ data.bounds.bulkRegion) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  simpa [data.F_eq] using regionalVerticalQuartetBulk_nonvanishing_of_bounds data.bounds hs

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_bulkRegionCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (bulk : C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_cover_offCritical
    (OffCriticalCoverData.ofNearBulkRegionEdge
      near.toNearAxisRouteData
      bulk.bulk
      edge.toEdgeRouteData
      (by
        simpa [C2OddTailContinuedBalancingSeedBulkModelNearAxisData.toNearAxisRouteData]
          using bulk.F_eq)
      rfl
      cover)
    rfl

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetBulkCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (bulk :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkRouteData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_bulkRegionCover
      near
      bulk.toBulkRegionData
      edge
      (by
        change ∀ s : ℂ, offCriticalStrip s →
          s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
            s ∈ bulk.route.bulkRegion ∨ s ∈ edge.edgeRegion
        exact cover)

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetBoundsCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (bulk :
      C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetBulkCover
      near
      bulk.toQuartetBulkRouteData
      edge
      (by
        change ∀ s : ℂ, offCriticalStrip s →
          s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
            s ∈ bulk.bounds.bulkRegion ∨ s ∈ edge.edgeRegion
        exact cover)

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBulkCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (bulk : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  have hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.toPinnedBulkRouteData.route.bulkRegion ∨ s ∈ edge.edgeRegion := by
    change ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion
    exact cover
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_pinnedNearBulkEdge
    {
      near := near
      bulk := bulk.toPinnedBulkRouteData
      edge := edge
      cover := hcover
    }

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBulkBoundsCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (bulk :
      C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  have hcover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.toPinnedBulkBoundsData.bounds.bulkRegion ∨ s ∈ edge.edgeRegion := by
    change ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion
    exact cover
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_pinnedNearBulkBoundsEdge
      {
        near := near
        bulk := bulk.toPinnedBulkBoundsData
        edge := edge
        cover := hcover
      }

theorem
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regional_genericNearEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk : C2OddTailContinuedBalancingSeedBulkModelRegionalBulkRouteData coreCutoff K M)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hEdgeF : edge.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBulkCover
    (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofNearAxisRouteData near hNearF)
    bulk
    (C2OddTailContinuedBalancingSeedBulkModelEdgeData.ofEdgeRouteData edge hEdgeF)
    cover

theorem
  mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBounds_genericNearEdge
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (near : NearAxisRouteData)
    (bulk :
      C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M)
    (edge : EdgeRouteData)
    (hNearF : near.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (hEdgeF : edge.F = c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBulkBoundsCover
      (C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofNearAxisRouteData near hNearF)
      bulk
      (C2OddTailContinuedBalancingSeedBulkModelEdgeData.ofEdgeRouteData edge hEdgeF)
      cover

end C2
