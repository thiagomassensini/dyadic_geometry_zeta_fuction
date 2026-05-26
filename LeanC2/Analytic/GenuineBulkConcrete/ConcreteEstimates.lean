import LeanC2.Analytic.GenuineBulkConcrete.Base

namespace C2

/-!
## Concrete regional bulk package for the continued balancing-seed model

This is the off-critical bulk certificate expected by the pinned continued route.
It keeps the quantitative inputs in the same concrete format already used by the
route-level bulk machinery: scaled seed bound for the tilt, geometric layer
control for the horizontal odd defect, scaled cutoff bound against the honest
continued target, and the final dominance inequality.
-/

structure C2OddTailContinuedBalancingSeedBulkConcreteEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound :
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2OddTailContinuedBalancingSeedBulkConcreteRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkConcreteEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailContinuedBalancingSeedBulkConcrete_mem_regularizedHorizontalRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkRegularizedHorizontalRegion
      (c2TiltRegularizedResidual
        (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)))
      (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)
      (c2ConcreteOddHorizontalLayerDefect coreCutoff)
      (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  have hseed :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s :=
    c2TiltSeed_bound_from_scaled hs.tiltScale_pos hs.tilt_scaled_bound
  have htiltLayer : ∀ j : ℕ,
      ‖c2SeededTiltLayerResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j :=
    c2SeededTiltLayerResidual_bound hseed
  exact
    {
      offCritical := hs.offCritical
      tilt_bound :=
        c2TiltRegularizedResidual_bound_of_analytic_geometric
          hs.offCritical hs.tiltScale_pos hs.tiltConstant_nonneg htiltLayer
      horizontalScale_pos := hs.horizontalScale_pos
      horizontalConstant_nonneg := hs.horizontalConstant_nonneg
      horizontalRatio_nonneg := hs.horizontalRatio_nonneg
      horizontalRatio_lt_one := hs.horizontalRatio_lt_one
      horizontalLayer_bound := hs.horizontalLayer_bound
      cutoffScale_pos := hs.cutoffScale_pos
      cutoff_scaled_bound := hs.cutoff_scaled_bound
      dominance := hs.dominance
    }

noncomputable def c2OddTailContinuedBalancingSeedBulkConcreteGenericBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  c2BulkRegularizedHorizontalBoundsData
    (c2TiltRegularizedResidual
      (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)))
    (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)
    (c2ConcreteOddHorizontalLayerDefect coreCutoff)
    (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale

noncomputable def c2OddTailContinuedBalancingSeedBulkConcreteBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData coreCutoff K M :=
  C2OddTailContinuedBalancingSeedBulkModelRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsDataOn
    (c2OddTailContinuedBalancingSeedBulkConcreteGenericBoundsData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    (c2OddTailContinuedBalancingSeedBulkConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    (by
      intro s hs
      exact c2OddTailContinuedBalancingSeedBulkConcrete_mem_regularizedHorizontalRegion hs)
    (by
      intro s _hs
      rfl)

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_concreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  exact c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_regionalBulkBoundsData
    (c2OddTailContinuedBalancingSeedBulkConcreteBoundsData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    hs

theorem c2OddTailContinuedBalancingSeedBulkConcreteRegion_nonempty_iff
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    Set.Nonempty
      (c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) ↔
      ∃ s : ℂ,
        C2OddTailContinuedBalancingSeedBulkConcreteEstimates
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  rfl

theorem
    c2OddTailContinuedBalancingSeedBulkModel_exists_nonvanishing_point_of_nonempty_concreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∧
        c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s, hs,
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_concreteRegion hs⟩

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_concreteCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_regionalBulkBoundsCover
      near
      (c2OddTailContinuedBalancingSeedBulkConcreteBoundsData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
      edge
      cover

theorem c2LiftBulkCover_of_subset
    {nearRegion bulkRegion targetRegion edgeRegion : Set ℂ}
    (hsubset : ∀ ⦃s : ℂ⦄, s ∈ bulkRegion → s ∈ targetRegion)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearRegion ∨ s ∈ bulkRegion ∨ s ∈ edgeRegion) :
    ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearRegion ∨ s ∈ targetRegion ∨ s ∈ edgeRegion := by
  intro s hs
  rcases cover s hs with hnear | hbulk | hedge
  · exact Or.inl hnear
  · exact Or.inr <| Or.inl <| hsubset hbulk
  · exact Or.inr <| Or.inr hedge

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_concreteSubsetCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {bulkRegion : Set ℂ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (hsubset : ∀ ⦃s : ℂ⦄, s ∈ bulkRegion →
      s ∈ c2OddTailContinuedBalancingSeedBulkConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulkRegion ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_concreteCover
      near edge (c2LiftBulkCover_of_subset hsubset cover)

/-!
## Quartet-refined concrete bulk package for the continued model

This is the same concrete continued bulk model as above, but routed through the
quartet vertical interface. The new dominance budget pays first for the explicit
quartet vertical tail and then for the analytic tilt, horizontal, and cutoff
terms.
-/

structure C2OddTailContinuedBalancingSeedBulkQuartetConcreteEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound :
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetConcreteEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_quartetRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2QuartetBulkErrorRegion
      (c2TiltRegularizedResidual
        (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)))
      (c2ConcreteOddHorizontalDefect coreCutoff)
      (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)
      (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (c2CutoffUpperFromScale cutoffConstant cutoffScale) := by
  have hseed :
      ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
        tiltConstant s / tiltScale s :=
    c2TiltSeed_bound_from_scaled hs.tiltScale_pos hs.tilt_scaled_bound
  have htiltLayer : ∀ j : ℕ,
      ‖c2SeededTiltLayerResidual
          (c2OddTailContinuedBalancingSeed coreCutoff K M) s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j :=
    c2SeededTiltLayerResidual_bound hseed
  have htilt :
      ‖c2TiltRegularizedResidual
          (c2SeededTiltLayerResidual
            (c2OddTailContinuedBalancingSeed coreCutoff K M)) s‖ ≤
        c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s :=
    c2TiltRegularizedResidual_bound_of_analytic_geometric
      hs.offCritical hs.tiltScale_pos hs.tiltConstant_nonneg htiltLayer
  have hhorizontal :
      ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s := by
    unfold c2ConcreteOddHorizontalDefect
    exact c2HorizontalRegularizedDefect_bound
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one
      hs.horizontalLayer_bound
  have hG :
      ‖c2BulkGdelta
          (c2TiltRegularizedResidual
            (c2SeededTiltLayerResidual
              (c2OddTailContinuedBalancingSeed coreCutoff K M)))
          (c2ConcreteOddHorizontalDefect coreCutoff) s‖ ≤
        c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio) s := by
    unfold c2BulkGdelta c2BulkGUpper
    exact le_trans (norm_add_le _ _) (add_le_add htilt hhorizontal)
  have hcutoff :
      ‖c2BulkEdelta
          (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M) s‖ ≤
        c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s := by
    simpa [c2BulkEdelta, c2BulkEUpper] using
      c2Cutoff_bound_from_scaled hs.cutoffScale_pos hs.cutoff_scaled_bound
  exact ⟨hs.offCritical, hG, hcutoff, hs.quartet_dominance⟩

noncomputable def c2OddTailContinuedBalancingSeedBulkQuartetConcreteGenericBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalQuartetBulkBoundsData :=
  c2QuartetBulkErrorsBoundsData
    (c2TiltRegularizedResidual
      (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)))
    (c2ConcreteOddHorizontalDefect coreCutoff)
    (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)
    (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
    (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
    (c2CutoffUpperFromScale cutoffConstant cutoffScale)

theorem c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  have hq :
      s ∈ c2QuartetBulkErrorRegion
        (c2TiltRegularizedResidual
          (c2SeededTiltLayerResidual (c2OddTailContinuedBalancingSeed coreCutoff K M)))
        (c2ConcreteOddHorizontalDefect coreCutoff)
        (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)
        (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
        (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
        (c2CutoffUpperFromScale cutoffConstant cutoffScale) :=
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_quartetRegion hs
  have hnonzero :
      c2AnalyticBulkF
        (c2BulkGdelta
          (c2TiltRegularizedResidual
            (c2SeededTiltLayerResidual
              (c2OddTailContinuedBalancingSeed coreCutoff K M)))
          (c2ConcreteOddHorizontalDefect coreCutoff))
        (c2BulkEdelta
          (c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M)) s ≠ 0 :=
    c2QuartetBulkErrors_nonvanishing_of_mem hq
  simpa [c2OddTailContinuedBalancingSeedBulkModel,
    c2ScaledSeededExplicitOddTailContinuedBulkModel] using hnonzero

theorem c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion_nonempty_iff
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    Set.Nonempty
      (c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) ↔
      ∃ s : ℂ,
        C2OddTailContinuedBalancingSeedBulkQuartetConcreteEstimates
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  rfl

theorem
    c2OddTailContinuedBalancingSeedBulkModel_exists_nonzero_of_nonempty_quartetConcreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∧
        c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s, hs,
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion hs⟩

noncomputable def c2OddTailContinuedBalancingSeedBulkQuartetConcreteBoundsData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2OddTailContinuedBalancingSeedBulkModelQuartetBulkBoundsData coreCutoff K M where
  bounds :=
    c2OddTailContinuedBalancingSeedBulkQuartetConcreteGenericBoundsData
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
  F_eq := by
    rfl

noncomputable def c2OddTailContinuedBalancingSeedBulkQuartetConcreteBulkRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M where
  bulk :=
    {
      F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
      bulkRegion :=
        c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
      bulk_nonvanishing := by
        intro s hs
        exact
          c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
            hs
    }
  F_eq := rfl

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_quartetConcreteCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_bulkRegionCover
      near
      (c2OddTailContinuedBalancingSeedBulkQuartetConcreteBulkRegionData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
      edge
      cover

/-- Continuation data type specialized to the balancing-seed bulk model. -/
abbrev C2OddTailBalancingSeedBulkModelContinuationData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :=
  ContinuationFromOneLtData
    (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta

/-- Comparison interface for transporting the balancing-seed bulk model from `Re(s) > 1`. -/
abbrev C2OddTailBalancingSeedBulkModelComparisonFromOneLtData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :=
  ComparisonFromOneLtData
    (c2OddTailBalancingSeedBulkModel coreCutoff K M)
    genuineFInfinite

/--
Comparison interface for the balancing-seed bulk model split into the punctured
right half-plane plus the special value at `s = 1`.
-/
abbrev C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :=
  ComparisonFromOneLtAtOneData
    (c2OddTailBalancingSeedBulkModel coreCutoff K M)
    genuineFInfinite

/--
Punctured-domain comparison of the balancing-seed bulk model with the honest
continued central target.
-/
abbrev C2OddTailBalancingSeedBulkModelComparisonToContinuedCentralData
    (coreCutoff : ℕ → ℕ) (K M : ℕ) :=
  ComparisonFromOneLtPuncturedData
    (c2OddTailBalancingSeedBulkModel coreCutoff K M)
    continuedCentralOddChannel

noncomputable def c2OddTailBalancingSeedBulkModelContinuationData_of_eqOnOpenRightHalfPlane
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : GenuineFInfiniteContinuationData)
    (hEq : ∀ s : ℂ, s ∈ openRightHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s) :
    C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M :=
  ContinuationFromOneLtData.of_eqOnOpenRightHalfPlane data hEq

def c2OddTailBalancingSeedBulkModelComparisonToContinuedCentralData_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane) :
    C2OddTailBalancingSeedBulkModelComparisonToContinuedCentralData coreCutoff K M :=
  ComparisonFromOneLtPuncturedData.of_analyticOnNhd_punctured
    hBulk continuedCentralOddChannel_analyticOnNhd_punctured

theorem c2OddTailBalancingSeedBulkModel_eq_continuedCentral_on_punctured_of_central
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hCentral : ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      genuineCentralDoubleSeries s = continuedCentralOddChannel s) :
    ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = continuedCentralOddChannel s := by
  intro s hs
  calc
    c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineCentralDoubleSeries s := by
      simpa [c2OddTailBalancingSeedBulkModel] using
        (c2OddTailBalancingSeedBulkModel_eq_central_of_re_pos coreCutoff K M
          (s := s) hs.1)
    _ = continuedCentralOddChannel s := hCentral s hs

def c2OddTailBalancingSeedBulkModelComparisonToContinuedCentral_of_central
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hCentral : ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      genuineCentralDoubleSeries s = continuedCentralOddChannel s) :
    C2OddTailBalancingSeedBulkModelComparisonToContinuedCentralData coreCutoff K M :=
  ComparisonFromOneLtPuncturedData.of_eqOnPuncturedOpenRightHalfPlane
    (c2OddTailBalancingSeedBulkModel_eq_continuedCentral_on_punctured_of_central
      (coreCutoff := coreCutoff) (K := K) (M := M) hCentral)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_offCritical_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane) :
    FundamentalIdentityOnOffCriticalStrip
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta := by
  exact ComparisonFromOneLtPuncturedData.transferOffCriticalIdentity
    (c2OddTailBalancingSeedBulkModelComparisonToContinuedCentralData_of_analyticOnNhd
      hBulk)
    continuedCentralOddChannel_fundamentalIdentity
    (c2OddTailBalancingSeedBulkModel_eq_continuedCentralOddChannel_on_oneLtHalfPlane
      coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_offCritical_of_central
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hCentral : ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      genuineCentralDoubleSeries s = continuedCentralOddChannel s) :
    FundamentalIdentityOnOffCriticalStrip
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta := by
  exact ComparisonFromOneLtPuncturedData.transferOffCriticalIdentity
    (c2OddTailBalancingSeedBulkModelComparisonToContinuedCentral_of_central
      (coreCutoff := coreCutoff) (K := K) (M := M) hCentral)
    continuedCentralOddChannel_fundamentalIdentity
    (c2OddTailBalancingSeedBulkModel_eq_continuedCentralOddChannel_on_oneLtHalfPlane
      coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_openRightHalfPlane
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M) :
    ∀ s : ℂ, s ∈ openRightHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s :=
  comparison.eqOnOpenRightHalfPlane
    (c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_oneLtHalfPlane coreCutoff K M)

noncomputable def c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M) :
    C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M :=
  comparison.toComparisonFromOneLtData

theorem c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_openRightHalfPlane_of_atOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M) :
    ∀ s : ℂ, s ∈ openRightHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s :=
  ComparisonFromOneLtData.eqOnOpenRightHalfPlane
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne comparison)
    (c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_oneLtHalfPlane coreCutoff K M)

def c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M :=
  ComparisonFromOneLtAtOneData.of_analyticOnNhd_punctured hBulk hGenuine hEqAtOne

noncomputable def c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_continuation
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_analyticOnNhd
    hBulk continuation.analyticOnNhd_punctured hEqAtOne

noncomputable def c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_analyticOnNhd
      hBulk hGenuine hEqAtOne)

noncomputable def c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_continuation
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_continuation
      continuation hBulk hEqAtOne)

noncomputable def c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLt
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M) :
    C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M :=
  comparison.transferContinuation continuation
    (c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_oneLtHalfPlane coreCutoff K M)

noncomputable def c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLtAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M) :
    C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLt
    continuation
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne comparison)

noncomputable def c2OddTailBalancingSeedBulkModelContinuationData_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLtAtOne
    continuation
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_analyticOnNhd
      hBulk hGenuine hEqAtOne)

noncomputable def c2OddTailBalancingSeedBulkModelContinuationData_of_continuation
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M :=
  c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLtAtOne
    continuation
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData_of_continuation
      continuation hBulk hEqAtOne)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_of_eqOnOpenRightHalfPlane
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : GenuineFInfiniteContinuationData)
    (hEq : ∀ s : ℂ, s ∈ openRightHalfPlane →
      c2OddTailBalancingSeedBulkModel coreCutoff K M s = genuineFInfinite s) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_eqOnOpenRightHalfPlane
    data hEq).to_fundamentalRightHalfPlane
      (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_of_comparisonFromOneLt
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLt
    continuation comparison).to_fundamentalRightHalfPlane
      (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_of_comparisonFromOneLtAtOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (comparison :
      C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_comparisonFromOneLtAtOne
    continuation comparison).to_fundamentalRightHalfPlane
      (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_of_analyticOnNhd
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_analyticOnNhd
    continuation hBulk hGenuine hEqAtOne).to_fundamentalRightHalfPlane
      (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

theorem c2OddTailBalancingSeedBulkModel_fundamentalIdentity_of_continuation
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_continuation
    continuation hBulk hEqAtOne).to_fundamentalRightHalfPlane
      (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

theorem C2OddTailBalancingSeedBulkModelContinuationData.fundamentalIdentity
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M) :
    FundamentalIdentityOnRightHalfPlane
      (c2OddTailBalancingSeedBulkModel coreCutoff K M) riemannZeta :=
  data.to_fundamentalRightHalfPlane
    (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)

noncomputable def C2OddTailBalancingSeedBulkModelContinuationData.toGenuineRouteData
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M)
    (hNonvanishing :
      offCriticalStripNonvanishing
        (c2OddTailBalancingSeedBulkModel coreCutoff K M)) :
    GenuineRouteData :=
  ContinuationFromOneLtData.toGenuineRouteData data
    (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)
    hNonvanishing

noncomputable def C2OddTailBalancingSeedBulkModelContinuationData.toGenuineRouteDataOfCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    GenuineRouteData :=
  ContinuationFromOneLtData.toGenuineRouteDataOfCover data
    (c2OddTailBalancingSeed_bulkModel_identity_on_oneLtHalfPlane coreCutoff K M)
    cover hCoverF

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModelContinuation
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M)
    (hNonvanishing :
      offCriticalStripNonvanishing
        (c2OddTailBalancingSeedBulkModel coreCutoff K M)) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteData hNonvanishing)

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModelContinuation_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (data : C2OddTailBalancingSeedBulkModelContinuationData coreCutoff K M)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteDataOfCover cover hCoverF)

noncomputable def c2OddTailBalancingSeedBulkModelGenuineRouteData_of_analyticOnNhd_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    GenuineRouteData :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_analyticOnNhd
    continuation hBulk hGenuine hEqAtOne).toGenuineRouteDataOfCover cover hCoverF

noncomputable def c2OddTailBalancingSeedBulkModelGenuineRouteData_of_continuation_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    GenuineRouteData :=
  (c2OddTailBalancingSeedBulkModelContinuationData_of_continuation
    continuation hBulk hEqAtOne).toGenuineRouteDataOfCover cover hCoverF

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModel_analyticOnNhd_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (c2OddTailBalancingSeedBulkModelGenuineRouteData_of_analyticOnNhd_cover
      continuation hBulk hGenuine hEqAtOne cover hCoverF)

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModel_continuation_cover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (hEqAtOne :
      c2OddTailBalancingSeedBulkModel coreCutoff K M 1 = genuineFInfinite 1)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (c2OddTailBalancingSeedBulkModelGenuineRouteData_of_continuation_cover
      continuation hBulk hEqAtOne cover hCoverF)

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModel_analyticOnNhd_cover_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hBulk : AnalyticOnNhd ℂ
      (c2OddTailBalancingSeedBulkModel coreCutoff K M)
      puncturedOpenRightHalfPlane)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity cover
    (by
      simpa [hCoverF] using
        c2OddTailBalancingSeedBulkModel_fundamentalIdentity_offCritical_of_analyticOnNhd
          (coreCutoff := coreCutoff) (K := K) (M := M) hBulk)

theorem mathlibRiemannHypothesis_of_oddTailBalancingSeedBulkModel_central_bridge_cover_offCritical
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (hCentral : ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      genuineCentralDoubleSeries s = continuedCentralOddChannel s)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = c2OddTailBalancingSeedBulkModel coreCutoff K M) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_coverData_offCriticalIdentity cover
    (by
      simpa [hCoverF] using
        c2OddTailBalancingSeedBulkModel_fundamentalIdentity_offCritical_of_central
          (coreCutoff := coreCutoff) (K := K) (M := M) hCentral)

/--
The existing concrete scaled-seeded bulk bounds data restricted to the stronger
operational region where the horizontal estimate is explicit and the cutoff is
certified against `c0 * ζ`.
-/
noncomputable def c2BulkScaledSeededExplicitOddTailC0ZetaCutoffBoundsData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData :=
  RegionalVerticalBulkBoundsData.restrict
    (c2BulkConcreteScaledSeededAnalyticTiltBoundsData
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    (c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    (by
      intro s hs
      have h0 := c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_mem_region hs
      have h1 := c2BulkScaledSeededExplicitOddTail_mem_scaled_seeded_analytic_tilt_region h0
      have h2 := c2BulkConcreteScaledSeededAnalyticTilt_mem_region h1
      have h3 := c2BulkConcreteSeededAnalyticTilt_mem_region h2
      have hreg := c2BulkConcreteAnalyticTilt_mem_regularized_region h3
      have hhorizontal := c2BulkConcreteRegularized_mem_regularized_horizontal_region hreg
      simpa [c2BulkConcreteScaledSeededAnalyticTiltBoundsData,
        c2BulkConcreteSeededAnalyticTiltBoundsData,
        c2BulkConcreteAnalyticTiltBoundsData,
        c2BulkConcreteRegularizedBoundsData,
        c2ConcreteOperatorBulkBoundsData,
        c2BulkRegularizedHorizontalBoundsData] using hhorizontal)

noncomputable def c2GenuineBulkScaledSeededExplicitOddTailC0ZetaCutoffBoundsData
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (hmodel : C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    GenuineFInfiniteRegionalBulkBoundsData :=
  GenuineFInfiniteRegionalBulkBoundsData.ofRegionalVerticalBulkBoundsData
    (c2BulkScaledSeededExplicitOddTailC0ZetaCutoffBoundsData
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    (by
      intro s hs
      exact hmodel s hs)

theorem c2GenuineBulkScaledSeededExplicitOddTailC0ZetaCutoff_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hmodel : C2ScaledSeededExplicitOddTailC0ZetaCutoffGenuineIdentity
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact genuineFInfinite_nonvanishing_of_regionalBulkBoundsData
    (c2GenuineBulkScaledSeededExplicitOddTailC0ZetaCutoffBoundsData
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      hmodel)
    hs

noncomputable def c2OddTailGenuineBulkBoundsData_balancingSeed
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    GenuineFInfiniteRegionalBulkBoundsData :=
  c2GenuineBulkScaledSeededExplicitOddTailC0ZetaCutoffBoundsData
    (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
    (c2OddTailGenuineIdentity_balancingSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)

theorem c2OddTailGenuine_nonvanishing_balancingSeed_of_mem
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact c2GenuineBulkScaledSeededExplicitOddTailC0ZetaCutoff_nonvanishing_of_mem
    (c2OddTailGenuineIdentity_balancingSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale)
    hs

/-!
## Scalar reduction of `C2OddTailBalancingSeedScaledBound`

The admissibility obligation for the balancing seed is reduced to three scalar
upper bounds: one on the vertical/rectangular residual (controlled by the
vertical cutoff `K` and the odd cutoff `M`), one on the concrete odd horizontal
defect (controlled by the layer cutoff data `coreCutoff`), and one on the
resolvent gap `‖1 - q s‖`.
-/

/-- Scalar upper bound on the vertical/rectangular residual at `s`. -/
def C2VerticalRectangularResidualBound
    (K M : ℕ) (verticalRectangularUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ ≤
    verticalRectangularUpper s

/-- Scalar upper bound on the concrete odd horizontal defect at `s`. -/
def C2OddHorizontalDefectBound
    (coreCutoff : ℕ → ℕ) (horizontalDefectUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤ horizontalDefectUpper s

/-- Scalar upper bound on the resolvent gap `‖1 - q s‖` at `s`. -/
def C2ResolventGapBound (resolventGapUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖1 - q s‖ ≤ resolventGapUpper s

/-- Combined scalar bound that majorises the seed-norm factor. -/
def C2BalancingSeedFactorScaledBound
    (verticalRectangularUpper horizontalDefectUpper resolventGapUpper
      tiltConstant tiltScale : ℂ → ℝ) (s : ℂ) : Prop :=
  ((verticalRectangularUpper s + horizontalDefectUpper s) *
      resolventGapUpper s) *
    tiltScale s ≤ tiltConstant s

/-- Note-style `C_R / X` upper used to package the combined resolvent defect. -/
noncomputable def c2ResolventNoteUpper
    (resolventConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s => resolventConstant s / cutoffScale s

/--
Concrete `C_R` obtained by matching the horizontal scale with the cutoff scale
`X`: the vertical part contributes `X * continuedVerticalUpper`, while the
horizontal geometric sum contributes `horizontalConstant / (1-r)`.
-/
noncomputable def c2ResolventNoteScaleMatchedConstant
    (continuedVerticalUpper horizontalConstant
      cutoffScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    cutoffScale s * continuedVerticalUpper s +
      horizontalConstant s * (1 - horizontalRatio s)⁻¹

theorem c2ResolventNoteUpper_eq_scaleMatched_of_pos
    {continuedVerticalUpper horizontalConstant
      cutoffScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hcutoffScale_pos : 0 < cutoffScale s) :
    c2ResolventNoteUpper
        (c2ResolventNoteScaleMatchedConstant
          continuedVerticalUpper horizontalConstant cutoffScale horizontalRatio)
        cutoffScale s =
      continuedVerticalUpper s +
        c2HorizontalRegularizedUpper
          horizontalConstant cutoffScale horizontalRatio s := by
  unfold c2ResolventNoteUpper c2ResolventNoteScaleMatchedConstant
    c2HorizontalRegularizedUpper
  field_simp [ne_of_gt hcutoffScale_pos]

theorem C2BalancingSeedFactorScaledBound.of_noteUpper
    {verticalRectangularUpper horizontalDefectUpper resolventGapUpper
      resolventConstant cutoffScale tiltConstant tiltScale : ℂ → ℝ}
    {s : ℂ}
    (hgap_nonneg : 0 ≤ resolventGapUpper s)
    (htilt_nonneg : 0 ≤ tiltScale s)
    (hnote :
      verticalRectangularUpper s + horizontalDefectUpper s ≤
        c2ResolventNoteUpper resolventConstant cutoffScale s)
    (hscaled :
      (c2ResolventNoteUpper resolventConstant cutoffScale s *
          resolventGapUpper s) *
        tiltScale s ≤ tiltConstant s) :
    C2BalancingSeedFactorScaledBound
      verticalRectangularUpper horizontalDefectUpper resolventGapUpper
      tiltConstant tiltScale s := by
  unfold C2BalancingSeedFactorScaledBound
  have hmul :
      (verticalRectangularUpper s + horizontalDefectUpper s) * resolventGapUpper s ≤
        c2ResolventNoteUpper resolventConstant cutoffScale s * resolventGapUpper s := by
    exact mul_le_mul_of_nonneg_right hnote hgap_nonneg
  have hscaled' :
      ((verticalRectangularUpper s + horizontalDefectUpper s) * resolventGapUpper s) *
          tiltScale s ≤
        (c2ResolventNoteUpper resolventConstant cutoffScale s *
            resolventGapUpper s) *
          tiltScale s := by
    exact mul_le_mul_of_nonneg_right hmul htilt_nonneg
  exact le_trans hscaled' hscaled

/--
Reduction lemma: from the three scalar bounds plus a combined scaled bound, we
recover the operational obligation `C2OddTailBalancingSeedScaledBound` used by
the balancing seed admissibility certificate.
-/
theorem c2OddTailBalancingSeed_scaledBound_of_componentBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      verticalRectangularUpper horizontalDefectUpper resolventGapUpper : ℂ → ℝ}
    {s : ℂ}
    (hvert_nonneg : 0 ≤ verticalRectangularUpper s)
    (hgap_nonneg : 0 ≤ resolventGapUpper s)
    (hscale_nonneg : 0 ≤ tiltScale s)
    (hvert : C2VerticalRectangularResidualBound K M verticalRectangularUpper s)
    (hhoriz : C2OddHorizontalDefectBound coreCutoff horizontalDefectUpper s)
    (hgap : C2ResolventGapBound resolventGapUpper s)
    (hcomb : C2BalancingSeedFactorScaledBound
      verticalRectangularUpper horizontalDefectUpper resolventGapUpper
      tiltConstant tiltScale s) :
    C2OddTailBalancingSeedScaledBound
      coreCutoff K M tiltConstant tiltScale s := by
  unfold C2OddTailBalancingSeedScaledBound
  have hsum_nonneg :
      0 ≤ verticalRectangularUpper s + horizontalDefectUpper s :=
    add_nonneg hvert_nonneg
      (le_trans (norm_nonneg _) hhoriz)
  have hsum_le :
      ‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        verticalRectangularUpper s + horizontalDefectUpper s :=
    add_le_add hvert hhoriz
  have hprod_le :
      (‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
          ‖1 - q s‖ ≤
        (verticalRectangularUpper s + horizontalDefectUpper s) *
          resolventGapUpper s := by
    exact mul_le_mul hsum_le hgap (norm_nonneg _) hsum_nonneg
  have hprod_nonneg :
      0 ≤ (verticalRectangularUpper s + horizontalDefectUpper s) *
        resolventGapUpper s :=
    mul_nonneg hsum_nonneg hgap_nonneg
  have hscaled_le :
      ((‖c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s‖ +
            ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
            ‖1 - q s‖) *
          tiltScale s ≤
        ((verticalRectangularUpper s + horizontalDefectUpper s) *
            resolventGapUpper s) *
          tiltScale s :=
    mul_le_mul_of_nonneg_right hprod_le hscale_nonneg
  exact le_trans hscaled_le hcomb

/-!
### Concrete instantiations of the three component bounds

The structural reduction above is now fed by closed-form certificates: a
triangle-inequality bound for the vertical/rectangular residual, a geometric
layer bound for the regularized odd horizontal defect (via the already
formalized `c2HorizontalRegularizedDefect_bound`), and the `1 + ‖q s‖` bound
for the resolvent gap.
-/

/-- Closed-form bound for the resolvent gap: `‖1 - q s‖ ≤ 1 + ‖q s‖`. -/
theorem c2ResolventGapBound_one_add_norm_q (s : ℂ) :
    C2ResolventGapBound (fun s => 1 + ‖q s‖) s := by
  unfold C2ResolventGapBound
  have h := norm_sub_le (1 : ℂ) (q s)
  simpa using h

/--
Triangle-inequality bound for the vertical/rectangular residual:
`‖verticalDepthTailFromTwo + rectangularGenuine - 2·genuineCentralDoubleSeries‖`
is bounded by `‖verticalDepthTailFromTwo‖ + ‖rectangularGenuine‖
+ 2 · ‖genuineCentralDoubleSeries‖`.
-/
theorem c2VerticalRectangularResidualBound_triangle (K M : ℕ) (s : ℂ) :
    C2VerticalRectangularResidualBound K M
      (fun s =>
        ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
          2 * ‖genuineCentralDoubleSeries s‖) s := by
  unfold C2VerticalRectangularResidualBound
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual
  have h₁ :
      ‖verticalDepthTailFromTwo s + rectangularGenuine s K M -
          (2 : ℂ) * genuineCentralDoubleSeries s‖ ≤
        ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ +
          ‖(2 : ℂ) * genuineCentralDoubleSeries s‖ :=
    norm_sub_le _ _
  have h₂ :
      ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ ≤
        ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ :=
    norm_add_le _ _
  have h₃ :
      ‖(2 : ℂ) * genuineCentralDoubleSeries s‖ =
        2 * ‖genuineCentralDoubleSeries s‖ := by
    rw [norm_mul]
    simp
  calc
    ‖verticalDepthTailFromTwo s + rectangularGenuine s K M -
          (2 : ℂ) * genuineCentralDoubleSeries s‖
        ≤ ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ +
            ‖(2 : ℂ) * genuineCentralDoubleSeries s‖ := h₁
    _ ≤ (‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖) +
            ‖(2 : ℂ) * genuineCentralDoubleSeries s‖ := by
              exact add_le_add h₂ le_rfl
    _ = ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
          2 * ‖genuineCentralDoubleSeries s‖ := by rw [h₃]

/-- The `K, M`-independent anchor left after removing the rectangular cutoff error. -/
noncomputable def c2VerticalRectangularAnchorResidual : ℂ → ℂ :=
  fun s => verticalDepthTailFromTwo s - genuineCentralDoubleSeries s

/-- The same anchor rewritten against the `c0 * ζ` target on `Re(s) > 1`. -/
noncomputable def c2VerticalC0ZetaAnchorResidual : ℂ → ℂ :=
  fun s => verticalDepthTailFromTwo s - c0 s * riemannZeta s

/--
Exact split of the vertical/rectangular residual into a fixed vertical anchor and
the rectangular cutoff error against the central infinite target.
-/
theorem c2ScaledSeededExplicitOddTailVerticalRectangularResidual_eq_anchor_add_cutoff
    (K M : ℕ) (s : ℂ) :
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s =
      c2VerticalRectangularAnchorResidual s + c2ConcreteCutoffError K M s := by
  unfold c2ScaledSeededExplicitOddTailVerticalRectangularResidual
    c2VerticalRectangularAnchorResidual c2ConcreteCutoffError
    c2ConcreteCutoffErrorFromTarget c2RectangularGenuineOperator c2AnalyticCentralTarget
  ring

/--
On `Re(s) > 1`, the same split can be written against the `c0 * ζ` cutoff error.
-/
theorem
  c2ScaledSeededExplicitOddTailVerticalRectangularResidual_eq_c0ZetaAnchor_add_cutoff_of_one_lt_re
    (K M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual K M s =
      c2VerticalC0ZetaAnchorResidual s + c2ConcreteCutoffErrorC0Zeta K M s := by
  unfold c2ScaledSeededExplicitOddTailVerticalRectangularResidual
    c2VerticalC0ZetaAnchorResidual c2ConcreteCutoffErrorC0Zeta
    c2ConcreteCutoffErrorFromTarget c2RectangularGenuineOperator
  rw [genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs]
  ring

/--
The `c0 * ζ` vertical anchor factors through the odd Dirichlet channel.
This isolates the non-decaying vertical contribution from the genuine central term.
-/
theorem c2VerticalC0ZetaAnchorResidual_eq_factorized_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    c2VerticalC0ZetaAnchorResidual s =
      verticalDepthTailFromTwo s * (1 - 2 * oddDirichletChannel s) := by
  unfold c2VerticalC0ZetaAnchorResidual
  rw [← genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs,
    genuineCentralDoubleSeries_eq_centralFromOddChannel s hs]
  unfold centralFromOddChannel
  ring

/-- Explicit upper envelope for the `c0 * ζ` vertical anchor residual. -/
noncomputable def c2VerticalC0ZetaAnchorExplicitUpper (s : ℂ) : ℝ :=
  verticalDepthTailUpper s * (1 + 2 * oddDirichletChannelExplicitUpper s)

theorem c2VerticalC0ZetaAnchorResidual_bound_explicit_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    ‖c2VerticalC0ZetaAnchorResidual s‖ ≤ c2VerticalC0ZetaAnchorExplicitUpper s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have htail :
      ‖verticalDepthTailFromTwo s‖ ≤ verticalDepthTailUpper s :=
    verticalDepthTailFromTwo_norm_le_upper_of_re_pos s hs0
  have htail_nonneg : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs0
  have hodd :
      ‖oddDirichletChannel s‖ ≤ oddDirichletChannelExplicitUpper s :=
    oddDirichletChannel_norm_le_explicit_of_one_lt_re s hs
  have hodd_gap :
      ‖1 - (2 : ℂ) * oddDirichletChannel s‖ ≤ 1 + 2 * ‖oddDirichletChannel s‖ := by
    have h := norm_sub_le (1 : ℂ) ((2 : ℂ) * oddDirichletChannel s)
    simpa [norm_mul] using h
  have hodd_gap_explicit :
      1 + 2 * ‖oddDirichletChannel s‖ ≤ 1 + 2 * oddDirichletChannelExplicitUpper s := by
    nlinarith
  calc
    ‖c2VerticalC0ZetaAnchorResidual s‖
      = ‖verticalDepthTailFromTwo s * (1 - 2 * oddDirichletChannel s)‖ := by
          rw [c2VerticalC0ZetaAnchorResidual_eq_factorized_of_one_lt_re s hs]
    _ = ‖verticalDepthTailFromTwo s‖ * ‖1 - 2 * oddDirichletChannel s‖ := by
          rw [norm_mul]
    _ ≤ verticalDepthTailUpper s * ‖1 - 2 * oddDirichletChannel s‖ := by
          exact mul_le_mul_of_nonneg_right htail (norm_nonneg _)
    _ ≤ verticalDepthTailUpper s * (1 + 2 * ‖oddDirichletChannel s‖) := by
          exact mul_le_mul_of_nonneg_left hodd_gap htail_nonneg
    _ ≤ verticalDepthTailUpper s * (1 + 2 * oddDirichletChannelExplicitUpper s) := by
          exact mul_le_mul_of_nonneg_left hodd_gap_explicit htail_nonneg
    _ = c2VerticalC0ZetaAnchorExplicitUpper s := by
          rfl

/--
Refined vertical/rectangular bound: a bound on the fixed `c0 * ζ` anchor together
with a scaled rectangular cutoff bound implies a bound for the full
vertical/rectangular residual.
-/
theorem c2VerticalRectangularResidualBound_of_c0ZetaAnchor_and_cutoffScaled
    {K M : ℕ}
    {verticalAnchorUpper cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : 1 < s.re)
    (hanchor : ‖c2VerticalC0ZetaAnchorResidual s‖ ≤ verticalAnchorUpper s)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled :
      ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s) :
    C2VerticalRectangularResidualBound K M
      (fun s => verticalAnchorUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s) s := by
  unfold C2VerticalRectangularResidualBound
  have hsplit :=
    c2ScaledSeededExplicitOddTailVerticalRectangularResidual_eq_c0ZetaAnchor_add_cutoff_of_one_lt_re
      K M hs
  rw [hsplit]
  have hcutoff :
      ‖c2ConcreteCutoffErrorC0Zeta K M s‖ ≤
        c2CutoffUpperFromScale cutoffConstant cutoffScale s :=
    c2Cutoff_bound_from_scaled hcutoffScale hcutoffScaled
  exact le_trans (norm_add_le _ _) (add_le_add hanchor hcutoff)

/--
Geometric layer bound for the regularized odd horizontal defect: from a per-layer
estimate `‖layer j‖ ≤ (C/X) * r^j` with `0 ≤ r < 1` we obtain
`C2OddHorizontalDefectBound` against `c2HorizontalRegularizedUpper C X r`.
-/
theorem c2OddHorizontalDefectBound_of_layer_geometric
    {coreCutoff : ℕ → ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hscale_pos : 0 < horizontalScale s)
    (hconstant_nonneg : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    C2OddHorizontalDefectBound coreCutoff
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale
        horizontalRatio) s := by
  unfold C2OddHorizontalDefectBound c2ConcreteOddHorizontalDefect
  exact c2HorizontalRegularizedDefect_bound hscale_pos hconstant_nonneg
    hratio_nonneg hratio_lt_one hlayer

/-!
### Component reduction for the continued quartet bulk region

The continued quartet region is reduced to scalar component estimates: a bound
for the continued vertical/rectangular residual, the already regularized
horizontal layer budget, the closed-form resolvent-gap bound, the continued
cutoff bound, and the quartet dominance inequality.
-/

/-- Scalar upper bound on the continued vertical/rectangular residual at `s`. -/
def C2ContinuedVerticalResidualBound
    (K M : ℕ) (continuedVerticalUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ ≤
    continuedVerticalUpper s

theorem c2OddTailContinuedBalancingSeed_norm_le
    (coreCutoff : ℕ → ℕ) (K M : ℕ) (s : ℂ) :
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ ≤
      (‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
        ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
        ‖1 - q s‖ := by
  have hsum :
      ‖-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        ‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ := by
    simpa [sub_eq_add_neg] using
      norm_add_le
        (-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s)
        (-c2ConcreteOddHorizontalDefect coreCutoff s)
  unfold c2OddTailContinuedBalancingSeed
  calc
    ‖(-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s) *
        (1 - q s)‖ =
        ‖-c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s -
          c2ConcreteOddHorizontalDefect coreCutoff s‖ * ‖1 - q s‖ := by
      rw [norm_mul]
    _ ≤
        (‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
          ‖1 - q s‖ := by
      exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

def C2OddTailContinuedBalancingSeedScaledBound
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale : ℂ → ℝ) (s : ℂ) : Prop :=
  ((‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
      ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
      ‖1 - q s‖) *
    tiltScale s ≤ tiltConstant s

theorem c2OddTailContinuedBalancingSeed_scaled_bound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale : ℂ → ℝ} {s : ℂ}
    (hscale_nonneg : 0 ≤ tiltScale s)
    (hbound : C2OddTailContinuedBalancingSeedScaledBound
      coreCutoff K M tiltConstant tiltScale s) :
    ‖c2OddTailContinuedBalancingSeed coreCutoff K M s‖ * tiltScale s ≤
      tiltConstant s := by
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (c2OddTailContinuedBalancingSeed_norm_le coreCutoff K M s)
      hscale_nonneg)
    hbound

theorem c2OddTailContinuedBalancingSeed_scaledBound_of_componentBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      continuedVerticalUpper horizontalDefectUpper resolventGapUpper : ℂ → ℝ}
    {s : ℂ}
    (hvert_nonneg : 0 ≤ continuedVerticalUpper s)
    (hscale_nonneg : 0 ≤ tiltScale s)
    (hvert : C2ContinuedVerticalResidualBound K M continuedVerticalUpper s)
    (hhoriz : C2OddHorizontalDefectBound coreCutoff horizontalDefectUpper s)
    (hgap : C2ResolventGapBound resolventGapUpper s)
    (hcomb : C2BalancingSeedFactorScaledBound
      continuedVerticalUpper horizontalDefectUpper resolventGapUpper
      tiltConstant tiltScale s) :
    C2OddTailContinuedBalancingSeedScaledBound
      coreCutoff K M tiltConstant tiltScale s := by
  unfold C2OddTailContinuedBalancingSeedScaledBound
  have hsum_nonneg :
      0 ≤ continuedVerticalUpper s + horizontalDefectUpper s :=
    add_nonneg hvert_nonneg
      (le_trans (norm_nonneg _) hhoriz)
  have hsum_le :
      ‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        continuedVerticalUpper s + horizontalDefectUpper s :=
    add_le_add hvert hhoriz
  have hprod_le :
      (‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
          ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
          ‖1 - q s‖ ≤
        (continuedVerticalUpper s + horizontalDefectUpper s) *
          resolventGapUpper s := by
    exact mul_le_mul hsum_le hgap (norm_nonneg _) hsum_nonneg
  have hscaled_le :
      ((‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖ +
            ‖c2ConcreteOddHorizontalDefect coreCutoff s‖) *
            ‖1 - q s‖) *
          tiltScale s ≤
        ((continuedVerticalUpper s + horizontalDefectUpper s) *
            resolventGapUpper s) *
          tiltScale s :=
    mul_le_mul_of_nonneg_right hprod_le hscale_nonneg
  exact le_trans hscaled_le hcomb

structure C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  continued_vertical_bound :
    C2ContinuedVerticalResidualBound K M continuedVerticalUpper s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      continuedVerticalUpper
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (continuedVerticalUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetComponentEstimates
    coreCutoff K M continuedVerticalUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M continuedVerticalUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  have hscale_nonneg : 0 ≤ tiltScale s := le_of_lt hs.tiltScale_pos
  have hvert_nonneg : 0 ≤ continuedVerticalUpper s :=
    le_trans (norm_nonneg _) hs.continued_vertical_bound
  have hhorizontal :
      C2OddHorizontalDefectBound coreCutoff
        (c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio) s :=
    c2OddHorizontalDefectBound_of_layer_geometric
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one
      hs.horizontalLayer_bound
  have hgap : C2ResolventGapBound (fun s => 1 + ‖q s‖) s :=
    c2ResolventGapBound_one_add_norm_q s
  have hseed_scaled_bound :
      C2OddTailContinuedBalancingSeedScaledBound
        coreCutoff K M tiltConstant tiltScale s :=
    c2OddTailContinuedBalancingSeed_scaledBound_of_componentBounds
      hvert_nonneg hscale_nonneg
      hs.continued_vertical_bound hhorizontal hgap
      hs.balancing_seed_factor_scaled_bound
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound :=
      c2OddTailContinuedBalancingSeed_scaled_bound
        hscale_nonneg hseed_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetComponentRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {continuedVerticalUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M continuedVerticalUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion hs)

/-- Exact upper envelope for the continued vertical/rectangular residual. -/
noncomputable def c2ContinuedVerticalResidualExactUpper (K M : ℕ) : ℂ → ℝ :=
  fun s => ‖c2ScaledSeededExplicitOddTailContinuedVerticalResidual K M s‖

theorem c2ContinuedVerticalResidualBound_exact (K M : ℕ) (s : ℂ) :
    C2ContinuedVerticalResidualBound K M
      (c2ContinuedVerticalResidualExactUpper K M) s := by
  unfold C2ContinuedVerticalResidualBound c2ContinuedVerticalResidualExactUpper
  exact le_rfl

/-- Exact upper envelope for the continued cutoff error. -/
noncomputable def c2ContinuedCutoffExactUpper (K M : ℕ) : ℂ → ℝ :=
  fun s => ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖

structure C2OddTailContinuedBalancingSeedBulkQuartetExactEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualExactUpper K M)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_exact_scaled_bound :
    c2ContinuedCutoffExactUpper K M s * cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetExactEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_exactRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M (c2ContinuedVerticalResidualExactUpper K M)
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    continued_vertical_bound := c2ContinuedVerticalResidualBound_exact K M s
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := by
      simpa [c2ContinuedCutoffExactUpper] using hs.cutoff_exact_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_exactRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_exactRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetExactRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExactRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_exactRegion hs)

/-!
### Triangle majorants for the continued quartet bulk

These bounds are deliberately available throughout the off-critical strip: they
do not use the Dirichlet-series identity in `Re(s) > 1`. The analytic burden is
therefore pushed to bounding the finite rectangle, the continued central channel,
and the final quartet dominance inequality.
-/

/-- Triangle upper envelope for the continued vertical/rectangular residual. -/
noncomputable def c2ContinuedVerticalResidualTriangleUpper (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    verticalDepthTailUpper s + ‖rectangularGenuine s K M‖ +
      2 * ‖continuedCentralOddChannel s‖

theorem c2ContinuedVerticalResidualBound_triangle (K M : ℕ) (s : ℂ) :
    C2ContinuedVerticalResidualBound K M
      (fun s =>
        ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
          2 * ‖continuedCentralOddChannel s‖) s := by
  unfold C2ContinuedVerticalResidualBound
    c2ScaledSeededExplicitOddTailContinuedVerticalResidual
  have h₁ :
      ‖verticalDepthTailFromTwo s + rectangularGenuine s K M -
          (2 : ℂ) * continuedCentralOddChannel s‖ ≤
        ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ +
          ‖(2 : ℂ) * continuedCentralOddChannel s‖ :=
    norm_sub_le _ _
  have h₂ :
      ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ ≤
        ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ :=
    norm_add_le _ _
  have h₃ :
      ‖(2 : ℂ) * continuedCentralOddChannel s‖ =
        2 * ‖continuedCentralOddChannel s‖ := by
    rw [norm_mul]
    simp
  calc
    ‖verticalDepthTailFromTwo s + rectangularGenuine s K M -
          (2 : ℂ) * continuedCentralOddChannel s‖
        ≤ ‖verticalDepthTailFromTwo s + rectangularGenuine s K M‖ +
            ‖(2 : ℂ) * continuedCentralOddChannel s‖ := h₁
    _ ≤ (‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖) +
            ‖(2 : ℂ) * continuedCentralOddChannel s‖ := by
              exact add_le_add h₂ le_rfl
    _ = ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
          2 * ‖continuedCentralOddChannel s‖ := by rw [h₃]

theorem c2ContinuedVerticalResidualBound_triangleUpper_of_offCritical
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    C2ContinuedVerticalResidualBound K M
      (c2ContinuedVerticalResidualTriangleUpper K M) s := by
  have htri := c2ContinuedVerticalResidualBound_triangle K M s
  have htail := verticalDepthTailFromTwo_norm_le_upper_of_offCriticalStrip s hs
  unfold C2ContinuedVerticalResidualBound c2ContinuedVerticalResidualTriangleUpper at *
  linarith

theorem c2ContinuedVerticalResidualTriangleUpper_nonneg_of_offCritical
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    0 ≤ c2ContinuedVerticalResidualTriangleUpper K M s := by
  have htail_nonneg : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs.1
  unfold c2ContinuedVerticalResidualTriangleUpper
  positivity

/-- Triangle upper envelope for the continued cutoff error. -/
noncomputable def c2ContinuedCutoffTriangleUpper (K M : ℕ) : ℂ → ℝ :=
  fun s => ‖rectangularGenuine s K M‖ + ‖continuedCentralOddChannel s‖

theorem c2ContinuedCutoff_norm_le_triangle (K M : ℕ) (s : ℂ) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      c2ContinuedCutoffTriangleUpper K M s := by
  unfold c2ConcreteCutoffErrorFromTarget c2RectangularGenuineOperator
    c2ContinuedCutoffTriangleUpper
  simpa [sub_eq_add_neg, norm_neg] using
    norm_add_le (rectangularGenuine s K M) (-continuedCentralOddChannel s)

theorem c2ContinuedCutoff_scaled_bound_of_triangle
    {K M : ℕ} {cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hscale_nonneg : 0 ≤ cutoffScale s)
    (hscaled :
      c2ContinuedCutoffTriangleUpper K M s * cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s := by
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (c2ContinuedCutoff_norm_le_triangle K M s) hscale_nonneg)
    hscaled

structure C2OddTailContinuedBalancingSeedBulkQuartetTriangleEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualTriangleUpper K M)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_triangle_scaled_bound :
    c2ContinuedCutoffTriangleUpper K M s * cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetTriangleEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_triangleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M (c2ContinuedVerticalResidualTriangleUpper K M)
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    continued_vertical_bound :=
      c2ContinuedVerticalResidualBound_triangleUpper_of_offCritical K M hs.offCritical
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound :=
      c2ContinuedCutoff_scaled_bound_of_triangle
        (le_of_lt hs.cutoffScale_pos) hs.cutoff_triangle_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_triangleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_triangleRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetTriangleRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetTriangleRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_triangleRegion hs)

/-!
### Separated envelopes for the continued quartet triangle bounds

The raw triangle majorants are now split into a finite rectangular envelope and
a continued-central envelope. This is the interface where sharper finite `K, M`
bounds and local bounds for the continued odd channel can land independently.
-/

def C2RectangularGenuineBound
    (K M : ℕ) (rectangularUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖rectangularGenuine s K M‖ ≤ rectangularUpper s

def C2GenuineCentralBound (centralUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖genuineCentralDoubleSeries s‖ ≤ centralUpper s

def C2ContinuedCentralBound (centralUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖continuedCentralOddChannel s‖ ≤ centralUpper s

/-- Neutral exact upper for the genuine central series. -/
noncomputable def c2GenuineCentralExactUpper : ℂ → ℝ :=
  fun s => ‖genuineCentralDoubleSeries s‖

theorem c2GenuineCentralBound_exact (s : ℂ) :
    C2GenuineCentralBound c2GenuineCentralExactUpper s := by
  unfold C2GenuineCentralBound c2GenuineCentralExactUpper
  exact le_rfl

noncomputable def c2CentralDefectTriangleUpper
    (genuineCentralUpper continuedCentralUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => genuineCentralUpper s + continuedCentralUpper s

theorem c2CentralDefectBound_triangle_of_bounds
    {genuineCentralUpper continuedCentralUpper : ℂ → ℝ} {s : ℂ}
    (hgenuine : C2GenuineCentralBound genuineCentralUpper s)
    (hcontinued : C2ContinuedCentralBound continuedCentralUpper s) :
    ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
      c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper s := by
  unfold C2GenuineCentralBound C2ContinuedCentralBound
    c2CentralDefectTriangleUpper at *
  calc
    ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        ‖genuineCentralDoubleSeries s‖ + ‖continuedCentralOddChannel s‖ :=
      norm_sub_le _ _
    _ ≤ genuineCentralUpper s + continuedCentralUpper s :=
      add_le_add hgenuine hcontinued

noncomputable def c2ContinuedVerticalResidualClosedUpper
    (_K _M : ℕ) (rectangularUpper centralUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => verticalDepthTailUpper s + rectangularUpper s + 2 * centralUpper s

noncomputable def c2ContinuedCutoffClosedUpper
    (_K _M : ℕ) (rectangularUpper centralUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => rectangularUpper s + centralUpper s

theorem c2ContinuedVerticalResidualBound_closedUpper_of_bounds
    {K M : ℕ} {rectangularUpper centralUpper : ℂ → ℝ} {s : ℂ}
    (hs : offCriticalStrip s)
    (hrect : C2RectangularGenuineBound K M rectangularUpper s)
    (hcentral : C2ContinuedCentralBound centralUpper s) :
    C2ContinuedVerticalResidualBound K M
      (c2ContinuedVerticalResidualClosedUpper K M rectangularUpper centralUpper) s := by
  have htri := c2ContinuedVerticalResidualBound_triangleUpper_of_offCritical K M hs
  have hcentral₂ : 2 * ‖continuedCentralOddChannel s‖ ≤ 2 * centralUpper s :=
    mul_le_mul_of_nonneg_left hcentral (by norm_num : (0 : ℝ) ≤ 2)
  unfold C2ContinuedVerticalResidualBound c2ContinuedVerticalResidualTriangleUpper
    c2ContinuedVerticalResidualClosedUpper C2RectangularGenuineBound
    C2ContinuedCentralBound at *
  linarith

theorem c2ContinuedVerticalResidualClosedUpper_nonneg_of_bounds
    {K M : ℕ} {rectangularUpper centralUpper : ℂ → ℝ} {s : ℂ}
    (hs : offCriticalStrip s)
    (hrect : C2RectangularGenuineBound K M rectangularUpper s)
    (hcentral : C2ContinuedCentralBound centralUpper s) :
    0 ≤ c2ContinuedVerticalResidualClosedUpper K M rectangularUpper centralUpper s := by
  have htail_nonneg : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs.1
  have hrect_nonneg : 0 ≤ rectangularUpper s :=
    le_trans (norm_nonneg _) hrect
  have hcentral_nonneg : 0 ≤ centralUpper s :=
    le_trans (norm_nonneg _) hcentral
  unfold c2ContinuedVerticalResidualClosedUpper
  positivity

theorem c2ContinuedCutoff_norm_le_closedUpper_of_bounds
    {K M : ℕ} {rectangularUpper centralUpper : ℂ → ℝ} {s : ℂ}
    (hrect : C2RectangularGenuineBound K M rectangularUpper s)
    (hcentral : C2ContinuedCentralBound centralUpper s) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      c2ContinuedCutoffClosedUpper K M rectangularUpper centralUpper s := by
  have htri := c2ContinuedCutoff_norm_le_triangle K M s
  unfold c2ContinuedCutoffTriangleUpper c2ContinuedCutoffClosedUpper
    C2RectangularGenuineBound C2ContinuedCentralBound at *
  linarith

theorem c2ContinuedCutoff_scaled_bound_of_closedUpper
    {K M : ℕ} {rectangularUpper centralUpper cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hrect : C2RectangularGenuineBound K M rectangularUpper s)
    (hcentral : C2ContinuedCentralBound centralUpper s)
    (hscale_nonneg : 0 ≤ cutoffScale s)
    (hscaled :
      c2ContinuedCutoffClosedUpper K M rectangularUpper centralUpper s *
          cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ *
        cutoffScale s ≤ cutoffConstant s := by
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (c2ContinuedCutoff_norm_le_closedUpper_of_bounds hrect hcentral)
      hscale_nonneg)
    hscaled

structure C2OddTailContinuedBalancingSeedBulkQuartetClosedEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (rectangularUpper centralUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  rectangular_bound : C2RectangularGenuineBound K M rectangularUpper s
  continued_central_bound : C2ContinuedCentralBound centralUpper s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualClosedUpper K M rectangularUpper centralUpper)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ContinuedCutoffClosedUpper K M rectangularUpper centralUpper s *
        cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (rectangularUpper centralUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetClosedEstimates
    coreCutoff K M rectangularUpper centralUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_closedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
      coreCutoff K M rectangularUpper centralUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetComponentRegion
      coreCutoff K M
      (c2ContinuedVerticalResidualClosedUpper K M rectangularUpper centralUpper)
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    continued_vertical_bound :=
      c2ContinuedVerticalResidualBound_closedUpper_of_bounds
        hs.offCritical hs.rectangular_bound hs.continued_central_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound :=
      c2ContinuedCutoff_scaled_bound_of_closedUpper
        hs.rectangular_bound hs.continued_central_bound
        (le_of_lt hs.cutoffScale_pos) hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_closedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
      coreCutoff K M rectangularUpper centralUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_componentRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetComponent_mem_of_closedRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {rectangularUpper centralUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
      coreCutoff K M rectangularUpper centralUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetConcreteRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_closedRegion hs)

/-- Canonical finite bound for `rectangularGenuine` from direct and bracket sums. -/
noncomputable def c2RectangularGenuineDirectBracketUpper (K M : ℕ) : ℂ → ℝ :=
  fun s => ‖rectangularDirect s K M‖ + ‖rectangularBracket s K M‖

/-- Finite triangle upper for the rectangular direct sum. -/
noncomputable def c2RectangularDirectFiniteUpper (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    ∑ k ∈ Finset.Icc 2 K,
      ∑ m ∈ oddCoresUpTo M,
        ‖directPairTerm (complexDirichletCoeff s) k m‖

lemma c2RectangularDirectFiniteUpper_nonneg (K M : ℕ) (s : ℂ) :
    0 ≤ c2RectangularDirectFiniteUpper K M s := by
  unfold c2RectangularDirectFiniteUpper
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem rectangularDirect_norm_le_finiteUpper (s : ℂ) (K M : ℕ) :
    ‖rectangularDirect s K M‖ ≤ c2RectangularDirectFiniteUpper K M s := by
  unfold rectangularDirect c2RectangularDirectFiniteUpper
  calc
    ‖∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          directPairTerm (complexDirichletCoeff s) k m‖
      ≤ ∑ k ∈ Finset.Icc 2 K,
          ‖∑ m ∈ oddCoresUpTo M,
              directPairTerm (complexDirichletCoeff s) k m‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            ‖directPairTerm (complexDirichletCoeff s) k m‖ := by
          refine Finset.sum_le_sum ?_
          intro k _hk
          exact norm_sum_le _ _

/-- Finite triangle upper for the rectangular bracket sum. -/
noncomputable def c2RectangularBracketFiniteUpper (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    ∑ k ∈ Finset.Icc 2 K,
      ∑ m ∈ oddCoresUpTo M,
        ‖bracketTerm (complexDirichletCoeff s) k m‖

lemma c2RectangularBracketFiniteUpper_nonneg (K M : ℕ) (s : ℂ) :
    0 ≤ c2RectangularBracketFiniteUpper K M s := by
  unfold c2RectangularBracketFiniteUpper
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem rectangularBracket_norm_le_finiteUpper (s : ℂ) (K M : ℕ) :
    ‖rectangularBracket s K M‖ ≤ c2RectangularBracketFiniteUpper K M s := by
  unfold rectangularBracket c2RectangularBracketFiniteUpper
  calc
    ‖∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          bracketTerm (complexDirichletCoeff s) k m‖
      ≤ ∑ k ∈ Finset.Icc 2 K,
          ‖∑ m ∈ oddCoresUpTo M,
              bracketTerm (complexDirichletCoeff s) k m‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            ‖bracketTerm (complexDirichletCoeff s) k m‖ := by
          refine Finset.sum_le_sum ?_
          intro k _hk
          exact norm_sum_le _ _

theorem c2RectangularGenuineBound_directBracket (K M : ℕ) (s : ℂ) :
    C2RectangularGenuineBound K M
      (c2RectangularGenuineDirectBracketUpper K M) s := by
  unfold C2RectangularGenuineBound c2RectangularGenuineDirectBracketUpper
    rectangularGenuine
  simpa [sub_eq_add_neg, norm_neg] using
    norm_add_le (rectangularDirect s K M) (-rectangularBracket s K M)

/-- Exact upper envelope for the continued central channel. -/
noncomputable def c2ContinuedCentralExactUpper : ℂ → ℝ :=
  fun s => ‖continuedCentralOddChannel s‖

theorem c2ContinuedCentralBound_exact (s : ℂ) :
    C2ContinuedCentralBound c2ContinuedCentralExactUpper s := by
  unfold C2ContinuedCentralBound c2ContinuedCentralExactUpper
  exact le_rfl

def C2ContinuedOddChannelBound (oddUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖continuedOddDirichletChannel s‖ ≤ oddUpper s

/-- Central-channel upper inherited from a bound on the continued odd channel. -/
noncomputable def c2ContinuedCentralFromOddUpper (oddUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => 2 * verticalDepthTailUpper s * oddUpper s

theorem c2ContinuedCentralBound_of_oddChannelBound
    {oddUpper : ℂ → ℝ} {s : ℂ}
    (hs : offCriticalStrip s)
    (hodd : C2ContinuedOddChannelBound oddUpper s) :
    C2ContinuedCentralBound (c2ContinuedCentralFromOddUpper oddUpper) s := by
  have htail :
      ‖verticalDepthTailFromTwo s‖ ≤ verticalDepthTailUpper s :=
    verticalDepthTailFromTwo_norm_le_upper_of_offCriticalStrip s hs
  have htail_upper_nonneg : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs.1
  have hprod :
      ‖verticalDepthTailFromTwo s‖ * ‖continuedOddDirichletChannel s‖ ≤
        verticalDepthTailUpper s * oddUpper s :=
    mul_le_mul htail hodd (norm_nonneg _) htail_upper_nonneg
  have hprod₂ :
      2 * (‖verticalDepthTailFromTwo s‖ * ‖continuedOddDirichletChannel s‖) ≤
        2 * (verticalDepthTailUpper s * oddUpper s) :=
    mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  unfold C2ContinuedCentralBound c2ContinuedCentralFromOddUpper
    continuedCentralOddChannel centralFromOddChannel
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_ofNat]
  linarith

/--
Canonical closed-layer certificate: the rectangular term is controlled by the
direct/bracket split and the continued-central term by its exact norm.
-/
structure C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ContinuedCutoffClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_canonicalClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
      coreCutoff K M
      (c2RectangularGenuineDirectBracketUpper K M)
      c2ContinuedCentralExactUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    rectangular_bound := c2RectangularGenuineBound_directBracket K M s
    continued_central_bound := c2ContinuedCentralBound_exact s
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_canonicalClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_closedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_canonicalClosedRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_canonicalClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetClosedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_canonicalClosedRegion hs)

/-- Upper bound for the finite rectangular depth factor. -/
def C2RectangularDepthFactorBound
    (K : ℕ) (depthUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖rectangularDepthFactor s K‖ ≤ depthUpper s

/-- Upper bound for the finite rectangular odd core. -/
def C2RectangularOddCoreBound
    (M : ℕ) (coreUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖rectangularOddCoreSum s M‖ ≤ coreUpper s

/-- Rectangular genuine upper inherited from the depth/core factorization. -/
noncomputable def c2RectangularGenuineDepthCoreUpper
    (_K _M : ℕ) (depthUpper coreUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => 2 * depthUpper s * coreUpper s

theorem c2RectangularGenuineBound_depthCore_of_bounds
    {K M : ℕ} {depthUpper coreUpper : ℂ → ℝ} {s : ℂ}
    (hdepth : C2RectangularDepthFactorBound K depthUpper s)
    (hcore : C2RectangularOddCoreBound M coreUpper s) :
    C2RectangularGenuineBound K M
      (c2RectangularGenuineDepthCoreUpper K M depthUpper coreUpper) s := by
  have hdepth_upper_nonneg : 0 ≤ depthUpper s :=
    le_trans (norm_nonneg _) hdepth
  have hprod :
      ‖rectangularDepthFactor s K‖ * ‖rectangularOddCoreSum s M‖ ≤
        depthUpper s * coreUpper s :=
    mul_le_mul hdepth hcore (norm_nonneg _) hdepth_upper_nonneg
  have hprod₂ :
      2 * (‖rectangularDepthFactor s K‖ * ‖rectangularOddCoreSum s M‖) ≤
        2 * (depthUpper s * coreUpper s) :=
    mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  unfold C2RectangularGenuineBound c2RectangularGenuineDepthCoreUpper
  rw [rectangularGenuine_eq_depth_core, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat]
  linarith

/-- Exact depth-factor upper, useful as a neutral producer for the depth/core interface. -/
noncomputable def c2RectangularDepthFactorExactUpper (K : ℕ) : ℂ → ℝ :=
  fun s => ‖rectangularDepthFactor s K‖

theorem c2RectangularDepthFactorBound_exact (K : ℕ) (s : ℂ) :
    C2RectangularDepthFactorBound K (c2RectangularDepthFactorExactUpper K) s := by
  unfold C2RectangularDepthFactorBound c2RectangularDepthFactorExactUpper
  exact le_rfl

/-- Exact odd-core upper, useful as a neutral producer for the depth/core interface. -/
noncomputable def c2RectangularOddCoreExactUpper (M : ℕ) : ℂ → ℝ :=
  fun s => ‖rectangularOddCoreSum s M‖

theorem c2RectangularOddCoreBound_exact (M : ℕ) (s : ℂ) :
    C2RectangularOddCoreBound M (c2RectangularOddCoreExactUpper M) s := by
  unfold C2RectangularOddCoreBound c2RectangularOddCoreExactUpper
  exact le_rfl

def C2OddEulerFactorBound (eulerUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖1 - complexDirichletCoeff s 2‖ ≤ eulerUpper s

def C2RiemannZetaBound (zetaUpper : ℂ → ℝ) (s : ℂ) : Prop :=
  ‖riemannZeta s‖ ≤ zetaUpper s

/-- Neutral pointwise upper for `ζ`, useful on the analytically continued strip. -/
noncomputable def c2RiemannZetaExactUpper : ℂ → ℝ :=
  fun s => ‖riemannZeta s‖

theorem c2RiemannZetaBound_exact (s : ℂ) :
    C2RiemannZetaBound c2RiemannZetaExactUpper s := by
  unfold C2RiemannZetaBound c2RiemannZetaExactUpper
  exact le_rfl

/-- Absolute Dirichlet-series upper for `ζ` on `Re(s) > 1`. -/
noncomputable def c2RiemannZetaOneLtDirichletUpper : ℂ → ℝ :=
  fun s => ∑' n : ℕ, ‖complexDirichletCoeff s (n + 1)‖

lemma summable_positiveDirichletCoeff_norm_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖complexDirichletCoeff s (n + 1)‖ := by
  have hnorm := summable_riemannZetaSummand (s := s) hs
  have htail : Summable fun n : ℕ =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (n + 1)‖ :=
    hnorm.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  exact htail.congr fun n => by
    rw [complexDirichletCoeff_eq_cpow_neg s (by omega : n + 1 ≠ 0)]
    simp [riemannZetaSummandHom, Nat.cast_add, Nat.cast_one]

theorem c2RiemannZetaBound_oneLtDirichletUpper
    {s : ℂ} (hs : 1 < s.re) :
    C2RiemannZetaBound c2RiemannZetaOneLtDirichletUpper s := by
  unfold C2RiemannZetaBound c2RiemannZetaOneLtDirichletUpper
  rw [← positiveDirichletChannel_eq_riemannZeta s hs]
  unfold positiveDirichletChannel
  exact norm_tsum_le_tsum_norm
    (summable_positiveDirichletCoeff_norm_of_one_lt_re s hs)

/-- Continued odd-channel upper obtained from an Euler-factor bound and a zeta bound. -/
noncomputable def c2ContinuedOddFromZetaUpper
    (eulerUpper zetaUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => eulerUpper s * zetaUpper s

theorem c2ContinuedOddChannelBound_of_zetaBound
    {eulerUpper zetaUpper : ℂ → ℝ} {s : ℂ}
    (heuler : C2OddEulerFactorBound eulerUpper s)
    (hzeta : C2RiemannZetaBound zetaUpper s) :
    C2ContinuedOddChannelBound
      (c2ContinuedOddFromZetaUpper eulerUpper zetaUpper) s := by
  have heuler_nonneg : 0 ≤ eulerUpper s :=
    le_trans (norm_nonneg _) heuler
  have hprod :
      ‖1 - complexDirichletCoeff s 2‖ * ‖riemannZeta s‖ ≤
        eulerUpper s * zetaUpper s :=
    mul_le_mul heuler hzeta (norm_nonneg _) heuler_nonneg
  unfold C2ContinuedOddChannelBound c2ContinuedOddFromZetaUpper
    continuedOddDirichletChannel
  rw [norm_mul]
  exact hprod

/-- Canonical triangle upper for the odd Euler factor `1 - 2^{-s}`. -/
noncomputable def c2OddEulerFactorTriangleUpper : ℂ → ℝ :=
  fun s => 1 + ‖complexDirichletCoeff s 2‖

theorem c2OddEulerFactorBound_triangle (s : ℂ) :
    C2OddEulerFactorBound c2OddEulerFactorTriangleUpper s := by
  unfold C2OddEulerFactorBound c2OddEulerFactorTriangleUpper
  have h := norm_sub_le (1 : ℂ) (complexDirichletCoeff s 2)
  simpa using h

structure C2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (depthUpper coreUpper eulerUpper zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  depth_bound : C2RectangularDepthFactorBound K depthUpper s
  core_bound : C2RectangularOddCoreBound M coreUpper s
  euler_factor_bound : C2OddEulerFactorBound eulerUpper s
  zeta_bound : C2RiemannZetaBound zetaUpper s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDepthCoreUpper K M depthUpper coreUpper)
        (c2ContinuedCentralFromOddUpper
          (c2ContinuedOddFromZetaUpper eulerUpper zetaUpper)))
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ContinuedCutoffClosedUpper K M
        (c2RectangularGenuineDepthCoreUpper K M depthUpper coreUpper)
        (c2ContinuedCentralFromOddUpper
          (c2ContinuedOddFromZetaUpper eulerUpper zetaUpper)) s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (depthUpper coreUpper eulerUpper zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreEstimates
    coreCutoff K M depthUpper coreUpper eulerUpper zetaUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_zetaDepthCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper eulerUpper zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
      coreCutoff K M depthUpper coreUpper eulerUpper zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetClosedRegion
      coreCutoff K M
      (c2RectangularGenuineDepthCoreUpper K M depthUpper coreUpper)
      (c2ContinuedCentralFromOddUpper
        (c2ContinuedOddFromZetaUpper eulerUpper zetaUpper))
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    rectangular_bound :=
      c2RectangularGenuineBound_depthCore_of_bounds hs.depth_bound hs.core_bound
    continued_central_bound :=
      c2ContinuedCentralBound_of_oddChannelBound hs.offCritical
        (c2ContinuedOddChannelBound_of_zetaBound
          hs.euler_factor_bound hs.zeta_bound)
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_zetaDepthCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper eulerUpper zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
      coreCutoff K M depthUpper coreUpper eulerUpper zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_closedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_zetaDepthCoreRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_zetaDepthCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {depthUpper coreUpper eulerUpper zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
      coreCutoff K M depthUpper coreUpper eulerUpper zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_quartetClosedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetClosed_mem_of_zetaDepthCoreRegion hs)

/-!
### Concrete operational region for the balancing seed

This region packages the explicit odd-tail horizontal budget together with the
closed-form vertical/resolvent bounds above and a single combined inequality
that certifies the balancing seed in scaled form.
-/

/--
Concrete scalar estimates ensuring that the balancing seed belongs to the final
`c0 * ζ` cutoff bulk region.
-/
structure C2OddTailBalancingSeedConcreteEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (fun s =>
        ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
          2 * ‖genuineCentralDoubleSeries s‖)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_c0Zeta_scaled_bound :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/--
Concrete operational region for the balancing seed, expressed only in terms of
the explicit odd-tail budget, the `c0 * ζ` cutoff estimate, and the closed-form
combined seed inequality.
-/
def c2OddTailBalancingSeedConcreteRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailBalancingSeedConcreteEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_concreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  have hscale_nonneg : 0 ≤ tiltScale s := le_of_lt hs.tiltScale_pos
  have hvert_nonneg :
      0 ≤ ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
        2 * ‖genuineCentralDoubleSeries s‖ := by
    positivity
  have hgap_nonneg : 0 ≤ 1 + ‖q s‖ := by
    positivity
  have hvertical :
      C2VerticalRectangularResidualBound K M
        (fun s =>
          ‖verticalDepthTailFromTwo s‖ + ‖rectangularGenuine s K M‖ +
            2 * ‖genuineCentralDoubleSeries s‖) s :=
    c2VerticalRectangularResidualBound_triangle K M s
  have hlayer :
      ∀ j : ℕ,
        ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
          (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j := by
    exact
      c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
        (coreCutoff := coreCutoff)
        (oddTruncationUpper :=
          fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (s := s)
        (c2ConcreteOddTruncation_bound_of_oddDirichletTailExplicitUpper
          (coreCutoff := coreCutoff)
          (oddTruncationUpper :=
            fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
          hs.one_lt_re
          (by
            intro j
            rfl))
        hs.horizontal_budget
  have hhorizontal :
      C2OddHorizontalDefectBound coreCutoff
        (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio) s :=
    c2OddHorizontalDefectBound_of_layer_geometric
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one hlayer
  have hgap : C2ResolventGapBound (fun s => 1 + ‖q s‖) s :=
    c2ResolventGapBound_one_add_norm_q s
  have hseed_scaled_bound :
      C2OddTailBalancingSeedScaledBound coreCutoff K M tiltConstant tiltScale s :=
    c2OddTailBalancingSeed_scaledBound_of_componentBounds
      hvert_nonneg hgap_nonneg hscale_nonneg
      hvertical hhorizontal hgap hs.balancing_seed_factor_scaled_bound
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound :=
      c2OddTailBalancingSeed_scaled_bound hscale_nonneg hseed_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_c0Zeta_scaled_bound := hs.cutoff_c0Zeta_scaled_bound
    dominance := hs.dominance
  }

theorem c2OddTailBalancingSeed_nonvanishing_of_mem_concreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact c2OddTailGenuine_nonvanishing_balancingSeed_of_mem
    (c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_concreteRegion hs)

/-!
### Refined concrete region using a vertical anchor plus scaled cutoff

The previous concrete region bounds the whole vertical/rectangular residual by a
single triangle inequality. The refined version isolates the `K, M`-independent
vertical anchor and reuses the already available scaled cutoff certificate to
recover the full residual bound.
-/

/--
Concrete scalar estimates for the balancing seed with the vertical contribution
split into a fixed `c0 * ζ` anchor plus a scaled rectangular cutoff term.
-/
structure C2OddTailBalancingSeedRefinedConcreteEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  vertical_anchor_bound :
    ‖c2VerticalC0ZetaAnchorResidual s‖ ≤ verticalAnchorUpper s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (fun s => verticalAnchorUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_c0Zeta_scaled_bound :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

/--
Refined concrete region for the balancing seed using the split
`vertical anchor + scaled cutoff`.
-/
def c2OddTailBalancingSeedRefinedConcreteRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailBalancingSeedRefinedConcreteEstimates
    coreCutoff K M
    verticalAnchorUpper tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_refinedConcreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedRefinedConcreteRegion
      coreCutoff K M
      verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  have hscale_nonneg : 0 ≤ tiltScale s := le_of_lt hs.tiltScale_pos
  have hanchor_nonneg : 0 ≤ verticalAnchorUpper s :=
    le_trans (norm_nonneg _) hs.vertical_anchor_bound
  have hcutoff_constant_nonneg : 0 ≤ cutoffConstant s := by
    exact le_trans
      (mul_nonneg (norm_nonneg _) (le_of_lt hs.cutoffScale_pos))
      hs.cutoff_c0Zeta_scaled_bound
  have hcutoff_upper_nonneg :
      0 ≤ c2CutoffUpperFromScale cutoffConstant cutoffScale s := by
    unfold c2CutoffUpperFromScale
    exact div_nonneg hcutoff_constant_nonneg (le_of_lt hs.cutoffScale_pos)
  have hvert_nonneg :
      0 ≤ verticalAnchorUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s :=
    add_nonneg hanchor_nonneg hcutoff_upper_nonneg
  have hgap_nonneg : 0 ≤ 1 + ‖q s‖ := by
    positivity
  have hvertical :
      C2VerticalRectangularResidualBound K M
        (fun s => verticalAnchorUpper s +
          c2CutoffUpperFromScale cutoffConstant cutoffScale s) s :=
    c2VerticalRectangularResidualBound_of_c0ZetaAnchor_and_cutoffScaled
      hs.one_lt_re hs.vertical_anchor_bound hs.cutoffScale_pos
      hs.cutoff_c0Zeta_scaled_bound
  have hlayer :
      ∀ j : ℕ,
        ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
          (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j := by
    exact
      c2ConcreteOddHorizontalLayer_bound_of_truncation_bound
        (coreCutoff := coreCutoff)
        (oddTruncationUpper :=
          fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (s := s)
        (c2ConcreteOddTruncation_bound_of_oddDirichletTailExplicitUpper
          (coreCutoff := coreCutoff)
          (oddTruncationUpper :=
            fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
          hs.one_lt_re
          (by
            intro j
            rfl))
        hs.horizontal_budget
  have hhorizontal :
      C2OddHorizontalDefectBound coreCutoff
        (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio) s :=
    c2OddHorizontalDefectBound_of_layer_geometric
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one hlayer
  have hgap : C2ResolventGapBound (fun s => 1 + ‖q s‖) s :=
    c2ResolventGapBound_one_add_norm_q s
  have hseed_scaled_bound :
      C2OddTailBalancingSeedScaledBound coreCutoff K M tiltConstant tiltScale s :=
    c2OddTailBalancingSeed_scaledBound_of_componentBounds
      hvert_nonneg hgap_nonneg hscale_nonneg
      hvertical hhorizontal hgap hs.balancing_seed_factor_scaled_bound
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound :=
      c2OddTailBalancingSeed_scaled_bound hscale_nonneg hseed_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_c0Zeta_scaled_bound := hs.cutoff_c0Zeta_scaled_bound
    dominance := hs.dominance
  }

theorem c2OddTailBalancingSeed_nonvanishing_of_mem_refinedConcreteRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedRefinedConcreteRegion
      coreCutoff K M
      verticalAnchorUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact c2OddTailGenuine_nonvanishing_balancingSeed_of_mem
    (c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_refinedConcreteRegion hs)

/-!
### Explicit-anchor specialization of the refined region

The refined region still allowed an abstract upper bound for the fixed vertical
anchor. The following specialization removes that parameter by plugging in the
explicit majorant `c2VerticalC0ZetaAnchorExplicitUpper` obtained above.
-/

structure C2OddTailBalancingSeedExplicitAnchorEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (fun s => c2VerticalC0ZetaAnchorExplicitUpper s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s)
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_c0Zeta_scaled_bound :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2OddTailBalancingSeedExplicitAnchorRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailBalancingSeedExplicitAnchorEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2OddTailBalancingSeedExplicitAnchorRegion_eq_empty
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2OddTailBalancingSeedExplicitAnchorRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale = ∅ := by
  ext s
  constructor
  · intro hs
    simpa using false_of_one_lt_re_offCritical hs.one_lt_re hs.offCritical
  · intro hs
    simp at hs

theorem c2OddTailBalancingSeed_mem_refinedConcreteRegion_of_mem_explicitAnchorRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitAnchorRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailBalancingSeedRefinedConcreteRegion
      coreCutoff K M
      c2VerticalC0ZetaAnchorExplicitUpper tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    vertical_anchor_bound :=
      c2VerticalC0ZetaAnchorResidual_bound_explicit_of_one_lt_re s hs.one_lt_re
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_c0Zeta_scaled_bound := hs.cutoff_c0Zeta_scaled_bound
    dominance := hs.dominance
  }

theorem c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitAnchorRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitAnchorRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_refinedConcreteRegion
    (c2OddTailBalancingSeed_mem_refinedConcreteRegion_of_mem_explicitAnchorRegion hs)

theorem c2OddTailBalancingSeed_nonvanishing_of_mem_explicitAnchorRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailBalancingSeedExplicitAnchorRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    genuineFInfinite s ≠ 0 := by
  exact c2OddTailBalancingSeed_nonvanishing_of_mem_refinedConcreteRegion
    (c2OddTailBalancingSeed_mem_refinedConcreteRegion_of_mem_explicitAnchorRegion hs)

/-!
### Witness-based nonemptiness of the quantitative bulk zone

At this stage the explicit-anchor region still carries the cutoff estimate as an
input hypothesis. The next two lemmas isolate the exact existence statement that
will later be discharged by a concrete `K, M`-dependent cutoff bound: once a
single point satisfies the explicit quantitative estimates, the operational bulk
zone is nonempty and contains a point where `genuineFInfinite` is nonzero.
-/

theorem c2OddTailBalancingSeedExplicitAnchorRegion_nonempty_iff
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    Set.Nonempty
      (c2OddTailBalancingSeedExplicitAnchorRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) ↔
      ∃ s : ℂ,
        C2OddTailBalancingSeedExplicitAnchorEstimates
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  rfl

theorem
  c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion_nonempty_of_nonempty_explicitAnchorRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitAnchorRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    Set.Nonempty
      (c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale) := by
  rcases hnonempty with ⟨s, hs⟩
  exact ⟨s,
    c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitAnchorRegion hs⟩

theorem c2OddTailBalancingSeed_exists_nonvanishing_point_of_nonempty_explicitAnchorRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (hnonempty : Set.Nonempty
      (c2OddTailBalancingSeedExplicitAnchorRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)) :
    ∃ s : ℂ,
      s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
        (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale ∧
      genuineFInfinite s ≠ 0 := by
  rcases hnonempty with ⟨s, hs⟩
  refine ⟨s,
    c2OddTailBalancingSeed_mem_c0ZetaCutoffRegion_of_mem_explicitAnchorRegion hs,
    c2OddTailBalancingSeed_nonvanishing_of_mem_explicitAnchorRegion hs⟩

/-!
### Explicit cutoff envelope decaying in `K` and `M`

The remaining abstract cutoff hypothesis is now reduced to two explicit tails:
the missing vertical geometric tail after depth `K`, and the missing odd-channel
tail after odd cutoff `M`.
-/

/-- Explicit upper bound for the missing vertical depths beyond cutoff `K`. -/
noncomputable def rectangularDepthCutoffUpper (s : ℂ) (K : ℕ) : ℝ :=
  ‖q s‖ ^ (K + 1) / (1 - ‖q s‖)

/-- Explicit upper bound for the finite rectangular depth factor. -/
noncomputable def rectangularDepthFactorExplicitUpper (s : ℂ) (K : ℕ) : ℝ :=
  verticalDepthTailUpper s + rectangularDepthCutoffUpper s K

/-- Explicit decaying upper bound for the rectangular cutoff against `c0 * ζ`. -/
noncomputable def c2ConcreteCutoffErrorC0ZetaExplicitUpper
    (s : ℂ) (K M : ℕ) : ℝ :=
  2 * rectangularDepthFactorExplicitUpper s K *
      oddDirichletTailExplicitUpper s ((M + 1) / 2) +
    2 * rectangularDepthCutoffUpper s K * oddDirichletChannelExplicitUpper s

lemma rectangularDepthCutoffUpper_nonneg_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) :
    0 ≤ rectangularDepthCutoffUpper s K := by
  unfold rectangularDepthCutoffUpper
  have hden : 0 ≤ 1 - ‖q s‖ := by
    have hq_lt_one : ‖q s‖ < 1 := q_norm_lt_one_of_re_pos s hs
    linarith [norm_nonneg (q s)]
  exact div_nonneg (by positivity) hden

lemma rectangularDepthFactorExplicitUpper_nonneg_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) :
    0 ≤ rectangularDepthFactorExplicitUpper s K := by
  unfold rectangularDepthFactorExplicitUpper
  exact add_nonneg
    (verticalDepthTailUpper_nonneg_of_re_pos s hs)
    (rectangularDepthCutoffUpper_nonneg_of_re_pos s K hs)

theorem verticalResolvent_norm_le_upper_of_re_pos
    (s : ℂ) (hs : 0 < s.re) :
    ‖verticalResolvent s‖ ≤ (1 - ‖q s‖)⁻¹ := by
  have hq_nonneg : 0 ≤ ‖q s‖ := norm_nonneg _
  have hq_lt_one : ‖q s‖ < 1 := q_norm_lt_one_of_re_pos s hs
  have hnorm : Summable fun j : ℕ => ‖verticalRatio s ^ j‖ := by
    have hgeom : Summable fun j : ℕ => ‖q s‖ ^ j :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    exact hgeom.congr (by
      intro j
      simp [q, norm_pow])
  rw [← vertical_geometric_tsum_eq_resolvent s hs]
  calc
    ‖∑' j : ℕ, verticalRatio s ^ j‖ ≤ ∑' j : ℕ, ‖verticalRatio s ^ j‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' j : ℕ, ‖q s‖ ^ j := by
      apply tsum_congr
      intro j
      simp [q, norm_pow]
    _ = (1 - ‖q s‖)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one]

theorem rectangularDepthFactor_eq_closed_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) (hK : 2 ≤ K) :
    rectangularDepthFactor s K =
      (verticalRatio s ^ (K + 1) - verticalRatio s ^ 2) /
        (verticalRatio s - 1) := by
  rw [rectangularDepthFactor_eq_kernel_depthFactor s K 0]
  rw [(complexDirichletKernel s K 0).depthFactor_eq_closed hK
    (verticalRatio_ne_one_of_re_pos s hs)]
  unfold FormalDirichletKernel.closedDepthFactor
  simp [complexDirichletKernel, verticalRatio]

theorem rectangularDepthFactor_sub_verticalDepthTailFromTwo_eq_neg_cutoff_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) (hK : 2 ≤ K) :
    rectangularDepthFactor s K - verticalDepthTailFromTwo s =
      -(verticalRatio s ^ (K + 1) * verticalResolvent s) := by
  rw [rectangularDepthFactor_eq_closed_of_re_pos s K hs hK,
    verticalDepthTailFromTwo_eq s hs]
  unfold verticalResolvent
  have hden₁ : verticalRatio s - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (verticalRatio_ne_one_of_re_pos s hs)
  have hden₂ : 1 - verticalRatio s ≠ 0 :=
    verticalResolvent_den_ne_zero_of_re_pos s hs
  field_simp [hden₁, hden₂]
  ring

theorem rectangularDepthFactor_sub_verticalDepthTailFromTwo_norm_le_explicit_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) (hK : 2 ≤ K) :
    ‖rectangularDepthFactor s K - verticalDepthTailFromTwo s‖ ≤
      rectangularDepthCutoffUpper s K := by
  rw [rectangularDepthFactor_sub_verticalDepthTailFromTwo_eq_neg_cutoff_of_re_pos
    s K hs hK, norm_neg, norm_mul]
  calc
    ‖verticalRatio s ^ (K + 1)‖ * ‖verticalResolvent s‖
      ≤ ‖verticalRatio s ^ (K + 1)‖ * (1 - ‖q s‖)⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (verticalResolvent_norm_le_upper_of_re_pos s hs)
            (norm_nonneg _)
    _ = rectangularDepthCutoffUpper s K := by
          unfold rectangularDepthCutoffUpper
          rw [div_eq_mul_inv]
          simp [q, norm_pow]

theorem rectangularDepthFactor_norm_le_explicit_of_re_pos
    (s : ℂ) (K : ℕ) (hs : 0 < s.re) (hK : 2 ≤ K) :
    ‖rectangularDepthFactor s K‖ ≤ rectangularDepthFactorExplicitUpper s K := by
  have hsplit :
      rectangularDepthFactor s K =
        verticalDepthTailFromTwo s +
          (rectangularDepthFactor s K - verticalDepthTailFromTwo s) := by
    ring
  rw [hsplit]
  exact le_trans (norm_add_le _ _)
    (add_le_add
      (verticalDepthTailFromTwo_norm_le_upper_of_re_pos s hs)
      (rectangularDepthFactor_sub_verticalDepthTailFromTwo_norm_le_explicit_of_re_pos
        s K hs hK))

/-- Route-facing depth upper using the explicit vertical cutoff envelope. -/
noncomputable def c2RectangularDepthFactorExplicitUpper (K : ℕ) : ℂ → ℝ :=
  fun s => rectangularDepthFactorExplicitUpper s K

theorem c2RectangularDepthFactorBound_explicit_of_re_pos
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) (hK : 2 ≤ K) :
    C2RectangularDepthFactorBound K
      (c2RectangularDepthFactorExplicitUpper K) s := by
  unfold C2RectangularDepthFactorBound c2RectangularDepthFactorExplicitUpper
  exact rectangularDepthFactor_norm_le_explicit_of_re_pos s K hs hK

theorem c2RectangularDepthFactorBound_explicit_of_offCriticalStrip
    (K : ℕ) {s : ℂ} (hs : offCriticalStrip s) (hK : 2 ≤ K) :
    C2RectangularDepthFactorBound K
      (c2RectangularDepthFactorExplicitUpper K) s :=
  c2RectangularDepthFactorBound_explicit_of_re_pos K hs.1 hK

/-- Universal finite upper for the rectangular odd core. -/
noncomputable def c2RectangularOddCoreFiniteUpper (M : ℕ) : ℂ → ℝ :=
  fun s => ∑ m ∈ oddCoresUpTo M, ‖complexDirichletCoeff s m‖

lemma c2RectangularOddCoreFiniteUpper_nonneg (M : ℕ) (s : ℂ) :
    0 ≤ c2RectangularOddCoreFiniteUpper M s := by
  unfold c2RectangularOddCoreFiniteUpper
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem rectangularOddCoreSum_norm_le_finiteUpper (s : ℂ) (M : ℕ) :
    ‖rectangularOddCoreSum s M‖ ≤ c2RectangularOddCoreFiniteUpper M s := by
  unfold rectangularOddCoreSum c2RectangularOddCoreFiniteUpper
  simpa using
    (norm_sum_le (oddCoresUpTo M) (fun m => complexDirichletCoeff s m))

theorem c2RectangularOddCoreBound_finite (M : ℕ) (s : ℂ) :
    C2RectangularOddCoreBound M
      (c2RectangularOddCoreFiniteUpper M) s := by
  unfold C2RectangularOddCoreBound
  exact rectangularOddCoreSum_norm_le_finiteUpper s M

structure C2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  zeta_bound : C2RiemannZetaBound zetaUpper s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    C2BalancingSeedFactorScaledBound
      (c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDepthCoreUpper K M
          (c2RectangularDepthFactorExplicitUpper K)
          (c2RectangularOddCoreFiniteUpper M))
        (c2ContinuedCentralFromOddUpper
          (c2ContinuedOddFromZetaUpper
            c2OddEulerFactorTriangleUpper zetaUpper)))
      (c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio)
      (fun s => 1 + ‖q s‖)
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ContinuedCutoffClosedUpper K M
        (c2RectangularGenuineDepthCoreUpper K M
          (c2RectangularDepthFactorExplicitUpper K)
          (c2RectangularOddCoreFiniteUpper M))
        (c2ContinuedCentralFromOddUpper
          (c2ContinuedOddFromZetaUpper
            c2OddEulerFactorTriangleUpper zetaUpper)) s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreEstimates
    coreCutoff K M zetaUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCore_mem_of_explicitFiniteCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCoreRegion
      coreCutoff K M
      (c2RectangularDepthFactorExplicitUpper K)
      (c2RectangularOddCoreFiniteUpper M)
      c2OddEulerFactorTriangleUpper zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    depth_bound :=
      c2RectangularDepthFactorBound_explicit_of_offCriticalStrip
        K hs.offCritical hs.two_le_K
    core_bound := c2RectangularOddCoreBound_finite M s
    euler_factor_bound := c2OddEulerFactorBound_triangle s
    zeta_bound := hs.zeta_bound
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitFiniteCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_zetaDepthCoreRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCore_mem_of_explicitFiniteCoreRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitFiniteCoreRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_zetaDepthCoreRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetZetaDepthCore_mem_of_explicitFiniteCoreRegion hs)

/-- Rectangular upper used by the explicit finite-core quartet route. -/
noncomputable def c2ExplicitFiniteCoreRectangularUpper
    (K M : ℕ) : ℂ → ℝ :=
  c2RectangularGenuineDepthCoreUpper K M
    (c2RectangularDepthFactorExplicitUpper K)
    (c2RectangularOddCoreFiniteUpper M)

/-- Continued odd-channel upper used by the explicit finite-core quartet route. -/
noncomputable def c2ExplicitFiniteCoreOddUpper
    (zetaUpper : ℂ → ℝ) : ℂ → ℝ :=
  c2ContinuedOddFromZetaUpper c2OddEulerFactorTriangleUpper zetaUpper

/-- Continued central-channel upper used by the explicit finite-core quartet route. -/
noncomputable def c2ExplicitFiniteCoreCentralUpper
    (zetaUpper : ℂ → ℝ) : ℂ → ℝ :=
  c2ContinuedCentralFromOddUpper (c2ExplicitFiniteCoreOddUpper zetaUpper)

/-- Continued vertical-residual upper used by the explicit finite-core quartet route. -/
noncomputable def c2ExplicitFiniteCoreContinuedVerticalUpper
    (K M : ℕ) (zetaUpper : ℂ → ℝ) : ℂ → ℝ :=
  c2ContinuedVerticalResidualClosedUpper K M
    (c2ExplicitFiniteCoreRectangularUpper K M)
    (c2ExplicitFiniteCoreCentralUpper zetaUpper)

/-- Continued cutoff upper used by the explicit finite-core quartet route. -/
noncomputable def c2ExplicitFiniteCoreContinuedCutoffUpper
    (K M : ℕ) (zetaUpper : ℂ → ℝ) : ℂ → ℝ :=
  c2ContinuedCutoffClosedUpper K M
    (c2ExplicitFiniteCoreRectangularUpper K M)
    (c2ExplicitFiniteCoreCentralUpper zetaUpper)

structure C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  zeta_bound : C2RiemannZetaBound zetaUpper s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    ((c2ExplicitFiniteCoreContinuedVerticalUpper K M zetaUpper s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ExplicitFiniteCoreContinuedCutoffUpper K M zetaUpper s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (zetaUpper : ℂ → ℝ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarEstimates
    coreCutoff K M zetaUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCore_mem_of_explicitScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCoreRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    zeta_bound := hs.zeta_bound
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := by
      simpa [C2BalancingSeedFactorScaledBound,
        c2ExplicitFiniteCoreContinuedVerticalUpper,
        c2ExplicitFiniteCoreRectangularUpper,
        c2ExplicitFiniteCoreCentralUpper,
        c2ExplicitFiniteCoreOddUpper] using
        hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := by
      simpa [c2ExplicitFiniteCoreContinuedCutoffUpper,
        c2ExplicitFiniteCoreRectangularUpper,
        c2ExplicitFiniteCoreCentralUpper,
        c2ExplicitFiniteCoreOddUpper] using
        hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitFiniteCoreRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCore_mem_of_explicitScalarRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {zetaUpper : ℂ → ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
      coreCutoff K M zetaUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitFiniteCoreRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetExplicitFiniteCore_mem_of_explicitScalarRegion hs)

structure C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    ((c2ExplicitFiniteCoreContinuedVerticalUpper K M c2RiemannZetaExactUpper s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ExplicitFiniteCoreContinuedCutoffUpper K M c2RiemannZetaExactUpper s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalar_mem_of_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarRegion
      coreCutoff K M c2RiemannZetaExactUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    zeta_bound := c2RiemannZetaBound_exact s
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalar_mem_of_explicitScalarExactZetaRegion
      hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitScalarRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalar_mem_of_explicitScalarExactZetaRegion
      hs)

/-- Expanded scalar rectangular upper for the exact-zeta route. -/
noncomputable def c2ExplicitFiniteCoreRectangularScalarUpper
    (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    2 * c2RectangularDepthFactorExplicitUpper K s *
      c2RectangularOddCoreFiniteUpper M s

theorem c2ExplicitFiniteCoreRectangularUpper_eq_scalar
    (K M : ℕ) (s : ℂ) :
    c2ExplicitFiniteCoreRectangularUpper K M s =
      c2ExplicitFiniteCoreRectangularScalarUpper K M s := by
  rfl

lemma c2ExplicitFiniteCoreRectangularScalarUpper_nonneg_of_re_pos
    (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ c2ExplicitFiniteCoreRectangularScalarUpper K M s := by
  have hdepth :
      0 ≤ c2RectangularDepthFactorExplicitUpper K s := by
    unfold c2RectangularDepthFactorExplicitUpper
    exact rectangularDepthFactorExplicitUpper_nonneg_of_re_pos s K hs
  have hcore : 0 ≤ c2RectangularOddCoreFiniteUpper M s :=
    c2RectangularOddCoreFiniteUpper_nonneg M s
  unfold c2ExplicitFiniteCoreRectangularScalarUpper
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdepth) hcore

/-- Expanded scalar odd-channel upper for the exact-zeta route. -/
noncomputable def c2ExplicitFiniteCoreOddExactZetaScalarUpper : ℂ → ℝ :=
  fun s => (1 + ‖complexDirichletCoeff s 2‖) * ‖riemannZeta s‖

theorem c2ExplicitFiniteCoreOddUpper_exactZeta_eq_scalar (s : ℂ) :
    c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s =
      c2ExplicitFiniteCoreOddExactZetaScalarUpper s := by
  rfl

lemma c2ExplicitFiniteCoreOddExactZetaScalarUpper_nonneg (s : ℂ) :
    0 ≤ c2ExplicitFiniteCoreOddExactZetaScalarUpper s := by
  unfold c2ExplicitFiniteCoreOddExactZetaScalarUpper
  exact mul_nonneg (by positivity) (norm_nonneg _)

/-- Expanded scalar central-channel upper for the exact-zeta route. -/
noncomputable def c2ExplicitFiniteCoreCentralExactZetaScalarUpper :
    ℂ → ℝ :=
  fun s =>
    2 * verticalDepthTailUpper s *
      c2ExplicitFiniteCoreOddExactZetaScalarUpper s

theorem c2ExplicitFiniteCoreCentralUpper_exactZeta_eq_scalar (s : ℂ) :
    c2ExplicitFiniteCoreCentralUpper c2RiemannZetaExactUpper s =
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  rfl

lemma c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  have htail : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs
  have hodd : 0 ≤ c2ExplicitFiniteCoreOddExactZetaScalarUpper s :=
    c2ExplicitFiniteCoreOddExactZetaScalarUpper_nonneg s
  unfold c2ExplicitFiniteCoreCentralExactZetaScalarUpper
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htail) hodd

/-- Explicit finite/exact-zeta upper for the canonical closed vertical term. -/
noncomputable def c2CanonicalClosedVerticalFiniteExactZetaUpper
    (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    verticalDepthTailUpper s +
      c2RectangularDirectFiniteUpper K M s +
      c2RectangularBracketFiniteUpper K M s +
      2 * c2ExplicitFiniteCoreCentralExactZetaScalarUpper s

lemma c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    c2ContinuedCentralExactUpper s ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  have hodd :
      C2ContinuedOddChannelBound
        (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper) s := by
    simpa [c2ExplicitFiniteCoreOddUpper] using
      (c2ContinuedOddChannelBound_of_zetaBound
        (c2OddEulerFactorBound_triangle s)
        (c2RiemannZetaBound_exact s))
  have hcentral :
      C2ContinuedCentralBound
        (c2ExplicitFiniteCoreCentralUpper c2RiemannZetaExactUpper) s :=
    c2ContinuedCentralBound_of_oddChannelBound hs hodd
  simpa [C2ContinuedCentralBound, c2ContinuedCentralExactUpper,
    c2ExplicitFiniteCoreCentralUpper, c2ExplicitFiniteCoreOddUpper,
    c2ContinuedCentralFromOddUpper, c2ContinuedOddFromZetaUpper,
    c2OddEulerFactorTriangleUpper, c2RiemannZetaExactUpper,
    c2ExplicitFiniteCoreCentralExactZetaScalarUpper,
    c2ExplicitFiniteCoreOddExactZetaScalarUpper] using hcentral

lemma c2GenuineCentralDoubleSeries_norm_le_exactZetaScalar_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    ‖genuineCentralDoubleSeries s‖ ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have htail :
      ‖verticalDepthTailFromTwo s‖ ≤ verticalDepthTailUpper s :=
    verticalDepthTailFromTwo_norm_le_upper_of_re_pos s hs0
  have htail_nonneg : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs0
  have hodd :
      ‖oddDirichletChannel s‖ ≤
        c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s := by
    have hcontinued :
        ‖continuedOddDirichletChannel s‖ ≤
          c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s := by
      simpa [C2ContinuedOddChannelBound, c2ExplicitFiniteCoreOddUpper] using
        (c2ContinuedOddChannelBound_of_zetaBound
          (c2OddEulerFactorBound_triangle s)
          (c2RiemannZetaBound_exact s))
    rw [continuedOddDirichletChannel_eq_oddDirichletChannel_on_oneLtHalfPlane s hs] at hcontinued
    exact hcontinued
  have hprod :
      ‖verticalDepthTailFromTwo s‖ * ‖oddDirichletChannel s‖ ≤
        verticalDepthTailUpper s *
          (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s) := by
    exact mul_le_mul htail hodd (norm_nonneg _) htail_nonneg
  have hprod₂ :
      2 * (‖verticalDepthTailFromTwo s‖ * ‖oddDirichletChannel s‖) ≤
        2 *
          (verticalDepthTailUpper s *
            (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s)) := by
    exact mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  have hprod₂' :
      2 * ‖verticalDepthTailFromTwo s‖ * ‖oddDirichletChannel s‖ ≤
        2 *
          (verticalDepthTailUpper s *
            (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s)) := by
    simpa [mul_assoc] using hprod₂
  rw [genuineCentralDoubleSeries_eq_centralFromOddChannel s hs]
  unfold centralFromOddChannel
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_ofNat]
  calc
    2 * ‖verticalDepthTailFromTwo s‖ * ‖oddDirichletChannel s‖ ≤
        2 *
          (verticalDepthTailUpper s *
            (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper s)) := hprod₂'
    _ = 2 *
          (verticalDepthTailUpper s *
            c2ExplicitFiniteCoreOddExactZetaScalarUpper s) := by
          rw [c2ExplicitFiniteCoreOddUpper_exactZeta_eq_scalar]
    _ = c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
          unfold c2ExplicitFiniteCoreCentralExactZetaScalarUpper
          ring

lemma c2GenuineCentralBound_exactZetaScalar_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    C2GenuineCentralBound c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  unfold C2GenuineCentralBound
  exact c2GenuineCentralDoubleSeries_norm_le_exactZetaScalar_of_one_lt_re hs

/--
Hybrid genuine-central upper: keep the caller-provided upper on `Re(s) ≤ 1`,
and automatically switch to the exact-zeta scalar upper on `Re(s) > 1`.
-/
noncomputable def c2GenuineCentralSplitAtOneUpper
    (genuineCentralUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s => if 1 < s.re then c2ExplicitFiniteCoreCentralExactZetaScalarUpper s
    else genuineCentralUpper s

lemma c2GenuineCentralSplitAtOneUpper_eq_exactZeta_of_one_lt_re
    {genuineCentralUpper : ℂ → ℝ} {s : ℂ} (hs : 1 < s.re) :
    c2GenuineCentralSplitAtOneUpper genuineCentralUpper s =
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
  simp [c2GenuineCentralSplitAtOneUpper, hs]

lemma c2GenuineCentralSplitAtOneUpper_eq_original_of_re_le_one
    {genuineCentralUpper : ℂ → ℝ} {s : ℂ} (hs : s.re ≤ 1) :
    c2GenuineCentralSplitAtOneUpper genuineCentralUpper s =
      genuineCentralUpper s := by
  simp [c2GenuineCentralSplitAtOneUpper, not_lt.mpr hs]

theorem c2GenuineCentralBound_splitAtOne
    {genuineCentralUpper : ℂ → ℝ} {s : ℂ}
    (hcenter : s.re ≤ 1 → C2GenuineCentralBound genuineCentralUpper s) :
    C2GenuineCentralBound (c2GenuineCentralSplitAtOneUpper genuineCentralUpper) s := by
  by_cases hs : 1 < s.re
  · simpa [C2GenuineCentralBound, c2GenuineCentralSplitAtOneUpper, hs] using
      (c2GenuineCentralBound_exactZetaScalar_of_one_lt_re hs)
  · have hle : s.re ≤ 1 := le_of_not_gt hs
    simpa [C2GenuineCentralBound, c2GenuineCentralSplitAtOneUpper, hs] using
      (hcenter hle)

theorem c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper
    {centralDefectUpper genuineCentralUpper : ℂ → ℝ} {s : ℂ}
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hupper :
      s.re ≤ 1 →
        centralDefectUpper s +
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s) :
    c2CentralDefectTriangleUpper
        (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
      2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s := by
  by_cases hs : 1 < s.re
  · unfold c2CentralDefectTriangleUpper
    rw [c2GenuineCentralSplitAtOneUpper_eq_exactZeta_of_one_lt_re
      (genuineCentralUpper := genuineCentralUpper) (s := s) hs] at *
    exact le_of_eq (by
      symm
      rw [two_mul])
  · have hle : s.re ≤ 1 := le_of_not_gt hs
    have hnonneg : 0 ≤ centralDefectUpper s :=
      le_trans (norm_nonneg _) hcentralDefect
    have hexact_le :
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤ genuineCentralUpper s := by
      have hbound := hupper hle
      calc
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
            centralDefectUpper s + c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
              linarith
        _ ≤ genuineCentralUpper s := hbound
    unfold c2CentralDefectTriangleUpper
    rw [c2GenuineCentralSplitAtOneUpper_eq_original_of_re_le_one
      (genuineCentralUpper := genuineCentralUpper) (s := s) hle] at *
    have hsum :
        genuineCentralUpper s + c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s + genuineCentralUpper s :=
      add_le_add le_rfl hexact_le
    exact le_trans hsum (le_of_eq (by
      symm
      rw [two_mul]))

theorem c2CentralDefectTriangleUpper_splitAtOne_le_two_mul_splitAtOneUpper_of_exactZetaLeOne
    {genuineCentralUpper : ℂ → ℝ} {s : ℂ}
    (hexact_le :
      s.re ≤ 1 →
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤ genuineCentralUpper s) :
    c2CentralDefectTriangleUpper
        (c2GenuineCentralSplitAtOneUpper genuineCentralUpper)
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
      2 * c2GenuineCentralSplitAtOneUpper genuineCentralUpper s := by
  by_cases hs : 1 < s.re
  · unfold c2CentralDefectTriangleUpper
    rw [c2GenuineCentralSplitAtOneUpper_eq_exactZeta_of_one_lt_re
      (genuineCentralUpper := genuineCentralUpper) (s := s) hs]
    exact le_of_eq (by
      symm
      rw [two_mul])
  · have hle : s.re ≤ 1 := le_of_not_gt hs
    unfold c2CentralDefectTriangleUpper
    rw [c2GenuineCentralSplitAtOneUpper_eq_original_of_re_le_one
      (genuineCentralUpper := genuineCentralUpper) (s := s) hle]
    have hsum :
        genuineCentralUpper s + c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s + genuineCentralUpper s :=
      add_le_add le_rfl (hexact_le hle)
    exact le_trans hsum (le_of_eq (by
      symm
      rw [two_mul]))

theorem c2CentralDefect_norm_le_splitAtOneUpper_of_exactZetaCentralDefect
    {centralDefectUpper genuineCentralUpper : ℂ → ℝ} {s : ℂ}
    (hs : offCriticalStrip s)
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
        centralDefectUpper s)
    (hupper :
      s.re ≤ 1 →
        centralDefectUpper s +
            c2ExplicitFiniteCoreCentralExactZetaScalarUpper s ≤
          genuineCentralUpper s) :
    ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤
      c2GenuineCentralSplitAtOneUpper genuineCentralUpper s := by
  by_cases hOne : 1 < s.re
  · rw [c2GenuineCentralSplitAtOneUpper_eq_exactZeta_of_one_lt_re
      (genuineCentralUpper := genuineCentralUpper) (s := s) hOne]
    have hEq : genuineCentralDoubleSeries s - continuedCentralOddChannel s = 0 := by
      rw [continuedCentralOddChannel_eq_genuineCentralDoubleSeries_on_oneLtHalfPlane
        s hOne]
      ring
    rw [hEq]
    simpa using
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs.1
  · have hle : s.re ≤ 1 := le_of_not_gt hOne
    rw [c2GenuineCentralSplitAtOneUpper_eq_original_of_re_le_one
      (genuineCentralUpper := genuineCentralUpper) (s := s) hle]
    have hdef_le : centralDefectUpper s ≤ genuineCentralUpper s := by
      have hbound := hupper hle
      have hnonneg : 0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
        c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs.1
      nlinarith
    exact le_trans hcentralDefect hdef_le

theorem c2CanonicalClosedVerticalUpper_le_finiteExactZetaUpper_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s ≤
      c2CanonicalClosedVerticalFiniteExactZetaUpper K M s := by
  have hdirect :
      ‖rectangularDirect s K M‖ ≤ c2RectangularDirectFiniteUpper K M s :=
    rectangularDirect_norm_le_finiteUpper s K M
  have hbracket :
      ‖rectangularBracket s K M‖ ≤ c2RectangularBracketFiniteUpper K M s :=
    rectangularBracket_norm_le_finiteUpper s K M
  have hcentral :
      ‖continuedCentralOddChannel s‖ ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
    simpa [c2ContinuedCentralExactUpper] using
    c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip hs
  have hcentral₂ :
      2 * ‖continuedCentralOddChannel s‖ ≤
        2 * c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
    exact mul_le_mul_of_nonneg_left hcentral (by norm_num : (0 : ℝ) ≤ 2)
  unfold c2ContinuedVerticalResidualClosedUpper
    c2RectangularGenuineDirectBracketUpper c2ContinuedCentralExactUpper
    c2CanonicalClosedVerticalFiniteExactZetaUpper
  linarith

/-- Explicit finite/exact-zeta upper for the canonical closed cutoff term. -/
noncomputable def c2CanonicalClosedCutoffFiniteExactZetaUpper
    (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    c2RectangularDirectFiniteUpper K M s +
      c2RectangularBracketFiniteUpper K M s +
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s

/-- Expanded scalar continued vertical-residual upper for the exact-zeta route. -/
noncomputable def
    c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper
    (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    verticalDepthTailUpper s +
      c2ExplicitFiniteCoreRectangularScalarUpper K M s +
      2 * c2ExplicitFiniteCoreCentralExactZetaScalarUpper s

theorem c2ExplicitFiniteCoreContinuedVerticalUpper_exactZeta_eq_scalar
    (K M : ℕ) (s : ℂ) :
    c2ExplicitFiniteCoreContinuedVerticalUpper
        K M c2RiemannZetaExactUpper s =
      c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s := by
  rfl

lemma
    c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper_nonneg_of_re_pos
    (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s := by
  have htail : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs
  have hrect : 0 ≤ c2ExplicitFiniteCoreRectangularScalarUpper K M s :=
    c2ExplicitFiniteCoreRectangularScalarUpper_nonneg_of_re_pos K M hs
  have hcentral :
      0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
    c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs
  unfold c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper
  exact add_nonneg (add_nonneg htail hrect)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcentral)

/-- Expanded scalar continued cutoff upper for the exact-zeta route. -/
noncomputable def
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper
    (K M : ℕ) : ℂ → ℝ :=
  fun s =>
    c2ExplicitFiniteCoreRectangularScalarUpper K M s +
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper s

theorem c2ExplicitFiniteCoreContinuedCutoffUpper_exactZeta_eq_scalar
    (K M : ℕ) (s : ℂ) :
    c2ExplicitFiniteCoreContinuedCutoffUpper
        K M c2RiemannZetaExactUpper s =
      c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s := by
  rfl

lemma
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper_nonneg_of_re_pos
    (K M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s := by
  have hrect : 0 ≤ c2ExplicitFiniteCoreRectangularScalarUpper K M s :=
    c2ExplicitFiniteCoreRectangularScalarUpper_nonneg_of_re_pos K M hs
  have hcentral :
      0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
    c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs
  unfold c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper
  exact add_nonneg hrect hcentral

theorem c2ContinuedCutoff_norm_le_exactZetaScalar_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hK : 2 ≤ K) (hs : offCriticalStrip s) :
    ‖c2ConcreteCutoffErrorFromTarget continuedCentralOddChannel K M s‖ ≤
      c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s := by
  have hrect :
      C2RectangularGenuineBound K M
        (c2ExplicitFiniteCoreRectangularUpper K M) s := by
    unfold c2ExplicitFiniteCoreRectangularUpper
    exact c2RectangularGenuineBound_depthCore_of_bounds
      (c2RectangularDepthFactorBound_explicit_of_offCriticalStrip K hs hK)
      (c2RectangularOddCoreBound_finite M s)
  have hodd :
      C2ContinuedOddChannelBound
        (c2ExplicitFiniteCoreOddUpper c2RiemannZetaExactUpper) s := by
    simpa [c2ExplicitFiniteCoreOddUpper] using
      (c2ContinuedOddChannelBound_of_zetaBound
        (c2OddEulerFactorBound_triangle s)
        (c2RiemannZetaBound_exact s))
  have hcentral :
      C2ContinuedCentralBound
        (c2ExplicitFiniteCoreCentralUpper c2RiemannZetaExactUpper) s :=
    c2ContinuedCentralBound_of_oddChannelBound hs hodd
  simpa [c2ExplicitFiniteCoreContinuedCutoffUpper_exactZeta_eq_scalar] using
    (c2ContinuedCutoff_norm_le_closedUpper_of_bounds hrect hcentral)

structure C2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    ((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s *
      cutoffScale s ≤ cutoffConstant s
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem
    c2ExpandedExactZeta_mem_explicitScalarExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := by
      simpa [
        c2ExplicitFiniteCoreContinuedVerticalUpper_exactZeta_eq_scalar]
        using hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := by
      simpa [
        c2ExplicitFiniteCoreContinuedCutoffUpper_exactZeta_eq_scalar]
        using hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2ExplicitScalarExactZeta_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := by
      simpa [c2ExplicitFiniteCoreContinuedVerticalUpper_exactZeta_eq_scalar]
        using hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := by
      simpa [c2ExplicitFiniteCoreContinuedCutoffUpper_exactZeta_eq_scalar]
        using hs.cutoff_closed_scaled_bound
    quartet_dominance := hs.quartet_dominance
  }

theorem c2ExplicitScalarExactZetaRegion_eq_expandedExactZetaRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2OddTailContinuedBalancingSeedBulkQuartetExplicitScalarExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale =
      c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale := by
  ext s
  constructor
  · exact c2ExplicitScalarExactZeta_mem_expandedExactZetaRegion
  · exact c2ExpandedExactZeta_mem_explicitScalarExactZetaRegion

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_explicitScalarExactZetaRegion
    (c2ExpandedExactZeta_mem_explicitScalarExactZetaRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_explicitScalarExactZetaRegion
    (c2ExpandedExactZeta_mem_explicitScalarExactZetaRegion hs)

/-- Quartet structural upper used by the expanded exact-zeta route. -/
noncomputable def c2ExpandedQuartetGUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) :
    ℂ → ℝ :=
  c2QuartetBulkGUpper
    (c2BulkGUpper
      (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
      (c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio))

/-- Quartet external upper used by the expanded exact-zeta route. -/
noncomputable def c2ExpandedQuartetEUpper
    (cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  c2BulkEUpper (c2CutoffUpperFromScale cutoffConstant cutoffScale)

/-- Full left side of the quartet dominance inequality. -/
noncomputable def c2ExpandedQuartetLeftUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2ExpandedQuartetGUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio s +
      c2ExpandedQuartetEUpper cutoffConstant cutoffScale s

/-- Expanded quartet left side written as the explicit four-term budget. -/
noncomputable def c2ExpandedQuartetFourTermUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2QuartetVerticalTailUpper s +
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s +
      c2CutoffUpperFromScale cutoffConstant cutoffScale s

/-- Expanded quartet upper after peeling off the exact quartet tail. -/
noncomputable def c2ExpandedQuartetResidualUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s +
      c2CutoffUpperFromScale cutoffConstant cutoffScale s

theorem c2ExpandedQuartetFourTermUpper_eq_tail_add_residualUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) :
    c2ExpandedQuartetFourTermUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s =
      c2QuartetVerticalTailUpper s +
        c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
  simp [c2ExpandedQuartetFourTermUpper, c2ExpandedQuartetResidualUpper, add_assoc]

theorem c2ExpandedQuartetLeftUpper_eq_fourTermUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) :
    c2ExpandedQuartetLeftUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s =
      c2ExpandedQuartetFourTermUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s := by
  simp [c2ExpandedQuartetLeftUpper, c2ExpandedQuartetFourTermUpper,
    c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
    c2QuartetBulkGUpper, c2BulkGUpper, c2BulkEUpper, add_left_comm,
    add_comm]

/-- Right side margin of the quartet dominance inequality. -/
noncomputable def c2ExpandedQuartetK2Margin : ℂ → ℝ :=
  fun s =>
    c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

/-- Quartet margin left after reserving the exact quartet tail. -/
noncomputable def c2ExpandedQuartetResidualMargin : ℂ → ℝ :=
  fun s => c2ExpandedQuartetK2Margin s - c2QuartetVerticalTailUpper s

/--
Explicit reserve lost when passing from the analytic allowance to the quartet
residual margin.
-/
noncomputable def c2ExpandedQuartetResidualReserve : ℂ → ℝ :=
  fun s => 2 * ‖q s‖ ^ 6 / (1 - ‖q s‖ ^ 2)

lemma c2ExpandedQuartetK2Margin_nonneg_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    0 ≤ c2ExpandedQuartetK2Margin s := by
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hk2 : 0 ≤ c2QuartetBulkK2Lower s := by
    unfold c2QuartetBulkK2Lower
    positivity
  have hgap : 0 ≤ 1 - ‖q s‖ := by
    linarith [norm_nonneg (q s), hq_lt]
  have hquad : 0 ≤ 1 + ‖q s‖ ^ 2 := by
    positivity
  unfold c2ExpandedQuartetK2Margin
  exact mul_nonneg hk2 (mul_nonneg hgap hquad)

theorem c2ExpandedQuartetResidualMargin_eq_analyticBulkAllowance_sub_reserve_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    c2ExpandedQuartetResidualMargin s =
      c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s := by
  have hq_nonneg : 0 ≤ ‖q s‖ := norm_nonneg _
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hq_sq_lt : ‖q s‖ ^ 2 < 1 := by
    nlinarith
  have hden₁ : 1 - ‖q s‖ ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hq_lt))
  have hden₂ : 1 + ‖q s‖ ≠ 0 := by
    have hpos : 0 < 1 + ‖q s‖ := by
      linarith
    exact ne_of_gt hpos
  have hden₃ : 1 - ‖q s‖ ^ 2 ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hq_sq_lt))
  unfold c2ExpandedQuartetResidualMargin c2ExpandedQuartetK2Margin
    c2AnalyticBulkAllowance c2ExpandedQuartetResidualReserve
    c2QuartetBulkK2Lower c2QuartetVerticalTailUpper
  field_simp [hden₁, hden₂, hden₃]
  ring

def C2ExpandedQuartetDominance
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) (s : ℂ) : Prop :=
  c2ExpandedQuartetLeftUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s <
    c2ExpandedQuartetK2Margin s

theorem c2ExpandedQuartetDominance_of_fourTermBound
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hdom : c2ExpandedQuartetFourTermUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s <
        c2ExpandedQuartetK2Margin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  rw [C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper_eq_fourTermUpper]
  exact hdom

theorem c2ExpandedQuartetDominance_of_budgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {quartetTailBudget tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (hquartetTail : c2QuartetVerticalTailUpper s ≤ quartetTailBudget)
    (htilt : c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : quartetTailBudget + tiltBudget + horizontalBudget + cutoffBudget <
      c2ExpandedQuartetK2Margin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  apply c2ExpandedQuartetDominance_of_fourTermBound
  have hsum₁ :
      c2QuartetVerticalTailUpper s +
          c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤
        quartetTailBudget + tiltBudget :=
    add_le_add hquartetTail htilt
  have hsum₂ :
      c2QuartetVerticalTailUpper s +
          c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s ≤
        quartetTailBudget + tiltBudget + horizontalBudget :=
    add_le_add hsum₁ hhorizontal
  have hsum₃ :
      c2QuartetVerticalTailUpper s +
          c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s +
          c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤
        quartetTailBudget + tiltBudget + horizontalBudget + cutoffBudget :=
    add_le_add hsum₂ hcutoff
  exact lt_of_le_of_lt hsum₃ hdom

/--
Finite resolvent non-cancellation criterion from `notas/teorema_resolvent_non_cancellation.md`, expressed in
the quartet/tail/tilt/horizontal/cutoff budget interface used by the Lean bulk route.
-/
theorem c2ResolventNonCancellationFiniteCriterion_of_budgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {quartetTailBudget tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (hquartetTail : c2QuartetVerticalTailUpper s ≤ quartetTailBudget)
    (htilt : c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : quartetTailBudget + tiltBudget + horizontalBudget + cutoffBudget <
      c2ExpandedQuartetK2Margin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  c2ExpandedQuartetDominance_of_budgetBounds
    hquartetTail htilt hhorizontal hcutoff hdom

theorem c2ExpandedQuartetDominance_of_residualBound
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hdom : c2ExpandedQuartetResidualUpper
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s <
        c2ExpandedQuartetResidualMargin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  apply c2ExpandedQuartetDominance_of_fourTermBound
  rw [c2ExpandedQuartetResidualMargin] at hdom
  rw [c2ExpandedQuartetFourTermUpper_eq_tail_add_residualUpper]
  linarith

theorem c2ExpandedQuartetDominance_of_residualBudgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (htilt : c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : tiltBudget + horizontalBudget + cutoffBudget <
      c2ExpandedQuartetResidualMargin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s := by
  apply c2ExpandedQuartetDominance_of_residualBound
  have hsum₁ :
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s ≤
        tiltBudget + horizontalBudget :=
    add_le_add htilt hhorizontal
  have hsum₂ :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s ≤
        tiltBudget + horizontalBudget + cutoffBudget := by
    simpa [c2ExpandedQuartetResidualUpper, add_assoc] using add_le_add hsum₁ hcutoff
  exact lt_of_le_of_lt hsum₂ hdom

/--
Adjusted resolvent non-cancellation criterion from `notas/teorema_resolvent_non_cancellation.md`, after peeling off
the exact quartet tail and keeping only the residual tilt/horizontal/cutoff budgets.
-/
theorem c2ResolventNonCancellationAdjustedCriterion_of_residualBudgetBounds
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {tiltBudget horizontalBudget cutoffBudget : ℝ}
    {s : ℂ}
    (htilt : c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s ≤ tiltBudget)
    (hhorizontal : c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s ≤ horizontalBudget)
    (hcutoff : c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤ cutoffBudget)
    (hdom : tiltBudget + horizontalBudget + cutoffBudget <
      c2ExpandedQuartetResidualMargin s) :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s :=
  c2ExpandedQuartetDominance_of_residualBudgetBounds
    htilt hhorizontal hcutoff hdom

/--
Abstract finite resolvent non-cancellation criterion from `notas/teorema_resolvent_non_cancellation.md`:
if a quartet lower bound beats tail plus cutoff proxy, then the limiting object is
nonzero.
-/
theorem c2ResolventNonCancellationFiniteCriterion_of_splitBounds
    {FInfinity FX quartet tail : ℂ → ℂ}
    {quartetLower tailBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hsplit : FX s = quartet s + tail s)
    (hquartet : quartetLower s ≤ ‖quartet s‖)
    (htail : ‖tail s‖ ≤ tailBudget s)
    (hproxy : ‖FInfinity s - FX s‖ ≤ cutoffProxy s)
    (hdom : quartetLower s - tailBudget s - cutoffProxy s > 0) :
    FInfinity s ≠ 0 := by
  have hquartet_le : quartetLower s ≤ ‖FX s‖ + tailBudget s := by
    calc
      quartetLower s ≤ ‖quartet s‖ := hquartet
      _ ≤ ‖FX s‖ + ‖tail s‖ := by
        simpa [hsplit, add_assoc, add_left_comm, add_comm] using
          (norm_add_le (FX s) (-tail s))
      _ ≤ ‖FX s‖ + tailBudget s := by
        exact add_le_add le_rfl htail
  have hfx_gt : cutoffProxy s < ‖FX s‖ := by
    linarith
  intro hzero
  have hfx_le : ‖FX s‖ ≤ cutoffProxy s := by
    simpa [hzero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hproxy
  linarith

/--
Abstract adjusted resolvent non-cancellation criterion from `notas/teorema_resolvent_non_cancellation.md`:
the quantity `quartetMain - adjustmentDefect` is the lower bound coming from the
adjusted quartet `|A(s) P₄(β(s))| - Σ |Eⱼ(s)|`.
-/
theorem c2ResolventNonCancellationAdjustedCriterion_of_adjustedQuartetBounds
    {FInfinity FX quartet tail : ℂ → ℂ}
    {quartetMain adjustmentDefect tailBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hsplit : FX s = quartet s + tail s)
    (hquartet : quartetMain s - adjustmentDefect s ≤ ‖quartet s‖)
    (htail : ‖tail s‖ ≤ tailBudget s)
    (hproxy : ‖FInfinity s - FX s‖ ≤ cutoffProxy s)
    (hdom : quartetMain s - adjustmentDefect s - tailBudget s - cutoffProxy s > 0) :
    FInfinity s ≠ 0 := by
  exact c2ResolventNonCancellationFiniteCriterion_of_splitBounds
    (quartetLower := fun z => quartetMain z - adjustmentDefect z)
    hsplit hquartet htail hproxy hdom

/--
Pointwise lower bound from the adjusted quartet representation in
`notas/teorema_resolvent_non_cancellation.md`.
-/
theorem c2ResolventNonCancellationAdjustedQuartetLowerBound_of_errorSplit
    {quartet A beta E0 E1 E2 E3 : ℂ}
    (hrep : quartet =
      (A + E0) + (A * beta + E1) + (A * beta ^ 2 + E2) + (A * beta ^ 3 + E3)) :
    ‖A * verticalQuartetPrefix beta‖ - (‖E0‖ + ‖E1‖ + ‖E2‖ + ‖E3‖) ≤ ‖quartet‖ := by
  have hrepr :
      quartet = A * verticalQuartetPrefix beta + (E0 + E1 + E2 + E3) := by
    rw [hrep]
    unfold verticalQuartetPrefix
    ring
  have hmain :
      ‖A * verticalQuartetPrefix beta‖ ≤ ‖quartet‖ + ‖E0 + E1 + E2 + E3‖ := by
    have hsub :
        A * verticalQuartetPrefix beta = quartet - (E0 + E1 + E2 + E3) := by
      rw [hrep]
      unfold verticalQuartetPrefix
      ring
    rw [hsub]
    exact norm_sub_le _ _
  have herr₀₁₂ : ‖E0 + E1 + E2‖ ≤ ‖E0‖ + ‖E1‖ + ‖E2‖ := by
    calc
      ‖E0 + E1 + E2‖ = ‖(E0 + E1) + E2‖ := by simp [add_assoc]
      _ ≤ ‖E0 + E1‖ + ‖E2‖ := norm_add_le _ _
      _ ≤ (‖E0‖ + ‖E1‖) + ‖E2‖ := by
        linarith [norm_add_le E0 E1]
  have herr : ‖E0 + E1 + E2 + E3‖ ≤ ‖E0‖ + ‖E1‖ + ‖E2‖ + ‖E3‖ := by
    calc
      ‖E0 + E1 + E2 + E3‖ = ‖(E0 + E1 + E2) + E3‖ := by simp [add_assoc]
      _ ≤ ‖E0 + E1 + E2‖ + ‖E3‖ := norm_add_le _ _
      _ ≤ (‖E0‖ + ‖E1‖ + ‖E2‖) + ‖E3‖ := by
        linarith
  linarith

/--
Adjusted resolvent non-cancellation criterion directly from the pointwise representation
`F_{2+j,X}(s) = A(s) β(s)^j + Eⱼ(s)`.
-/
theorem c2ResolventNonCancellationAdjustedCriterion_of_errorSplit
    {FInfinity FX quartet tail A beta E0 E1 E2 E3 : ℂ → ℂ}
    {tailBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hsplit : FX s = quartet s + tail s)
    (hrep : quartet s =
      (A s + E0 s) + (A s * beta s + E1 s) +
        (A s * beta s ^ 2 + E2 s) + (A s * beta s ^ 3 + E3 s))
    (htail : ‖tail s‖ ≤ tailBudget s)
    (hproxy : ‖FInfinity s - FX s‖ ≤ cutoffProxy s)
    (hdom :
      ‖A s * verticalQuartetPrefix (beta s)‖ -
        (‖E0 s‖ + ‖E1 s‖ + ‖E2 s‖ + ‖E3 s‖) -
        tailBudget s - cutoffProxy s > 0) :
    FInfinity s ≠ 0 := by
  exact c2ResolventNonCancellationAdjustedCriterion_of_adjustedQuartetBounds
    (quartetMain := fun z => ‖A z * verticalQuartetPrefix (beta z)‖)
    (adjustmentDefect := fun z => ‖E0 z‖ + ‖E1 z‖ + ‖E2 z‖ + ‖E3 z‖)
    hsplit
    (c2ResolventNonCancellationAdjustedQuartetLowerBound_of_errorSplit hrep)
    htail hproxy hdom

theorem c2ConcreteResolventNonCancellationAdjustedQuartetLowerBound
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ) (s : ℂ) :
    c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s ≤
      ‖c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s‖ := by
  simpa [c2ConcreteResolventNonCancellationAdjustedMain, c2ConcreteResolventNonCancellationAdjustedDefect] using
    (c2ResolventNonCancellationAdjustedQuartetLowerBound_of_errorSplit
      (quartet := c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff s)
      (A := c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed s)
      (beta := c2ConcreteResolventNonCancellationAdjustedRatio s)
      (E0 := c2ConcreteResolventNonCancellationAdjustedError0 coreCutoff s)
      (E1 := c2ConcreteResolventNonCancellationAdjustedError1 coreCutoff s)
      (E2 := c2ConcreteResolventNonCancellationAdjustedError2 coreCutoff s)
      (E3 := c2ConcreteResolventNonCancellationAdjustedError3 coreCutoff s)
      (c2ConcreteResolventNonCancellationAdjustedQuartet_eq_errorSplit tiltSeed coreCutoff s))

theorem c2ConcreteResolventNonCancellationHorizontalTail_norm_le_upper_of_geometric
    {coreCutoff : ℕ → ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_nonneg : 0 ≤ horizontalRatio s)
    (hratio_lt_one : horizontalRatio s < 1)
    (hlayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    ‖c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s‖ ≤
      c2ConcreteResolventNonCancellationHorizontalTailUpper
        horizontalConstant horizontalScale horizontalRatio s := by
  have hnorm : Summable fun j : ℕ => ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ :=
    summable_norm_horizontalLayerDefect_of_geometric
      hscale hconstant hratio_nonneg hratio_lt_one hlayer
  have htail :
      ‖c2HorizontalTail (c2ConcreteOddHorizontalLayerDefect coreCutoff) s 4‖ ≤
        c2HorizontalTailUpper (c2ConcreteOddHorizontalLayerDefect coreCutoff) s 4 :=
    c2HorizontalTail_norm_le_upper hnorm 4
  have hupper :
      c2ConcreteHorizontalTailUpper
          (c2ConcreteOddHorizontalLayerDefect coreCutoff) (fun _ => 4) s ≤
        c2ConcreteResolventNonCancellationHorizontalTailUpper
          horizontalConstant horizontalScale horizontalRatio s := by
    simpa [c2ConcreteResolventNonCancellationHorizontalTailUpper] using
      (c2ConcreteHorizontalTailUpper_le_geometric
        (horizontalLayerDefect := c2ConcreteOddHorizontalLayerDefect coreCutoff)
        (horizontalCutoff := fun _ => 4)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (s := s)
        hscale hconstant hratio_nonneg hratio_lt_one hlayer)
  have htail' :
      ‖c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s‖ ≤
        c2ConcreteHorizontalTailUpper
          (c2ConcreteOddHorizontalLayerDefect coreCutoff) (fun _ => 4) s := by
    simpa [c2ConcreteResolventNonCancellationHorizontalTail, c2ConcreteHorizontalTailUpper] using htail
  exact le_trans htail' hupper

/-- Explicit upper bound for the full adjusted tail in the seeded concrete package. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedTailUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffBudget : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2QuartetVerticalTailUpper s +
      c2TiltAnalyticTailGeometricUpper tiltConstant tiltScale (fun _ => 4) s +
      c2ConcreteResolventNonCancellationHorizontalTailUpper
        horizontalConstant horizontalScale horizontalRatio s +
      cutoffBudget s

theorem c2ConcreteResolventNonCancellationAdjustedTail_norm_le_upper_of_bounds
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffBudget : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ ≤ cutoffBudget s) :
    ‖c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s‖ ≤
      c2ConcreteResolventNonCancellationAdjustedTailUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffBudget s := by
  have hs : 0 < s.re := hoff.1
  have htiltNorm : Summable fun j : ℕ => ‖c2SeededTiltLayerResidual tiltSeed s j‖ :=
    summable_norm_tiltLayerResidual_of_geometric
      htiltScale htiltConstant_nonneg
      (c2TiltAnalyticRatio_nonneg s)
      (c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hoff)
      (c2SeededTiltLayerResidual_bound
        (tiltConstant := tiltConstant)
        (tiltScale := tiltScale)
        (s := s)
        hseed)
  have hhorizontalSummable :
      Summable fun j : ℕ => c2ConcreteOddHorizontalLayerDefect coreCutoff s j :=
    summable_horizontalLayerDefect_of_geometric
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one hhorizontalLayer
  have htiltTailNorm :
      ‖c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s‖ ≤
        c2ConcreteTiltTailUpper (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s := by
    unfold c2ConcreteTiltTailError c2ConcreteTiltTailUpper
    exact c2TiltTruncationError_norm_le_tailUpper_of_summable
      (summable_c2SeededTiltLayerResidual_of_re_pos tiltSeed hs) htiltNorm 4
  have htiltTailUpper :
      c2ConcreteTiltTailUpper (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s ≤
        c2TiltAnalyticTailGeometricUpper tiltConstant tiltScale (fun _ => 4) s := by
    exact c2ConcreteTiltTailUpper_le_analytic_geometric
      hoff htiltScale htiltConstant_nonneg
      (c2SeededTiltLayerResidual_bound
        (tiltConstant := tiltConstant)
        (tiltScale := tiltScale)
        (s := s)
        hseed)
  have hhorizontalTail :
      ‖c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s‖ ≤
        c2ConcreteResolventNonCancellationHorizontalTailUpper
          horizontalConstant horizontalScale horizontalRatio s :=
    c2ConcreteResolventNonCancellationHorizontalTail_norm_le_upper_of_geometric
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one hhorizontalLayer
  rw [c2ConcreteResolventNonCancellationAdjustedTail_eq_expanded_of_re_pos
    tiltSeed coreCutoff K M hs hhorizontalSummable]
  calc
    ‖c2QuartetVerticalTail s +
        c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
        c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
        c2ConcreteCutoffError K M s‖
      ≤ ‖c2QuartetVerticalTail s‖ +
          ‖c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
            c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
            c2ConcreteCutoffError K M s‖ := by
          simpa [add_assoc] using
            (norm_add_le
              (c2QuartetVerticalTail s)
              (c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
                c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
                c2ConcreteCutoffError K M s))
    _ ≤ ‖c2QuartetVerticalTail s‖ +
          (‖c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s‖ +
            ‖c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
              c2ConcreteCutoffError K M s‖) := by
          gcongr
          simpa [add_assoc] using
            (norm_add_le
              (c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s)
              (c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s +
                c2ConcreteCutoffError K M s))
    _ ≤ ‖c2QuartetVerticalTail s‖ +
          (‖c2ConcreteTiltTailError (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s‖ +
            (‖c2ConcreteResolventNonCancellationHorizontalTail coreCutoff s‖ +
              ‖c2ConcreteCutoffError K M s‖)) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ c2QuartetVerticalTailUpper s +
          (c2ConcreteTiltTailUpper (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s +
            (c2ConcreteResolventNonCancellationHorizontalTailUpper
              horizontalConstant horizontalScale horizontalRatio s + cutoffBudget s)) := by
          gcongr
          exact c2QuartetVerticalTail_norm_le_upper_of_re_pos s hs
    _ ≤ c2QuartetVerticalTailUpper s +
          (c2TiltAnalyticTailGeometricUpper tiltConstant tiltScale (fun _ => 4) s +
            (c2ConcreteResolventNonCancellationHorizontalTailUpper
              horizontalConstant horizontalScale horizontalRatio s + cutoffBudget s)) := by
          gcongr
    _ = c2ConcreteResolventNonCancellationAdjustedTailUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffBudget s := by
          simp [c2ConcreteResolventNonCancellationAdjustedTailUpper, add_assoc, add_left_comm, add_comm]

theorem c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetUpperBounds
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ ≤ cutoffBudget s)
    (hproxy : ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ ≤
      cutoffProxy s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffBudget s -
      cutoffProxy s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact c2ResolventNonCancellationAdjustedCriterion_of_errorSplit
    (FInfinity := genuineFInfinite)
    (FX := c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M)
    (quartet := c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff)
    (tail := c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M)
    (A := c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed)
    (beta := c2ConcreteResolventNonCancellationAdjustedRatio)
    (E0 := c2ConcreteResolventNonCancellationAdjustedError0 coreCutoff)
    (E1 := c2ConcreteResolventNonCancellationAdjustedError1 coreCutoff)
    (E2 := c2ConcreteResolventNonCancellationAdjustedError2 coreCutoff)
    (E3 := c2ConcreteResolventNonCancellationAdjustedError3 coreCutoff)
    (c2ConcreteResolventNonCancellationFiniteModel_eq_adjustedQuartet_add_tail tiltSeed coreCutoff K M s)
    (c2ConcreteResolventNonCancellationAdjustedQuartet_eq_errorSplit tiltSeed coreCutoff s)
    (c2ConcreteResolventNonCancellationAdjustedTail_norm_le_upper_of_bounds
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoff)
    hproxy
    (by
      simpa [c2ConcreteResolventNonCancellationAdjustedMain, c2ConcreteResolventNonCancellationAdjustedDefect] using hdom)

/-- Standard scaled-cutoff specialization of the explicit adjusted-tail upper bound. -/
noncomputable def c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  c2ConcreteResolventNonCancellationAdjustedTailUpper
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    (c2CutoffUpperFromScale cutoffConstant cutoffScale)

theorem c2ConcreteResolventNonCancellationAdjustedTail_norm_le_scaledUpper_of_bounds
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s) :
    ‖c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s‖ ≤
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s := by
  simpa [c2ConcreteResolventNonCancellationAdjustedTailScaledUpper] using
    (c2ConcreteResolventNonCancellationAdjustedTail_norm_le_upper_of_bounds
      (tiltSeed := tiltSeed) (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffBudget := c2CutoffUpperFromScale cutoffConstant cutoffScale)
      (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer
      (c2Cutoff_bound_from_scaled hcutoffScale hcutoffScaled))

theorem c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hproxy : ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ ≤
      cutoffProxy s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s -
      cutoffProxy s > 0) :
    genuineFInfinite s ≠ 0 := by
  simpa [c2ConcreteResolventNonCancellationAdjustedTailScaledUpper] using
    (c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetUpperBounds
      (tiltSeed := tiltSeed) (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffBudget := c2CutoffUpperFromScale cutoffConstant cutoffScale)
      (cutoffProxy := cutoffProxy) (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer
      (c2Cutoff_bound_from_scaled hcutoffScale hcutoffScaled)
      hproxy hdom)

theorem c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetUpperBounds_of_residualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoff : ‖c2ConcreteCutoffError K M s‖ ≤ cutoffBudget s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤ cutoffProxy s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffBudget s -
      cutoffProxy s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hproxy_eq :
      ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ =
        ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ := by
    simpa [c2ConcreteResolventNonCancellationResidual, c2ConcreteResolventNonCancellationFiniteModel,
      c2ScaledSeededExplicitOddTailBulkModelResidual, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using
      (norm_neg
        (c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s - genuineFInfinite s))
  have hproxy : ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ ≤
      cutoffProxy s := by
    rw [hproxy_eq]
    exact hresidual
  exact c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetUpperBounds
    (tiltSeed := tiltSeed) (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffBudget := cutoffBudget) (cutoffProxy := cutoffProxy) (s := s)
    hoff htiltScale htiltConstant_nonneg hseed
    hhorizontalScale hhorizontalConstant_nonneg
    hhorizontalRatio_nonneg hhorizontalRatio_lt_one
    hhorizontalLayer hcutoff hproxy hdom

theorem c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_residualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤ cutoffProxy s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s -
      cutoffProxy s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hproxy_eq :
      ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ =
        ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ := by
    simpa [c2ConcreteResolventNonCancellationResidual, c2ConcreteResolventNonCancellationFiniteModel,
      c2ScaledSeededExplicitOddTailBulkModelResidual, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using
      (norm_neg
        (c2ScaledSeededExplicitOddTailBulkModel tiltSeed coreCutoff K M s - genuineFInfinite s))
  have hproxy : ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ ≤
      cutoffProxy s := by
    rw [hproxy_eq]
    exact hresidual
  exact c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds
    (tiltSeed := tiltSeed) (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    (cutoffProxy := cutoffProxy) (s := s)
    hoff htiltScale htiltConstant_nonneg hseed
    hhorizontalScale hhorizontalConstant_nonneg
    hhorizontalRatio_nonneg hhorizontalRatio_lt_one
    hhorizontalLayer hcutoffScale hcutoffScaled hproxy hdom

/--
Analytic adjusted resolvent non-cancellation margin, with the cutoff proxy replaced by a real
upper bound for `|F_∞ - F_X|`.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale residualUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s -
      residualUpper s

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale residualUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤ residualUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale residualUpper s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_residualBound
    (tiltSeed := tiltSeed)
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    (cutoffProxy := residualUpper) (s := s)
    hoff htiltScale htiltConstant_nonneg hseed
    hhorizontalScale hhorizontalConstant_nonneg
    hhorizontalRatio_nonneg hhorizontalRatio_lt_one
    hhorizontalLayer hcutoffScale hcutoffScaled hresidual
    (by
      simpa [c2ConcreteResolventNonCancellationAdjustedAnalyticMargin] using hmargin)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_centralDefectBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale centralDefectUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hcentralDefect :
      ‖genuineCentralDoubleSeries s - continuedCentralOddChannel s‖ ≤ centralDefectUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale centralDefectUpper s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hresidual :
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤
        centralDefectUpper s := by
    rw [c2ConcreteResolventNonCancellationResidual_norm_eq_centralDefect_of_continuation_offCritical
      continuation hoff]
    exact hcentralDefect
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual hmargin

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_separatedCentralBounds
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      genuineCentralUpper continuedCentralUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hgenuine : C2GenuineCentralBound genuineCentralUpper s)
    (hcontinued : C2ContinuedCentralBound continuedCentralUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper) s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_centralDefectBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (centralDefectUpper :=
        c2CentralDefectTriangleUpper genuineCentralUpper continuedCentralUpper)
      continuation
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled
      (c2CentralDefectBound_triangle_of_bounds hgenuine hcontinued)
      hmargin

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_genuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale genuineCentralUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hgenuine : C2GenuineCentralBound genuineCentralUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            genuineCentralUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hcontinued :
      C2ContinuedCentralBound c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
    simpa [C2ContinuedCentralBound, c2ContinuedCentralExactUpper] using
      c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip hoff
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_separatedCentralBounds
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (genuineCentralUpper := genuineCentralUpper)
      (continuedCentralUpper := c2ExplicitFiniteCoreCentralExactZetaScalarUpper)
      continuation
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled
      hgenuine hcontinued hmargin

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_exactGenuineCentralBound
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (continuation : GenuineFInfiniteContinuationData)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          (c2CentralDefectTriangleUpper
            c2GenuineCentralExactUpper c2ExplicitFiniteCoreCentralExactZetaScalarUpper) s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_genuineCentralBound
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (genuineCentralUpper := c2GenuineCentralExactUpper)
      continuation hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled
      (c2GenuineCentralBound_exact s)
      hmargin

/--
Note-style exponential cutoff residual upper of the form
`C_Γ(s) * X^(1-σ) + C₁(s)/X + C₂(s)/X²`.
-/
noncomputable def c2ConcreteResolventNonCancellationExponentialResidualUpper
    (mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale : ℂ → ℝ) :
    ℂ → ℝ :=
  fun s =>
    mellinGammaUpper s * Real.rpow (cutoffScale s) (1 - s.re) +
      dirichletShiftUpper s / cutoffScale s +
      secondOrderUpper s / ((cutoffScale s) ^ 2)

/--
Adjusted resolvent non-cancellation margin specialized to the note-style exponential cutoff
residual upper.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedExponentialMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      mellinGammaUpper dirichletShiftUpper secondOrderUpper : ℂ → ℝ) :
    ℂ → ℝ :=
  c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
    tiltSeed coreCutoff
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
    (c2ConcreteResolventNonCancellationExponentialResidualUpper
      mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale)

/--
Pointwise oscillatory main term for a cutoff residual witness, keeping the
complex cancellation of the first `J - 1` Taylor terms instead of bounding each
moment separately.

The input `oscillatoryMoment j s` is the note-style moment `D_j(s)`.
-/
noncomputable def c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ) (cutoffScale : ℂ → ℝ) :
    ℂ → ℂ :=
  fun s =>
    Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
      (((-1 : ℂ) ^ j) /
          (((j.factorial : ℕ) : ℂ) * ((cutoffScale s : ℂ) ^ j))) *
        oscillatoryMoment j s

/--
Pointwise oscillatory cutoff witness of the form
`‖Σ_{1 ≤ j < J} (-1)^j D_j(s)/(j! X^j)‖ + remainderUpper(s)`.

This is the Lean-facing wrapper for the witness proposed in the resolvent non-cancellation
notes: the oscillatory main term is kept as a single complex quantity, and only
the final remainder is bounded coarsely.
-/
noncomputable def c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ)
    (cutoffScale remainderUpper : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    ‖c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
        oscillatoryMoment J cutoffScale s‖ +
      remainderUpper s

/--
Adjusted resolvent non-cancellation margin specialized to the pointwise oscillatory cutoff
witness.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ)
    (oscillatoryMoment : ℕ → ℂ → ℂ) (J : ℕ) :
    ℂ → ℝ :=
  c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
    tiltSeed coreCutoff
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
    (c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
      oscillatoryMoment J cutoffScale remainderUpper)

/--
Adjusted resolvent non-cancellation margin specialized to the explicit exponential pointwise
oscillatory witness coming from the finite exponential cutoff model.
-/
noncomputable def c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
    (tiltSeed : ℂ → ℂ) (coreCutoff : ℕ → ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (K M J : ℕ) (X : ℝ) :
    ℂ → ℝ :=
  c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
    tiltSeed coreCutoff
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale
    (c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X)

/-- Concrete exponential oscillatory main term with the Taylor denominator
carried by a fixed cutoff parameter `X`. -/
noncomputable def c2ExponentialPointwiseOscillatoryMain
    (K M J : ℕ) (X : ℝ) : ℂ → ℂ :=
  fun s => rectangularExponentialPointwiseOscillatoryMain s K M J X

/-- Concrete exponential remainder term attached to the `J - 1` oscillatory
main term. -/
noncomputable def c2ExponentialPointwiseOscillatoryRemainderTerm
    (K M J : ℕ) (X : ℝ) : ℂ → ℂ :=
  fun s =>
    rectangularExponentialTaylorRemainder s K M
        (exponentialCutoffTaylorRemainderCoeff X J) +
      c2ConcreteCutoffError K M s

/-- Exponential remainder budget attached to the `J - 1` oscillatory Taylor
main term. This keeps the cutoff error outside the complex oscillatory sum. -/
noncomputable def c2ExponentialPointwiseOscillatoryRemainderUpper
    (K M J : ℕ) (X : ℝ) : ℂ → ℝ :=
  fun s =>
    rectangularExponentialTaylorRemainderExpUpper s K M J X +
      ‖c2ConcreteCutoffError K M s‖

theorem c2ExponentialCutoffError_eq_pointwiseOscillatoryMain_add_remainderTerm
    (K M J : ℕ) (X : ℝ) (s : ℂ) :
    c2ExponentialCutoffError K M X s =
      c2ExponentialPointwiseOscillatoryMain K M J X s +
        c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s := by
  rw [c2ExponentialCutoffError_eq_residual_add_concreteCutoffError,
    rectangularExponentialResidual_eq_taylorMain_add_taylorRemainder,
    rectangularExponentialTaylorMain_eq_pointwiseOscillatoryMain]
  unfold c2ExponentialPointwiseOscillatoryMain
    c2ExponentialPointwiseOscillatoryRemainderTerm
  ring

theorem c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper
    (K M J : ℕ) (X : ℝ) {s : ℂ} (hJ : 1 ≤ J) :
    ‖c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s‖ ≤
      c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s := by
  unfold c2ExponentialPointwiseOscillatoryRemainderTerm
    c2ExponentialPointwiseOscillatoryRemainderUpper
  calc
    ‖rectangularExponentialTaylorRemainder s K M
        (exponentialCutoffTaylorRemainderCoeff X J) +
      c2ConcreteCutoffError K M s‖ ≤
        ‖rectangularExponentialTaylorRemainder s K M
            (exponentialCutoffTaylorRemainderCoeff X J)‖ +
          ‖c2ConcreteCutoffError K M s‖ := by
            exact norm_add_le _ _
    _ ≤ rectangularExponentialTaylorRemainderExpUpper s K M J X +
          ‖c2ConcreteCutoffError K M s‖ := by
            exact add_le_add
              (rectangularExponentialTaylorRemainder_norm_le_expUpper
                s K M J X hJ) le_rfl

theorem c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper_three
    (K M : ℕ) (X : ℝ) (s : ℂ) :
    ‖c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s‖ ≤
      c2ExponentialPointwiseOscillatoryRemainderUpper K M 3 X s := by
  exact c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper
    K M 3 X (s := s) (by decide)

theorem c2ExponentialCutoffErrorPointwiseOscillatoryUpper_eq_main_add_remainderUpper
    (K M J : ℕ) (X : ℝ) (s : ℂ) :
    c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s =
      ‖c2ExponentialPointwiseOscillatoryMain K M J X s‖ +
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s := by
  simp [c2ExponentialCutoffErrorPointwiseOscillatoryUpper,
    c2ExponentialCutoffErrorPointwiseOscillatoryExpUpper,
    c2ExponentialPointwiseOscillatoryMain,
    c2ExponentialPointwiseOscillatoryRemainderUpper,
    rectangularExponentialPointwiseOscillatoryExpUpper,
    add_assoc]

theorem c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_add_remainder
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ} {remainderTerm : ℂ → ℂ} {s : ℂ}
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder :
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s) :
    ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s := by
  have hmain :
      ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
        ‖c2ExponentialPointwiseOscillatoryMain K M J X s‖ +
          ‖remainderTerm s‖ := by
    rw [hexpansion]
    exact norm_add_le _ _
  have hupper :
      ‖c2ExponentialPointwiseOscillatoryMain K M J X s‖ +
          ‖remainderTerm s‖ ≤
        ‖c2ExponentialPointwiseOscillatoryMain K M J X s‖ +
          c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s := by
    exact add_le_add le_rfl hremainder
  rw [c2ExponentialCutoffErrorPointwiseOscillatoryUpper_eq_main_add_remainderUpper
    K M J X s]
  exact le_trans hmain hupper

theorem
    c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_canonicalRemainder
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ} {s : ℂ}
    (hJ : 1 ≤ J)
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M J X s) :
    ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s := by
  exact
    c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_add_remainder
      (K := K) (M := M) (J := J) (X := X)
      hexpansion
      (c2ExponentialPointwiseOscillatoryRemainderTerm_norm_le_upper
        K M J X (s := s) hJ)

theorem
    c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_canonicalRemainder_three
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {X : ℝ} {s : ℂ}
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M 3 X s +
          c2ExponentialPointwiseOscillatoryRemainderTerm K M 3 X s) :
    ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M 3 X s := by
  exact
    c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_canonicalRemainder
      (K := K) (M := M) (J := 3) (X := X) (s := s)
      (by decide) hexpansion

theorem c2ConcreteResolventNonCancellationHorizontalDefect_add_tail_le_regularizedUpper
    {coreCutoff : ℕ → ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ}
    (_hhorizontalScale : 0 < horizontalScale s)
    (_hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s +
      c2ConcreteResolventNonCancellationHorizontalTailUpper
        horizontalConstant horizontalScale horizontalRatio s ≤
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s := by
  have hquartet :
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s ≤
        c2TiltPartialGeometricUpper
          horizontalConstant horizontalScale horizontalRatio (fun _ => 4) s := by
    unfold c2ConcreteResolventNonCancellationAdjustedDefect
      c2ConcreteResolventNonCancellationAdjustedError0
      c2ConcreteResolventNonCancellationAdjustedError1
      c2ConcreteResolventNonCancellationAdjustedError2
      c2ConcreteResolventNonCancellationAdjustedError3
      c2TiltPartialGeometricUpper
    simp [Finset.sum_range_succ]
    linarith [hhorizontalLayer 0, hhorizontalLayer 1,
      hhorizontalLayer 2, hhorizontalLayer 3]
  have hregularized :
      c2TiltPartialGeometricUpper
          horizontalConstant horizontalScale horizontalRatio (fun _ => 4) s +
        c2ConcreteResolventNonCancellationHorizontalTailUpper
          horizontalConstant horizontalScale horizontalRatio s =
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s := by
    simpa [c2ConcreteResolventNonCancellationHorizontalTailUpper,
      c2HorizontalTailGeometricUpper,
      c2HorizontalRegularizedUpper,
      c2TiltRegularizedUpper] using
      (c2TiltPartialGeometricUpper_add_tail_eq_regularized
        (tiltCutoff := fun _ => 4)
        (tiltConstant := horizontalConstant)
        (tiltScale := horizontalScale)
        (tiltRatio := horizontalRatio)
        (s := s)
        hhorizontalRatio_nonneg hhorizontalRatio_lt_one)
  linarith

theorem
    c2ConcreteResolventNonCancellationAdjustedBaseMargin_ge_expandedQuartetResidualMargin_sub_residualUpper
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (_htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j) :
    c2ExpandedQuartetResidualMargin s -
      c2ExpandedQuartetResidualUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s ≤
    c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s := by
  have htiltLayer : ∀ j : ℕ,
      ‖c2SeededTiltLayerResidual tiltSeed s j‖ ≤
        (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j :=
    c2SeededTiltLayerResidual_bound hseed
  have htiltPartial_eq :
      c2ConcreteTiltPartialResidual
          (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s =
        tiltSeed s * verticalQuartetPrefix (q s) := by
    calc
      c2ConcreteTiltPartialResidual
          (c2SeededTiltLayerResidual tiltSeed) (fun _ => 4) s =
          tiltSeed s + tiltSeed s * q s +
            (tiltSeed s * q s ^ 2 + tiltSeed s * q s ^ 3) := by
              unfold c2ConcreteTiltPartialResidual c2TiltPartialSum
                c2SeededTiltLayerResidual
              simp [Finset.sum_range_succ]
              ring
      _ = tiltSeed s * verticalQuartetPrefix (q s) := by
            unfold verticalQuartetPrefix
            ring
  have htiltPartial :
      ‖tiltSeed s * verticalQuartetPrefix (q s)‖ ≤
        c2TiltAnalyticPartialGeometricUpper
          tiltConstant tiltScale (fun _ => 4) s := by
    rw [← htiltPartial_eq]
    simpa [c2TiltAnalyticPartialGeometricUpper] using
      (c2ConcreteTiltPartialResidual_norm_le_geometric
        (tiltLayerResidual := c2SeededTiltLayerResidual tiltSeed)
        (tiltCutoff := fun _ => 4)
        (tiltConstant := tiltConstant)
        (tiltScale := tiltScale)
        (tiltRatio := c2TiltAnalyticRatio)
        (s := s)
        htiltScale htiltLayer)
  have htiltReg :
      c2TiltAnalyticPartialGeometricUpper
          tiltConstant tiltScale (fun _ => 4) s +
        c2TiltAnalyticTailGeometricUpper
          tiltConstant tiltScale (fun _ => 4) s =
      c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s := by
    simpa [c2TiltAnalyticPartialGeometricUpper,
      c2TiltAnalyticTailGeometricUpper,
      c2TiltAnalyticRegularizedUpper] using
      (c2TiltPartialGeometricUpper_add_tail_eq_regularized
        (tiltCutoff := fun _ => 4)
        (tiltConstant := tiltConstant)
        (tiltScale := tiltScale)
        (tiltRatio := c2TiltAnalyticRatio)
        (s := s)
        (c2TiltAnalyticRatio_nonneg s)
        (c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hoff))
  have hk2Prefix :
      c2ExpandedQuartetK2Margin s ≤
        ‖c2QuartetBulkK2 s * verticalQuartetPrefix (q s)‖ := by
    have hprefix :=
      verticalQuartetPrefix_norm_lower_bound_of_offCriticalStrip s hoff
    have hk2_nonneg : 0 ≤ c2QuartetBulkK2Lower s := by
      rw [c2QuartetBulkK2Lower_eq_norm]
      exact norm_nonneg _
    calc
      c2ExpandedQuartetK2Margin s =
          c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2)) := by
            rfl
      _ ≤ c2QuartetBulkK2Lower s * ‖verticalQuartetPrefix (q s)‖ := by
            exact mul_le_mul_of_nonneg_left hprefix hk2_nonneg
      _ = ‖c2QuartetBulkK2 s‖ * ‖verticalQuartetPrefix (q s)‖ := by
            rw [c2QuartetBulkK2Lower_eq_norm]
      _ = ‖c2QuartetBulkK2 s * verticalQuartetPrefix (q s)‖ := by
            rw [norm_mul]
  have hmain :
      c2ExpandedQuartetK2Margin s -
        c2TiltAnalyticPartialGeometricUpper
          tiltConstant tiltScale (fun _ => 4) s ≤
      c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s := by
    have htri :
        ‖c2QuartetBulkK2 s * verticalQuartetPrefix (q s)‖ ≤
          ‖(c2QuartetBulkK2 s + tiltSeed s) * verticalQuartetPrefix (q s)‖ +
            ‖tiltSeed s * verticalQuartetPrefix (q s)‖ := by
      have hsplit :
          c2QuartetBulkK2 s * verticalQuartetPrefix (q s) =
            (c2QuartetBulkK2 s + tiltSeed s) * verticalQuartetPrefix (q s) -
              tiltSeed s * verticalQuartetPrefix (q s) := by
        ring
      rw [hsplit]
      exact norm_sub_le _ _
    have hmain' :
        c2ExpandedQuartetK2Margin s -
          c2TiltAnalyticPartialGeometricUpper
            tiltConstant tiltScale (fun _ => 4) s ≤
        ‖(c2QuartetBulkK2 s + tiltSeed s) * verticalQuartetPrefix (q s)‖ := by
      linarith [hk2Prefix, htri, htiltPartial]
    simpa [c2ConcreteResolventNonCancellationAdjustedMain,
      c2ConcreteResolventNonCancellationAdjustedAmplitude] using hmain'
  have hhorizontal :
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s +
        c2ConcreteResolventNonCancellationHorizontalTailUpper
          horizontalConstant horizontalScale horizontalRatio s ≤
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s :=
    c2ConcreteResolventNonCancellationHorizontalDefect_add_tail_le_regularizedUpper
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one hhorizontalLayer
  have hbase :
      c2ExpandedQuartetK2Margin s - c2QuartetVerticalTailUpper s -
        c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s -
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s -
        c2CutoffUpperFromScale cutoffConstant cutoffScale s ≤
      c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
        c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
        c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s := by
    unfold c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
      c2ConcreteResolventNonCancellationAdjustedTailUpper
    linarith [hmain, htiltReg, hhorizontal]
  convert hbase using 1;
    simp [c2ExpandedQuartetResidualMargin, c2ExpandedQuartetResidualUpper]
  ring

theorem
    c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_combinedResidualDominance
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
        tiltSeed coreCutoff
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale
        K M J X s > 0 := by
  have hbase :=
    c2ConcreteResolventNonCancellationAdjustedBaseMargin_ge_expandedQuartetResidualMargin_sub_residualUpper
      (tiltSeed := tiltSeed) (coreCutoff := coreCutoff)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one hhorizontalLayer
  unfold c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin at *
  linarith

theorem c2ConcreteResolventNonCancellationAdjustedAnalyticMargin_pos_of_combinedResidualDominance
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale residualUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        residualUpper s <
      c2ExpandedQuartetResidualMargin s) :
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin
        tiltSeed coreCutoff
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale residualUpper s > 0 := by
  have hbase :=
    c2ConcreteResolventNonCancellationAdjustedBaseMargin_ge_expandedQuartetResidualMargin_sub_residualUpper
      (tiltSeed := tiltSeed) (coreCutoff := coreCutoff)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one hhorizontalLayer
  unfold c2ConcreteResolventNonCancellationAdjustedAnalyticMargin at *
  linarith

theorem c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_dominance
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ} {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hdominance :
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
        c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
          c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
          c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale s) :
    c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
        tiltSeed coreCutoff
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale
        K M J X s > 0 := by
  unfold c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
    c2ConcreteResolventNonCancellationAdjustedAnalyticMargin at *
  linarith

theorem
    c2ConcreteResolventNonCancellationResidual_norm_le_pointwiseOscillatoryResidualUpper_of_eq_add_remainder
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ} {s : ℂ}
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ‖remainderTerm s‖ ≤ remainderUpper s) :
    ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
        oscillatoryMoment J cutoffScale remainderUpper s := by
  have hmain :
      ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
        ‖c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s‖ +
          ‖remainderTerm s‖ := by
    rw [hexpansion]
    exact norm_add_le _ _
  have hupper :
      ‖c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
          oscillatoryMoment J cutoffScale s‖ +
        ‖remainderTerm s‖ ≤
      ‖c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
          oscillatoryMoment J cutoffScale s‖ +
        remainderUpper s := by
    exact add_le_add le_rfl hremainder
  exact le_trans hmain (by
    simpa [c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper] using hupper)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialResidualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale
      mellinGammaUpper dirichletShiftUpper secondOrderUpper : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ConcreteResolventNonCancellationExponentialResidualUpper
        mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedExponentialMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          mellinGammaUpper dirichletShiftUpper secondOrderUpper s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (residualUpper := c2ConcreteResolventNonCancellationExponentialResidualUpper
        mellinGammaUpper dirichletShiftUpper secondOrderUpper cutoffScale)
      (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual
      (by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialMargin] using hmargin)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_pointwiseOscillatoryResidualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
        oscillatoryMoment J cutoffScale remainderUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (residualUpper := c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
        oscillatoryMoment J cutoffScale remainderUpper)
      (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual
      (by
        simpa [c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin] using hmargin)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryResidualBound
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_analyticResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (residualUpper := c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X)
      (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual
      (by
        simpa [c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin] using
          hmargin)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryDominance
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance :
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
        c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
          c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
          c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
            tiltConstant tiltScale
            horizontalConstant horizontalScale horizontalRatio
            cutoffConstant cutoffScale s) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual
      (c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_dominance
        (tiltSeed := tiltSeed) (coreCutoff := coreCutoff)
        (K := K) (M := M) (J := J) (X := X)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        hdominance)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryCombinedResidualDominance
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hresidual : ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
      c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s)
    (hdominance :
      c2ExpandedQuartetResidualUpper
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale s +
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s <
      c2ExpandedQuartetResidualMargin s) :
    genuineFInfinite s ≠ 0 := by
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual
      (c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin_pos_of_combinedResidualDominance
        (tiltSeed := tiltSeed) (coreCutoff := coreCutoff)
        (K := K) (M := M) (J := J) (X := X)
        (tiltConstant := tiltConstant) (tiltScale := tiltScale)
        (horizontalConstant := horizontalConstant)
        (horizontalScale := horizontalScale)
        (horizontalRatio := horizontalRatio)
        (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
        hoff htiltScale htiltConstant_nonneg hseed
        hhorizontalScale hhorizontalConstant_nonneg
        hhorizontalRatio_nonneg hhorizontalRatio_lt_one
        hhorizontalLayer hdominance)

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_pointwiseOscillatoryExpansion
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale remainderUpper : ℂ → ℝ}
    {oscillatoryMoment : ℕ → ℂ → ℂ} {J : ℕ}
    {remainderTerm : ℂ → ℂ} {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ConcreteResolventNonCancellationPointwiseOscillatoryMain
            oscillatoryMoment J cutoffScale s +
          remainderTerm s)
    (hremainder : ‖remainderTerm s‖ ≤ remainderUpper s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedPointwiseOscillatoryMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale remainderUpper
          oscillatoryMoment J s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hresidual :
      ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
        c2ConcreteResolventNonCancellationPointwiseOscillatoryResidualUpper
          oscillatoryMoment J cutoffScale remainderUpper s :=
    c2ConcreteResolventNonCancellationResidual_norm_le_pointwiseOscillatoryResidualUpper_of_eq_add_remainder
      hexpansion hremainder
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_pointwiseOscillatoryResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M)
      (tiltConstant := tiltConstant) (tiltScale := tiltScale)
      (horizontalConstant := horizontalConstant)
      (horizontalScale := horizontalScale)
      (horizontalRatio := horizontalRatio)
      (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
      (remainderUpper := remainderUpper)
      (oscillatoryMoment := oscillatoryMoment) (J := J)
      (s := s)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual hmargin

theorem
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryExpansion
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M J : ℕ}
    {X : ℝ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {remainderTerm : ℂ → ℂ} {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hexpansion :
      c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s =
        c2ExponentialPointwiseOscillatoryMain K M J X s +
          remainderTerm s)
    (hremainder :
      ‖remainderTerm s‖ ≤
        c2ExponentialPointwiseOscillatoryRemainderUpper K M J X s)
    (hmargin :
      c2ConcreteResolventNonCancellationAdjustedExponentialPointwiseOscillatoryMargin
          tiltSeed coreCutoff
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
          K M J X s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hresidual :
      ‖c2ConcreteResolventNonCancellationResidual tiltSeed coreCutoff K M s‖ ≤
        c2ExponentialCutoffErrorPointwiseOscillatoryUpper K M J X s :=
    c2ConcreteResolventNonCancellationResidual_norm_le_exponentialPointwiseOscillatoryUpper_of_eq_add_remainder
      (K := K) (M := M) (J := J) (X := X)
      hexpansion hremainder
  exact
    c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_exponentialPointwiseOscillatoryResidualBound
      (tiltSeed := tiltSeed)
      (coreCutoff := coreCutoff) (K := K) (M := M) (J := J) (X := X)
      hoff htiltScale htiltConstant_nonneg hseed
      hhorizontalScale hhorizontalConstant_nonneg
      hhorizontalRatio_nonneg hhorizontalRatio_lt_one
      hhorizontalLayer hcutoffScale hcutoffScaled hresidual hmargin

theorem c2ConcreteResolventNonCancellationResidual_eq_zero_of_oddTailBalancingSeed_of_comparison
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison : C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M)
    {s : ℂ} (hs : s ∈ openRightHalfPlane) :
    c2ConcreteResolventNonCancellationResidual (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s = 0 := by
  have hmodel :=
    c2OddTailBalancingSeedBulkModel_eq_genuineFInfinite_on_openRightHalfPlane
      comparison s hs
  simpa [c2ConcreteResolventNonCancellationResidual, c2ConcreteResolventNonCancellationFiniteModel,
    c2ScaledSeededExplicitOddTailBulkModelResidual, c2OddTailBalancingSeedBulkModel] using
    sub_eq_zero.mpr hmodel

theorem c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_comparison
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison : C2OddTailBalancingSeedBulkModelComparisonFromOneLtData coreCutoff K M)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain (c2OddTailBalancingSeed coreCutoff K M) s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s > 0) :
    genuineFInfinite s ≠ 0 := by
  have hsOpen : s ∈ openRightHalfPlane := by
    simpa [openRightHalfPlane] using hoff.1
  have hres_eq :
      c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s = 0 :=
    c2ConcreteResolventNonCancellationResidual_eq_zero_of_oddTailBalancingSeed_of_comparison
      comparison hsOpen
  have hresidual :
      ‖c2ConcreteResolventNonCancellationResidual
          (c2OddTailBalancingSeed coreCutoff K M) coreCutoff K M s‖ ≤ 0 := by
    simp [hres_eq]
  exact c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetScaledUpperBounds_of_residualBound
    (tiltSeed := c2OddTailBalancingSeed coreCutoff K M)
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (tiltConstant := tiltConstant) (tiltScale := tiltScale)
    (horizontalConstant := horizontalConstant)
    (horizontalScale := horizontalScale)
    (horizontalRatio := horizontalRatio)
    (cutoffConstant := cutoffConstant) (cutoffScale := cutoffScale)
    (cutoffProxy := fun _ => 0) (s := s)
    hoff htiltScale htiltConstant_nonneg hseed
    hhorizontalScale hhorizontalConstant_nonneg
    hhorizontalRatio_nonneg hhorizontalRatio_lt_one
    hhorizontalLayer hcutoffScale hcutoffScaled hresidual
    (by simpa using hdom)

theorem c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_atOne
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    (comparison : C2OddTailBalancingSeedBulkModelComparisonFromOneLtAtOneData coreCutoff K M)
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    {s : ℂ}
    (hoff : offCriticalStrip s)
    (htiltScale : 0 < tiltScale s)
    (htiltConstant_nonneg : 0 ≤ tiltConstant s)
    (hseed : ‖c2OddTailBalancingSeed coreCutoff K M s‖ ≤ tiltConstant s / tiltScale s)
    (hhorizontalScale : 0 < horizontalScale s)
    (hhorizontalConstant_nonneg : 0 ≤ horizontalConstant s)
    (hhorizontalRatio_nonneg : 0 ≤ horizontalRatio s)
    (hhorizontalRatio_lt_one : horizontalRatio s < 1)
    (hhorizontalLayer : ∀ j : ℕ,
      ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
        (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j)
    (hcutoffScale : 0 < cutoffScale s)
    (hcutoffScaled : ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain (c2OddTailBalancingSeed coreCutoff K M) s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      c2ConcreteResolventNonCancellationAdjustedTailScaledUpper
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact c2ResolventNonCancellationAdjustedCriterion_of_oddTailBalancingSeedScaledUpperBounds_of_comparison
    (coreCutoff := coreCutoff) (K := K) (M := M)
    (c2OddTailBalancingSeedBulkModelComparisonFromOneLtData_of_atOne comparison)
    hoff htiltScale htiltConstant_nonneg hseed
    hhorizontalScale hhorizontalConstant_nonneg
    hhorizontalRatio_nonneg hhorizontalRatio_lt_one
    hhorizontalLayer hcutoffScale hcutoffScaled hdom

/--
Concrete adjusted resolvent non-cancellation criterion specialized to the current seeded tilt and
horizontal-layer package. The remaining obligations are exactly the tail budget,
the proxy against `genuineFInfinite`, and the final positivity inequality.
-/
theorem c2ResolventNonCancellationAdjustedCriterion_of_concreteSeededQuartetBounds
    {tiltSeed : ℂ → ℂ} {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tailBudget cutoffProxy : ℂ → ℝ}
    {s : ℂ}
    (htail : ‖c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M s‖ ≤ tailBudget s)
    (hproxy : ‖genuineFInfinite s - c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M s‖ ≤
      cutoffProxy s)
    (hdom : c2ConcreteResolventNonCancellationAdjustedMain tiltSeed s -
      c2ConcreteResolventNonCancellationAdjustedDefect coreCutoff s -
      tailBudget s - cutoffProxy s > 0) :
    genuineFInfinite s ≠ 0 := by
  exact c2ResolventNonCancellationAdjustedCriterion_of_errorSplit
    (FInfinity := genuineFInfinite)
    (FX := c2ConcreteResolventNonCancellationFiniteModel tiltSeed coreCutoff K M)
    (quartet := c2ConcreteResolventNonCancellationAdjustedQuartet tiltSeed coreCutoff)
    (tail := c2ConcreteResolventNonCancellationAdjustedTail tiltSeed coreCutoff K M)
    (A := c2ConcreteResolventNonCancellationAdjustedAmplitude tiltSeed)
    (beta := c2ConcreteResolventNonCancellationAdjustedRatio)
    (E0 := c2ConcreteResolventNonCancellationAdjustedError0 coreCutoff)
    (E1 := c2ConcreteResolventNonCancellationAdjustedError1 coreCutoff)
    (E2 := c2ConcreteResolventNonCancellationAdjustedError2 coreCutoff)
    (E3 := c2ConcreteResolventNonCancellationAdjustedError3 coreCutoff)
    (c2ConcreteResolventNonCancellationFiniteModel_eq_adjustedQuartet_add_tail tiltSeed coreCutoff K M s)
    (c2ConcreteResolventNonCancellationAdjustedQuartet_eq_errorSplit tiltSeed coreCutoff s)
    htail hproxy
    (by
      simpa [c2ConcreteResolventNonCancellationAdjustedMain, c2ConcreteResolventNonCancellationAdjustedDefect] using hdom)

structure C2ExpandedExactZetaDominanceEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  balancing_seed_factor_scaled_bound :
    ((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)) * tiltScale s ≤ tiltConstant s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_closed_scaled_bound :
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s *
      cutoffScale s ≤ cutoffConstant s
  dominance :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

def c2ExpandedExactZetaDominanceRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2ExpandedExactZetaDominanceEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2ExpandedDominance_mem_expandedExactZetaRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetExpandedExactZetaRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := hs.balancing_seed_factor_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := hs.cutoff_closed_scaled_bound
    quartet_dominance := by
      simpa [C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper,
        c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
        c2ExpandedQuartetK2Margin] using hs.dominance
  }

theorem c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedExactZetaRegion
    (c2ExpandedDominance_mem_expandedExactZetaRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedExactZetaRegion
    (c2ExpandedDominance_mem_expandedExactZetaRegion hs)

/-- Nonnegativity of the regularized horizontal scalar envelope. -/
lemma c2HorizontalRegularizedUpper_nonneg_of_pos
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_lt_one : horizontalRatio s < 1) :
    0 ≤ c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s := by
  have hden_nonneg : 0 ≤ 1 - horizontalRatio s := by
    linarith
  unfold c2HorizontalRegularizedUpper
  exact mul_nonneg
    (div_nonneg hconstant (le_of_lt hscale))
    (inv_nonneg.mpr hden_nonneg)

/-- Canonical tilt constant for the closed-layer route with unit tilt scale. -/
noncomputable def c2CanonicalClosedTiltConstant
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    (c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s +
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)

/-- Canonical cutoff constant for the closed-layer route with unit cutoff scale. -/
noncomputable def c2CanonicalClosedCutoffConstant
    (K M : ℕ) : ℂ → ℝ :=
  c2ContinuedCutoffClosedUpper K M
    (c2RectangularGenuineDirectBracketUpper K M)
    c2ContinuedCentralExactUpper

theorem c2CanonicalClosedCutoffConstant_le_finiteExactZetaUpper_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedCutoffConstant K M s ≤
      c2CanonicalClosedCutoffFiniteExactZetaUpper K M s := by
  have hdirect :
      ‖rectangularDirect s K M‖ ≤ c2RectangularDirectFiniteUpper K M s :=
    rectangularDirect_norm_le_finiteUpper s K M
  have hbracket :
      ‖rectangularBracket s K M‖ ≤ c2RectangularBracketFiniteUpper K M s :=
    rectangularBracket_norm_le_finiteUpper s K M
  have hcentral :
      ‖continuedCentralOddChannel s‖ ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s := by
    simpa [c2ContinuedCentralExactUpper] using
      c2ContinuedCentralExactUpper_le_exactZetaScalar_of_offCriticalStrip hs
  unfold c2CanonicalClosedCutoffConstant c2ContinuedCutoffClosedUpper
    c2RectangularGenuineDirectBracketUpper c2ContinuedCentralExactUpper
    c2CanonicalClosedCutoffFiniteExactZetaUpper
  linarith

/-- Exact residual quartet upper for the canonical closed/scaled route. -/
noncomputable def c2CanonicalClosedScaledResidualUpper
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  c2ExpandedQuartetResidualUpper
    (c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio)
    (fun _ => (1 : ℝ))
    horizontalConstant horizontalScale horizontalRatio
    (c2CanonicalClosedCutoffConstant K M)
    (fun _ => (1 : ℝ))

/-- Explicit expanded form of the canonical residual upper. -/
noncomputable def c2CanonicalClosedScaledResidualExpandedUpper
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    (c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s +
      c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s) *
      ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
    c2HorizontalRegularizedUpper
      horizontalConstant horizontalScale horizontalRatio s +
    c2CanonicalClosedCutoffConstant K M s

/-- Residual upper with the horizontal term merged into a single geometric factor. -/
noncomputable def c2CanonicalClosedScaledResidualLinearUpper
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s *
      ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
    c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2CanonicalClosedCutoffConstant K M s

/-- Coarser majorant of the canonical residual upper. -/
noncomputable def c2CanonicalClosedScaledResidualMajorant
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2CanonicalClosedCutoffConstant K M s

/-- Residual majorant with the canonical vertical term replaced by an external budget. -/
noncomputable def c2CanonicalClosedScaledResidualVerticalBudgetUpper
    (K M : ℕ)
    (verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    verticalUpper s * (2 * (1 - ‖q s‖)⁻¹) +
    c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2CanonicalClosedCutoffConstant K M s


/-- Fully explicit residual upper using finite exact-zeta envelopes for the vertical and cutoff pieces. -/
noncomputable def c2CanonicalClosedScaledResidualFiniteExactZetaUpper
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2CanonicalClosedVerticalFiniteExactZetaUpper K M s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s *
      (2 * (1 - ‖q s‖)⁻¹) +
    c2CanonicalClosedCutoffFiniteExactZetaUpper K M s

theorem c2CanonicalClosedVerticalUpper_eq_directBracketExact
    (K M : ℕ) (s : ℂ) :
    c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s =
      verticalDepthTailUpper s +
        ‖rectangularDirect s K M‖ + ‖rectangularBracket s K M‖ +
        2 * ‖continuedCentralOddChannel s‖ := by
  unfold c2ContinuedVerticalResidualClosedUpper
    c2RectangularGenuineDirectBracketUpper c2ContinuedCentralExactUpper
  ring

theorem c2CanonicalClosedScaledResidualUpper_eq_expanded
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) :
    c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s =
      c2CanonicalClosedScaledResidualExpandedUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  simp [c2CanonicalClosedScaledResidualUpper,
    c2CanonicalClosedScaledResidualExpandedUpper,
    c2ExpandedQuartetResidualUpper, c2CanonicalClosedTiltConstant,
    c2CanonicalClosedCutoffConstant, c2TiltAnalyticRegularizedUpper,
    c2TiltRegularizedUpper, c2TiltAnalyticRatio, c2CutoffUpperFromScale,
    mul_assoc, add_assoc]

theorem c2CanonicalClosedScaledResidualExpanded_eq_linear_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualExpandedUpper
        K M horizontalConstant horizontalScale horizontalRatio s =
      c2CanonicalClosedScaledResidualLinearUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hden : 1 - ‖q s‖ ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hq_lt))
  have hhorizontal :
      c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s *
        ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s =
      c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s *
        (2 * (1 - ‖q s‖)⁻¹) := by
    have hcoeff :
        ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) + 1 = 2 * (1 - ‖q s‖)⁻¹ := by
      field_simp [hden]
      ring
    calc
      c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s *
          ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s
          = c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s *
              ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
            c2HorizontalRegularizedUpper
              horizontalConstant horizontalScale horizontalRatio s * 1 := by
                rw [mul_one]
      _ = c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s *
            (((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) + 1) := by ring
      _ = c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s *
            (2 * (1 - ‖q s‖)⁻¹) := by rw [hcoeff]
  unfold c2CanonicalClosedScaledResidualExpandedUpper
    c2CanonicalClosedScaledResidualLinearUpper
  have hmain :
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s *
        ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
        (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s *
            ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
          c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s) +
        c2CanonicalClosedCutoffConstant K M s =
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s *
        ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s *
        (2 * (1 - ‖q s‖)⁻¹) +
        c2CanonicalClosedCutoffConstant K M s := by
    rw [hhorizontal]
  simpa [add_assoc, add_mul] using hmain

theorem c2CanonicalClosedScaledResidualUpper_eq_linear_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s =
      c2CanonicalClosedScaledResidualLinearUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  rw [c2CanonicalClosedScaledResidualUpper_eq_expanded]
  exact c2CanonicalClosedScaledResidualExpanded_eq_linear_of_offCriticalStrip hs

theorem c2CanonicalClosedScaledResidualUpper_le_majorant_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualUpper
        K M horizontalConstant horizontalScale horizontalRatio s ≤
      c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s := by
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hgap_nonneg : 0 ≤ 1 - ‖q s‖ := by
    linarith [norm_nonneg (q s), hq_lt]
  have hinv_nonneg : 0 ≤ (1 - ‖q s‖)⁻¹ :=
    inv_nonneg.mpr hgap_nonneg
  have hvert_nonneg :
      0 ≤ c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s :=
    c2ContinuedVerticalResidualClosedUpper_nonneg_of_bounds
      hs
      (c2RectangularGenuineBound_directBracket K M s)
      (c2ContinuedCentralBound_exact s)
  have hcoeff_le :
      (1 + ‖q s‖) * (1 - ‖q s‖)⁻¹ ≤ 2 * (1 - ‖q s‖)⁻¹ := by
    have htop : 1 + ‖q s‖ ≤ 2 := by
      linarith [norm_nonneg (q s), hq_lt]
    exact mul_le_mul_of_nonneg_right htop hinv_nonneg
  rw [c2CanonicalClosedScaledResidualUpper_eq_linear_of_offCriticalStrip hs]
  unfold c2CanonicalClosedScaledResidualLinearUpper
    c2CanonicalClosedScaledResidualMajorant
  have hvertical :
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s *
        ((1 + ‖q s‖) * (1 - ‖q s‖)⁻¹) ≤
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s *
        (2 * (1 - ‖q s‖)⁻¹) :=
    mul_le_mul_of_nonneg_left hcoeff_le hvert_nonneg
  exact add_le_add (add_le_add hvertical le_rfl) le_rfl

theorem c2CanonicalClosedScaledResidualMajorant_le_verticalBudget_of_offCriticalStrip
    {K M : ℕ}
    {verticalUpper horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s)
    (hvertical :
      c2ContinuedVerticalResidualClosedUpper K M
          (c2RectangularGenuineDirectBracketUpper K M)
          c2ContinuedCentralExactUpper s ≤
        verticalUpper s) :
    c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s ≤
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M verticalUpper horizontalConstant horizontalScale horizontalRatio s := by
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hgap_nonneg : 0 ≤ 1 - ‖q s‖ := by
    linarith [norm_nonneg (q s), hq_lt]
  have hcoeff_nonneg : 0 ≤ 2 * (1 - ‖q s‖)⁻¹ := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (inv_nonneg.mpr hgap_nonneg)
  unfold c2CanonicalClosedScaledResidualMajorant
    c2CanonicalClosedScaledResidualVerticalBudgetUpper
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right hvertical hcoeff_nonneg)
      le_rfl)
    le_rfl

theorem c2CanonicalClosedScaledResidualMajorant_le_finiteExactZetaVerticalBudget_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s ≤
      c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M (c2CanonicalClosedVerticalFiniteExactZetaUpper K M)
        horizontalConstant horizontalScale horizontalRatio s := by
  apply c2CanonicalClosedScaledResidualMajorant_le_verticalBudget_of_offCriticalStrip hs
  exact c2CanonicalClosedVerticalUpper_le_finiteExactZetaUpper_of_offCriticalStrip K M hs

theorem c2CanonicalClosedScaledResidualVerticalBudgetUpper_le_finiteExactZeta_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualVerticalBudgetUpper
        K M (c2CanonicalClosedVerticalFiniteExactZetaUpper K M)
        horizontalConstant horizontalScale horizontalRatio s ≤
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  have hcutoff :
      c2CanonicalClosedCutoffConstant K M s ≤
        c2CanonicalClosedCutoffFiniteExactZetaUpper K M s :=
    c2CanonicalClosedCutoffConstant_le_finiteExactZetaUpper_of_offCriticalStrip K M hs
  unfold c2CanonicalClosedScaledResidualVerticalBudgetUpper
    c2CanonicalClosedScaledResidualFiniteExactZetaUpper
  exact add_le_add (add_le_add le_rfl le_rfl) hcutoff

theorem c2CanonicalClosedScaledResidualMajorant_le_finiteExactZeta_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s) :
    c2CanonicalClosedScaledResidualMajorant
        K M horizontalConstant horizontalScale horizontalRatio s ≤
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  exact le_trans
    (c2CanonicalClosedScaledResidualMajorant_le_finiteExactZetaVerticalBudget_of_offCriticalStrip
      hs)
    (c2CanonicalClosedScaledResidualVerticalBudgetUpper_le_finiteExactZeta_of_offCriticalStrip
      hs)

theorem c2ExpandedQuartetResidualMargin_lt_scaledVerticalDepthTail_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    c2ExpandedQuartetResidualMargin s <
      verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) := by
  have hq_nonneg : 0 ≤ ‖q s‖ := norm_nonneg _
  have hq_pos : 0 < ‖q s‖ := by
    have hq_ne : q s ≠ 0 := by
      unfold q verticalRatio
      exact complexDirichletDepthRatio_ne_zero s
    exact norm_pos_iff.mpr hq_ne
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hgap_pos : 0 < 1 - ‖q s‖ := by
    linarith
  have hgap_ne : 1 - ‖q s‖ ≠ 0 := ne_of_gt hgap_pos
  have hpoly_aux_nonneg :
      0 ≤ 2 * ‖q s‖ * (1 - ‖q s‖) * (1 - ‖q s‖ + ‖q s‖ ^ 2) := by
    have hgap_nonneg : 0 ≤ 1 - ‖q s‖ := by linarith
    have hquad_nonneg : 0 ≤ 1 - ‖q s‖ + ‖q s‖ ^ 2 := by
      nlinarith
    positivity
  have hpoly_decomp :
      1 + 3 * ‖q s‖ - 4 * ‖q s‖ ^ 2 + 4 * ‖q s‖ ^ 3 - 2 * ‖q s‖ ^ 4 =
        1 + ‖q s‖ + 2 * ‖q s‖ * (1 - ‖q s‖) * (1 - ‖q s‖ + ‖q s‖ ^ 2) := by
    ring
  have hpoly_pos :
      0 < 1 + 3 * ‖q s‖ - 4 * ‖q s‖ ^ 2 + 4 * ‖q s‖ ^ 3 - 2 * ‖q s‖ ^ 4 := by
    have hbase : 0 < 1 + ‖q s‖ := by
      linarith
    rw [hpoly_decomp]
    linarith
  have hmain :
      verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) -
          c2ExpandedQuartetResidualMargin s =
        ‖q s‖ ^ 2 *
            (1 + 3 * ‖q s‖ - 4 * ‖q s‖ ^ 2 + 4 * ‖q s‖ ^ 3 - 2 * ‖q s‖ ^ 4) *
            ((1 - ‖q s‖)⁻¹ * (1 - ‖q s‖)⁻¹) := by
    unfold verticalDepthTailUpper c2ExpandedQuartetResidualMargin
      c2ExpandedQuartetK2Margin c2QuartetBulkK2Lower c2QuartetVerticalTailUpper
    field_simp [hgap_ne]
    ring
  have hinv_sq_pos : 0 < (1 - ‖q s‖)⁻¹ * (1 - ‖q s‖)⁻¹ := by
    have hinv_pos : 0 < (1 - ‖q s‖)⁻¹ := inv_pos.mpr hgap_pos
    exact mul_pos hinv_pos hinv_pos
  have hsq_pos : 0 < ‖q s‖ ^ 2 := by
    positivity
  have hprod_pos :
      0 < ‖q s‖ ^ 2 *
          (1 + 3 * ‖q s‖ - 4 * ‖q s‖ ^ 2 + 4 * ‖q s‖ ^ 3 - 2 * ‖q s‖ ^ 4) *
          ((1 - ‖q s‖)⁻¹ * (1 - ‖q s‖)⁻¹) := by
    exact mul_pos (mul_pos hsq_pos hpoly_pos) hinv_sq_pos
  have hdiff_pos :
      0 < verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) -
          c2ExpandedQuartetResidualMargin s := by
    simpa [hmain] using hprod_pos
  linarith

theorem c2AnalyticBulkAllowance_sub_reserve_lt_scaledVerticalDepthTail_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s <
      verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) := by
  rw [← c2ExpandedQuartetResidualMargin_eq_analyticBulkAllowance_sub_reserve_of_offCriticalStrip hs]
  exact c2ExpandedQuartetResidualMargin_lt_scaledVerticalDepthTail_of_offCriticalStrip hs

lemma c2CanonicalClosedCutoffFiniteExactZetaUpper_nonneg_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    0 ≤ c2CanonicalClosedCutoffFiniteExactZetaUpper K M s := by
  have hdirect : 0 ≤ c2RectangularDirectFiniteUpper K M s :=
    c2RectangularDirectFiniteUpper_nonneg K M s
  have hbracket : 0 ≤ c2RectangularBracketFiniteUpper K M s :=
    c2RectangularBracketFiniteUpper_nonneg K M s
  have hcentral : 0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
    c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs.1
  unfold c2CanonicalClosedCutoffFiniteExactZetaUpper
  linarith

lemma c2CanonicalClosedVerticalFiniteExactZetaUpper_nonneg_of_offCriticalStrip
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    0 ≤ c2CanonicalClosedVerticalFiniteExactZetaUpper K M s := by
  have htail : 0 ≤ verticalDepthTailUpper s :=
    verticalDepthTailUpper_nonneg_of_re_pos s hs.1
  have hdirect : 0 ≤ c2RectangularDirectFiniteUpper K M s :=
    c2RectangularDirectFiniteUpper_nonneg K M s
  have hbracket : 0 ≤ c2RectangularBracketFiniteUpper K M s :=
    c2RectangularBracketFiniteUpper_nonneg K M s
  have hcentral : 0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
    c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs.1
  unfold c2CanonicalClosedVerticalFiniteExactZetaUpper
  linarith


theorem scaledVerticalDepthTail_le_c2CanonicalClosedScaledResidualFiniteExactZetaUpper_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s)
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_lt_one : horizontalRatio s < 1) :
    verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) ≤
      c2CanonicalClosedScaledResidualFiniteExactZetaUpper
        K M horizontalConstant horizontalScale horizontalRatio s := by
  have hq_lt : ‖q s‖ < 1 := q_norm_lt_one_of_offCriticalStrip s hs
  have hgap_nonneg : 0 ≤ 1 - ‖q s‖ := by
    linarith [norm_nonneg (q s), hq_lt]
  have hcoeff_nonneg : 0 ≤ 2 * (1 - ‖q s‖)⁻¹ := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (inv_nonneg.mpr hgap_nonneg)
  have hvert_tail_le :
      verticalDepthTailUpper s ≤ c2CanonicalClosedVerticalFiniteExactZetaUpper K M s := by
    have hdirect : 0 ≤ c2RectangularDirectFiniteUpper K M s :=
      c2RectangularDirectFiniteUpper_nonneg K M s
    have hbracket : 0 ≤ c2RectangularBracketFiniteUpper K M s :=
      c2RectangularBracketFiniteUpper_nonneg K M s
    have hcentral : 0 ≤ c2ExplicitFiniteCoreCentralExactZetaScalarUpper s :=
      c2ExplicitFiniteCoreCentralExactZetaScalarUpper_nonneg_of_re_pos hs.1
    unfold c2CanonicalClosedVerticalFiniteExactZetaUpper
    linarith
  have hvertical :
      verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) ≤
        c2CanonicalClosedVerticalFiniteExactZetaUpper K M s *
          (2 * (1 - ‖q s‖)⁻¹) :=
    mul_le_mul_of_nonneg_right hvert_tail_le hcoeff_nonneg
  have hhorizontal_nonneg :
      0 ≤ c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s :=
    c2HorizontalRegularizedUpper_nonneg_of_pos hscale hconstant hratio_lt_one
  have hcutoff_nonneg :
      0 ≤ c2CanonicalClosedCutoffFiniteExactZetaUpper K M s :=
    c2CanonicalClosedCutoffFiniteExactZetaUpper_nonneg_of_offCriticalStrip K M hs
  unfold c2CanonicalClosedScaledResidualFiniteExactZetaUpper
  have hrest_nonneg :
      0 ≤ c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio s *
            (2 * (1 - ‖q s‖)⁻¹) +
          c2CanonicalClosedCutoffFiniteExactZetaUpper K M s := by
    exact add_nonneg (mul_nonneg hhorizontal_nonneg hcoeff_nonneg) hcutoff_nonneg
  linarith


theorem not_c2CanonicalClosedScaledResidualFiniteExactZetaUpper_lt_analyticResidual_of_offCriticalStrip
    {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s)
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_lt_one : horizontalRatio s < 1) :
    ¬ c2CanonicalClosedScaledResidualFiniteExactZetaUpper
          K M horizontalConstant horizontalScale horizontalRatio s <
        c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s := by
  intro hlt
  have htail_le :
      verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) ≤
        c2CanonicalClosedScaledResidualFiniteExactZetaUpper
          K M horizontalConstant horizontalScale horizontalRatio s :=
    scaledVerticalDepthTail_le_c2CanonicalClosedScaledResidualFiniteExactZetaUpper_of_offCriticalStrip
      hs hscale hconstant hratio_lt_one
  have htarget_lt :
      c2AnalyticBulkAllowance s - c2ExpandedQuartetResidualReserve s <
        verticalDepthTailUpper s * (2 * (1 - ‖q s‖)⁻¹) :=
    c2AnalyticBulkAllowance_sub_reserve_lt_scaledVerticalDepthTail_of_offCriticalStrip hs
  linarith

lemma c2CanonicalClosedVerticalUpper_nonneg_of_offCritical
    (K M : ℕ) {s : ℂ} (hs : offCriticalStrip s) :
    0 ≤ c2ContinuedVerticalResidualClosedUpper K M
      (c2RectangularGenuineDirectBracketUpper K M)
      c2ContinuedCentralExactUpper s :=
  c2ContinuedVerticalResidualClosedUpper_nonneg_of_bounds
    hs
    (c2RectangularGenuineBound_directBracket K M s)
    (c2ContinuedCentralBound_exact s)

lemma c2CanonicalClosedTiltConstant_nonneg_of_offCritical
    (K M : ℕ)
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ}
    {s : ℂ} (hs : offCriticalStrip s)
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_lt_one : horizontalRatio s < 1) :
    0 ≤ c2CanonicalClosedTiltConstant
      K M horizontalConstant horizontalScale horizontalRatio s := by
  have hvert :
      0 ≤ c2ContinuedVerticalResidualClosedUpper K M
        (c2RectangularGenuineDirectBracketUpper K M)
        c2ContinuedCentralExactUpper s :=
    c2CanonicalClosedVerticalUpper_nonneg_of_offCritical K M hs
  have hhorizontal :
      0 ≤ c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s :=
    c2HorizontalRegularizedUpper_nonneg_of_pos hscale hconstant hratio_lt_one
  have hgap : 0 ≤ 1 + ‖q s‖ := by
    positivity
  unfold c2CanonicalClosedTiltConstant
  exact mul_nonneg (add_nonneg hvert hhorizontal) hgap

/--
Closed-layer certificate with unit tilt/cutoff scales and canonical exact constants.
The only remaining inputs are the horizontal geometric budget and quartet dominance.
-/
structure C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ)
    (s : ℂ) : Prop where
  offCritical : offCriticalStrip s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  quartet_dominance :
    c2QuartetBulkGUpper
        (c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper
            (c2CanonicalClosedTiltConstant
              K M horizontalConstant horizontalScale horizontalRatio)
            (fun _ => (1 : ℝ)))
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio)) s +
      c2BulkEUpper
        (c2CutoffUpperFromScale
          (c2CanonicalClosedCutoffConstant K M)
          (fun _ => (1 : ℝ))) s <
        c2QuartetBulkK2Lower s * ((1 - ‖q s‖) * (1 + ‖q s‖ ^ 2))

def c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ) : Set ℂ :=
  {s | C2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledEstimates
    coreCutoff K M horizontalConstant horizontalScale horizontalRatio s}

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosed_mem_of_scaledRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedRegion
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ)) := by
  refine {
    offCritical := hs.offCritical
    tiltScale_pos := by norm_num
    tiltConstant_nonneg :=
      c2CanonicalClosedTiltConstant_nonneg_of_offCritical K M hs.offCritical
        hs.horizontalScale_pos hs.horizontalConstant_nonneg hs.horizontalRatio_lt_one
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := by
      unfold C2BalancingSeedFactorScaledBound c2CanonicalClosedTiltConstant
      simp
    cutoffScale_pos := by norm_num
    cutoff_closed_scaled_bound := by
      unfold c2CanonicalClosedCutoffConstant c2ContinuedCutoffClosedUpper
      simp
    quartet_dominance := hs.quartet_dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_scaledCanonicalClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ)) :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_canonicalClosedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosed_mem_of_scaledRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_scaledCanonicalClosedRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_canonicalClosedRegion
    (c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosed_mem_of_scaledRegion hs)

/-- Left side of the expanded exact-zeta seed scaled bound. -/
noncomputable def c2ExpandedSeedScaledLeft
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio tiltScale : ℂ → ℝ) :
    ℂ → ℝ :=
  fun s =>
    ((c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s +
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s) *
      (1 + ‖q s‖)) * tiltScale s

lemma c2ExpandedSeedScaledLeft_nonneg_of_re_pos
    (K M : ℕ)
    {horizontalConstant horizontalScale horizontalRatio tiltScale : ℂ → ℝ}
    {s : ℂ} (hs : 0 < s.re)
    (hscale : 0 < horizontalScale s)
    (hconstant : 0 ≤ horizontalConstant s)
    (hratio_lt_one : horizontalRatio s < 1)
    (htiltScale_nonneg : 0 ≤ tiltScale s) :
    0 ≤ c2ExpandedSeedScaledLeft
      K M horizontalConstant horizontalScale horizontalRatio tiltScale s := by
  have hvert :
      0 ≤ c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper K M s :=
    c2ExplicitFiniteCoreContinuedVerticalExactZetaScalarUpper_nonneg_of_re_pos
      K M hs
  have hhorizontal :
      0 ≤ c2HorizontalRegularizedUpper
        horizontalConstant horizontalScale horizontalRatio s :=
    c2HorizontalRegularizedUpper_nonneg_of_pos
      hscale hconstant hratio_lt_one
  have hgap : 0 ≤ 1 + ‖q s‖ := by
    positivity
  unfold c2ExpandedSeedScaledLeft
  exact mul_nonneg (mul_nonneg (add_nonneg hvert hhorizontal) hgap)
    htiltScale_nonneg

def C2ExpandedSeedScaledBound
    (K M : ℕ)
    (horizontalConstant horizontalScale horizontalRatio
      tiltConstant tiltScale : ℂ → ℝ) (s : ℂ) : Prop :=
  c2ExpandedSeedScaledLeft
      K M horizontalConstant horizontalScale horizontalRatio tiltScale s ≤
    tiltConstant s

/-- Left side of the expanded exact-zeta cutoff scaled bound. -/
noncomputable def c2ExpandedCutoffScaledLeft
    (K M : ℕ) (cutoffScale : ℂ → ℝ) : ℂ → ℝ :=
  fun s =>
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s *
      cutoffScale s

lemma c2ExpandedCutoffScaledLeft_nonneg_of_re_pos
    (K M : ℕ) {cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : 0 < s.re) (hscale_nonneg : 0 ≤ cutoffScale s) :
    0 ≤ c2ExpandedCutoffScaledLeft K M cutoffScale s := by
  have hcutoff :
      0 ≤ c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper K M s :=
    c2ExplicitFiniteCoreContinuedCutoffExactZetaScalarUpper_nonneg_of_re_pos
      K M hs
  unfold c2ExpandedCutoffScaledLeft
  exact mul_nonneg hcutoff hscale_nonneg

def C2ExpandedCutoffScaledBound
    (K M : ℕ) (cutoffConstant cutoffScale : ℂ → ℝ) (s : ℂ) : Prop :=
  c2ExpandedCutoffScaledLeft K M cutoffScale s ≤ cutoffConstant s

structure C2ExpandedExactZetaScalarEstimates
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  two_le_K : 2 ≤ K
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontalLayer_bound : ∀ j : ℕ,
    ‖c2ConcreteOddHorizontalLayerDefect coreCutoff s j‖ ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  seed_scaled_bound :
    C2ExpandedSeedScaledBound
      K M horizontalConstant horizontalScale horizontalRatio
      tiltConstant tiltScale s
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    C2ExpandedCutoffScaledBound K M cutoffConstant cutoffScale s
  dominance :
    C2ExpandedQuartetDominance
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale s

def c2ExpandedExactZetaScalarRegion
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2ExpandedExactZetaScalarEstimates
    coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2ExpandedScalar_mem_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    two_le_K := hs.two_le_K
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    balancing_seed_factor_scaled_bound := by
      simpa [C2ExpandedSeedScaledBound, c2ExpandedSeedScaledLeft] using
        hs.seed_scaled_bound
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_closed_scaled_bound := by
      simpa [C2ExpandedCutoffScaledBound, c2ExpandedCutoffScaledLeft] using
        hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetConcreteRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale :=
  c2OddTailContinuedBalancingSeedBulkQuartetConcrete_mem_of_expandedDominanceRegion
    (c2ExpandedScalar_mem_expandedDominanceRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaled_mem_of_expandedDominanceRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaDominanceRegion
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio := by
  exact {
    offCritical := hs.offCritical
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound := hs.horizontalLayer_bound
    quartet_dominance := by
      simpa [C2ExpandedQuartetDominance, c2ExpandedQuartetLeftUpper,
        c2ExpandedQuartetGUpper, c2ExpandedQuartetEUpper,
        c2ExpandedQuartetK2Margin] using hs.dominance
  }

theorem
    c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaled_mem_of_expandedScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {horizontalConstant horizontalScale horizontalRatio : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      (c2CanonicalClosedTiltConstant
        K M horizontalConstant horizontalScale horizontalRatio)
      (fun _ => (1 : ℝ))
      horizontalConstant horizontalScale horizontalRatio
      (c2CanonicalClosedCutoffConstant K M)
      (fun _ => (1 : ℝ))) :
    s ∈ c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaledRegion
      coreCutoff K M horizontalConstant horizontalScale horizontalRatio :=
  c2OddTailContinuedBalancingSeedBulkQuartetCanonicalClosedScaled_mem_of_expandedDominanceRegion
    (c2ExpandedScalar_mem_expandedDominanceRegion hs)

theorem
    c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedScalarRegion
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2ExpandedExactZetaScalarRegion
      coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M s ≠ 0 :=
  c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedDominanceRegion
    (c2ExpandedScalar_mem_expandedDominanceRegion hs)

noncomputable def c2ExpandedScalarBulkRegionData
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    C2OddTailContinuedBalancingSeedBulkModelBulkRegionData coreCutoff K M where
  bulk :=
    {
      F := c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M
      bulkRegion :=
        c2ExpandedExactZetaScalarRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale
      bulk_nonvanishing := by
        intro s hs
        exact
          c2OddTailContinuedBalancingSeedBulkModel_nonvanishing_of_mem_expandedScalarRegion
            hs
    }
  F_eq := rfl

theorem
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_expandedScalarCover
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ}
    (near : C2OddTailContinuedBalancingSeedBulkModelNearAxisData coreCutoff K M)
    (edge : C2OddTailContinuedBalancingSeedBulkModelEdgeData coreCutoff K M)
    (cover : ∀ s : ℂ, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ c2ExpandedExactZetaScalarRegion
          coreCutoff K M
          tiltConstant tiltScale
          horizontalConstant horizontalScale horizontalRatio
          cutoffConstant cutoffScale ∨
        s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact
    mathlibRiemannHypothesis_of_oddTailContinuedBalancingSeedBulkModel_bulkRegionCover
      near
      (c2ExpandedScalarBulkRegionData
        coreCutoff K M
        tiltConstant tiltScale
        horizontalConstant horizontalScale horizontalRatio
        cutoffConstant cutoffScale)
      edge
      cover

end C2
