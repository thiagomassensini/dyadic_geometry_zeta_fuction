import LeanC2.Roadmap

namespace C2

lemma q_ne_zero (s : ℂ) : q s ≠ 0 := by
  unfold q verticalRatio
  exact complexDirichletDepthRatio_ne_zero s

/-- The actual C2 vertical tail used as a pure resolvent bulk model. -/
noncomputable def c2VerticalResolventBulkF : GenuineNumerator :=
  verticalDepthTailFromTwo

/-- The pure vertical bulk is valid on the whole off-critical strip. -/
def c2VerticalResolventBulkRegion : Set ℂ :=
  {s | offCriticalStrip s}

/-- Main bulk term before splitting into the explicit resolvent. -/
noncomputable def c2VerticalResolventBulkKdelta : ℂ → ℂ :=
  verticalDepthTailFromTwo

/-- The depth-two numerator `K₂ = q²` for the vertical C2 resolvent. -/
noncomputable def c2VerticalResolventBulkK2 (s : ℂ) : ℂ :=
  q s ^ 2

/-- The pure vertical model has no auxiliary resolvent error. -/
noncomputable def c2VerticalResolventBulkGdelta : ℂ → ℂ :=
  fun _ => 0

/-- The pure vertical model has no external error. -/
noncomputable def c2VerticalResolventBulkEdelta : ℂ → ℂ :=
  fun _ => 0

/-- Sharp scalar lower bound for the pure vertical numerator. -/
noncomputable def c2VerticalResolventBulkK2Lower (s : ℂ) : ℝ :=
  ‖q s‖ ^ 2

noncomputable def c2VerticalResolventBulkGUpper : ℂ → ℝ :=
  fun _ => 0

noncomputable def c2VerticalResolventBulkEUpper : ℂ → ℝ :=
  fun _ => 0

theorem c2VerticalResolventBulk_resolvent_shape
    (s : ℂ) (hs : offCriticalStrip s) :
    c2VerticalResolventBulkKdelta s =
      c2VerticalResolventBulkK2 s / (1 - q s) + c2VerticalResolventBulkGdelta s := by
  unfold c2VerticalResolventBulkKdelta c2VerticalResolventBulkK2
    c2VerticalResolventBulkGdelta
  rw [verticalDepthTailFromTwo_eq s hs.1]
  unfold verticalResolvent q
  rw [div_eq_mul_inv]
  ring

theorem c2VerticalResolventBulk_K2Lower_eq_norm (s : ℂ) :
    c2VerticalResolventBulkK2Lower s = ‖c2VerticalResolventBulkK2 s‖ := by
  unfold c2VerticalResolventBulkK2Lower c2VerticalResolventBulkK2
  rw [norm_pow]

theorem c2VerticalResolventBulk_dominance_bounds
    (s : ℂ) (_hs : s ∈ c2VerticalResolventBulkRegion) :
    c2VerticalResolventBulkGUpper s + c2VerticalResolventBulkEUpper s <
      c2VerticalResolventBulkK2Lower s / (1 + ‖q s‖) := by
  have hqpos : 0 < ‖q s‖ := norm_pos_iff.mpr (q_ne_zero s)
  have hnum : 0 < ‖q s‖ ^ 2 := pow_pos hqpos 2
  have hden : 0 < 1 + ‖q s‖ := by positivity
  have hpos : 0 < ‖q s‖ ^ 2 / (1 + ‖q s‖) := div_pos hnum hden
  simpa [c2VerticalResolventBulkGUpper, c2VerticalResolventBulkEUpper,
    c2VerticalResolventBulkK2Lower] using hpos

/--
Concrete instantiation of `RegionalVerticalBulkBoundsData` with the real C2 vertical
resolvent: `verticalDepthTailFromTwo(s) = q(s)^2 / (1 - q(s))`.
-/
noncomputable def c2VerticalResolventBulkBoundsData : RegionalVerticalBulkBoundsData where
  F := c2VerticalResolventBulkF
  bulkRegion := c2VerticalResolventBulkRegion
  Kdelta := c2VerticalResolventBulkKdelta
  K2 := c2VerticalResolventBulkK2
  Gdelta := c2VerticalResolventBulkGdelta
  Edelta := c2VerticalResolventBulkEdelta
  K2Lower := c2VerticalResolventBulkK2Lower
  GUpper := c2VerticalResolventBulkGUpper
  EUpper := c2VerticalResolventBulkEUpper
  bulk_offCritical := by
    intro s hs
    exact hs
  decomposition := by
    intro _s _hs
    simp [c2VerticalResolventBulkF, c2VerticalResolventBulkKdelta,
      c2VerticalResolventBulkEdelta]
  resolvent_shape := by
    intro s hs
    exact c2VerticalResolventBulk_resolvent_shape s hs
  K2_lower := by
    intro s _hs
    rw [c2VerticalResolventBulk_K2Lower_eq_norm]
  G_upper := by
    intro _s _hs
    simp [c2VerticalResolventBulkGdelta, c2VerticalResolventBulkGUpper]
  E_upper := by
    intro _s _hs
    simp [c2VerticalResolventBulkEdelta, c2VerticalResolventBulkEUpper]
  dominance_bounds := by
    intro s hs
    exact c2VerticalResolventBulk_dominance_bounds s hs

noncomputable def c2VerticalResolventBulkRouteData : RegionalVerticalBulkRouteData :=
  c2VerticalResolventBulkBoundsData.toRouteData

theorem c2VerticalResolventBulk_nonvanishing_of_offCriticalStrip
    {s : ℂ} (hs : offCriticalStrip s) :
    c2VerticalResolventBulkF s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    c2VerticalResolventBulkBoundsData hs

end C2
