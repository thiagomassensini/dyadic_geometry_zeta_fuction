import LeanC2.Roadmap

namespace C2

/-- The resolvent allowance available to absorb the bulk errors. -/
noncomputable def c2AnalyticBulkAllowance (s : ℂ) : ℝ :=
  ‖q s‖ ^ 2 / (1 + ‖q s‖)

/-- Positive margin after subtracting the analytic bulk error bounds. -/
noncomputable def c2AnalyticBulkMargin (GUpper EUpper : ℂ → ℝ) (s : ℂ) : ℝ :=
  c2AnalyticBulkAllowance s - (GUpper s + EUpper s)

/--
Bulk region for the real analytic decomposition:

* the point is off-critical;
* `Gdelta` and `Edelta` are controlled by the supplied upper bounds;
* the sum of upper bounds is strictly dominated by the vertical C2 allowance.
-/
def c2AnalyticBulkRegion
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) : Set ℂ :=
  {s | offCriticalStrip s ∧
    ‖Gdelta s‖ ≤ GUpper s ∧
    ‖Edelta s‖ ≤ EUpper s ∧
    GUpper s + EUpper s < c2AnalyticBulkAllowance s}

/-- The real bulk target: vertical resolvent term plus analytic errors. -/
noncomputable def c2AnalyticBulkF (Gdelta Edelta : ℂ → ℂ) : GenuineNumerator :=
  fun s => verticalDepthTailFromTwo s + Gdelta s + Edelta s

/-- The resolvent-side term before the external error is added. -/
noncomputable def c2AnalyticBulkKdelta (Gdelta : ℂ → ℂ) : ℂ → ℂ :=
  fun s => verticalDepthTailFromTwo s + Gdelta s

/-- The depth-two numerator `K₂ = q²`. -/
noncomputable def c2AnalyticBulkK2 (s : ℂ) : ℂ :=
  q s ^ 2

/-- Sharp lower bound for the depth-two numerator. -/
noncomputable def c2AnalyticBulkK2Lower (s : ℂ) : ℝ :=
  ‖q s‖ ^ 2

theorem c2AnalyticBulk_margin_pos_of_mem
    {Gdelta Edelta : ℂ → ℂ} {GUpper EUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2AnalyticBulkRegion Gdelta Edelta GUpper EUpper) :
    0 < c2AnalyticBulkMargin GUpper EUpper s := by
  unfold c2AnalyticBulkMargin
  linarith [hs.2.2.2]

theorem c2AnalyticBulk_resolvent_shape
    {Gdelta Edelta : ℂ → ℂ} {GUpper EUpper : ℂ → ℝ}
    {s : ℂ} (hs : s ∈ c2AnalyticBulkRegion Gdelta Edelta GUpper EUpper) :
    c2AnalyticBulkKdelta Gdelta s =
      c2AnalyticBulkK2 s / (1 - q s) + Gdelta s := by
  unfold c2AnalyticBulkKdelta c2AnalyticBulkK2
  rw [verticalDepthTailFromTwo_eq s hs.1.1]
  unfold verticalResolvent q
  rw [div_eq_mul_inv]

theorem c2AnalyticBulk_resolvent_shape_of_re_pos
    (Gdelta : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    c2AnalyticBulkKdelta Gdelta s =
      c2AnalyticBulkK2 s / (1 - q s) + Gdelta s := by
  unfold c2AnalyticBulkKdelta c2AnalyticBulkK2
  rw [verticalDepthTailFromTwo_eq s hs]
  unfold verticalResolvent q
  rw [div_eq_mul_inv]

theorem c2AnalyticBulk_decomposition
    (Gdelta Edelta : ℂ → ℂ) (s : ℂ) :
    c2AnalyticBulkF Gdelta Edelta s =
      c2AnalyticBulkKdelta Gdelta s + Edelta s := by
  unfold c2AnalyticBulkF c2AnalyticBulkKdelta
  ring

theorem c2AnalyticBulk_K2Lower_eq_norm (s : ℂ) :
    c2AnalyticBulkK2Lower s = ‖c2AnalyticBulkK2 s‖ := by
  unfold c2AnalyticBulkK2Lower c2AnalyticBulkK2
  rw [norm_pow]

/--
Concrete `RegionalVerticalBulkBoundsData` for the real analytic bulk shape with
nonzero analytic errors `Gdelta` and `Edelta`.

The region itself stores the upper-bound hypotheses and the strict dominance margin.
-/
noncomputable def c2AnalyticBulkBoundsData
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) :
    RegionalVerticalBulkBoundsData where
  F := c2AnalyticBulkF Gdelta Edelta
  bulkRegion := c2AnalyticBulkRegion Gdelta Edelta GUpper EUpper
  Kdelta := c2AnalyticBulkKdelta Gdelta
  K2 := c2AnalyticBulkK2
  Gdelta := Gdelta
  Edelta := Edelta
  K2Lower := c2AnalyticBulkK2Lower
  GUpper := GUpper
  EUpper := EUpper
  bulk_offCritical := by
    intro _s hs
    exact hs.1
  decomposition := by
    intro s _hs
    exact c2AnalyticBulk_decomposition Gdelta Edelta s
  resolvent_shape := by
    intro _s hs
    exact c2AnalyticBulk_resolvent_shape hs
  K2_lower := by
    intro s _hs
    rw [c2AnalyticBulk_K2Lower_eq_norm]
  G_upper := by
    intro _s hs
    exact hs.2.1
  E_upper := by
    intro _s hs
    exact hs.2.2.1
  dominance_bounds := by
    intro s hs
    exact hs.2.2.2

noncomputable def c2AnalyticBulkRouteData
    (Gdelta Edelta : ℂ → ℂ) (GUpper EUpper : ℂ → ℝ) :
    RegionalVerticalBulkRouteData :=
  (c2AnalyticBulkBoundsData Gdelta Edelta GUpper EUpper).toRouteData

theorem c2AnalyticBulk_nonvanishing_of_mem
    {Gdelta Edelta : ℂ → ℂ} {GUpper EUpper : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2AnalyticBulkRegion Gdelta Edelta GUpper EUpper) :
    c2AnalyticBulkF Gdelta Edelta s ≠ 0 := by
  exact regionalVerticalBulk_nonvanishing_of_bounds
    (c2AnalyticBulkBoundsData Gdelta Edelta GUpper EUpper) hs

theorem c2AnalyticBulk_nonvanishing_of_re_pos
    {Gdelta Edelta : ℂ → ℂ} {GUpper EUpper : ℂ → ℝ} {s : ℂ}
    (hs : 0 < s.re)
    (hG : ‖Gdelta s‖ ≤ GUpper s)
    (hE : ‖Edelta s‖ ≤ EUpper s)
    (hdom : GUpper s + EUpper s < c2AnalyticBulkAllowance s) :
    c2AnalyticBulkF Gdelta Edelta s ≠ 0 := by
  refine no_zero_of_resolvent_dominance_at s
    (F := c2AnalyticBulkF Gdelta Edelta)
    (Kdelta := c2AnalyticBulkKdelta Gdelta)
    (K2 := c2AnalyticBulkK2)
    (q := q)
    (Gdelta := Gdelta)
    (Edelta := Edelta)
    (c2AnalyticBulk_decomposition Gdelta Edelta s)
    (c2AnalyticBulk_resolvent_shape_of_re_pos Gdelta hs)
    ?_ ?_
  · calc
      ‖c2AnalyticBulkK2 s‖ / (1 + ‖q s‖)
          = ‖c2AnalyticBulkK2 s‖ * (1 / (1 + ‖q s‖)) := by ring
      _ ≤ ‖c2AnalyticBulkK2 s‖ * ‖1 / (1 - q s)‖ := by
          exact mul_le_mul_of_nonneg_left
            (resolvent_lower_bound_of_re_pos s hs)
            (norm_nonneg _)
      _ = ‖c2AnalyticBulkK2 s / (1 - q s)‖ := by
          simp [div_eq_mul_inv]
  · have hGE : ‖Gdelta s‖ + ‖Edelta s‖ ≤ GUpper s + EUpper s :=
      add_le_add hG hE
    have hdom' :
        GUpper s + EUpper s < c2AnalyticBulkK2Lower s / (1 + ‖q s‖) := by
      simpa [c2AnalyticBulkAllowance, c2AnalyticBulkK2Lower] using hdom
    rw [c2AnalyticBulk_K2Lower_eq_norm] at hdom'
    exact lt_of_le_of_lt hGE hdom'

end C2
