import LeanC2.Route.BulkEstimates
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.AtTopBot.Group

namespace C2

/-- Partial odd Dirichlet channel using the first `N` odd positive integers. -/
noncomputable def oddDirichletPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, complexDirichletCoeff s (2 * n + 1)

/-- Tail of the odd Dirichlet channel after removing the first `N` odd terms. -/
noncomputable def oddDirichletTail (s : ℂ) (N : ℕ) : ℂ :=
  ∑' n : ℕ, complexDirichletCoeff s (2 * (n + N) + 1)

/-- Explicit real upper envelope for the odd Dirichlet tail in terms of `Re(s)`. -/
noncomputable def oddDirichletTailUpper (s : ℂ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, ((2 * (n + N) + 1 : ℝ) ^ (-s.re))

/-- Quantitative explicit upper bound for `oddDirichletTailUpper`. -/
noncomputable def oddDirichletTailExplicitUpper (s : ℂ) (N : ℕ) : ℝ :=
  ((2 * N + 1 : ℝ) ^ (-s.re)) +
    (2 : ℝ) ^ (-s.re) * (((N : ℝ) + (1 / 2 : ℝ)) ^ (1 - s.re) / (s.re - 1))

/-- Explicit upper envelope for the full odd Dirichlet channel (the case `N = 0`). -/
noncomputable def oddDirichletChannelExplicitUpper (s : ℂ) : ℝ :=
  oddDirichletTailExplicitUpper s 0

lemma integral_Ioi_add_rpow_of_lt {a c m : ℝ} (ha : a < -1) (hc : -m < c) :
    ∫ t : ℝ in Set.Ioi c, (t + m) ^ a = -((c + m) ^ (a + 1) / (a + 1)) := by
  have hd : ∀ x ∈ Set.Ici c,
      HasDerivAt (fun t => (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 ≠ 0 by linarith]
    · left
      linarith [Set.mem_Ici.mp hx, id_eq x]
  have ht : Filter.Tendsto (fun t => ((t + m) ^ (a + 1)) / (a + 1)) Filter.atTop
      (nhds (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))).comp
      (Filter.tendsto_atTop_add_const_right _ m Filter.tendsto_id) |>.div_const _
  simpa only [sub_eq_add_neg, neg_div, zero_div, zero_add] using
    (MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := c) (m := 0 / (a + 1)) hd
      (integrableOn_add_rpow_Ioi_of_lt ha hc) ht)

lemma integrableOn_Ioi_odd_rpow_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (N : ℕ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (2 * x + 1) ^ (-s.re)) (Set.Ioi (N : ℝ)) := by
  have hadd : MeasureTheory.IntegrableOn
      (fun x : ℝ => (x + (1 / 2 : ℝ)) ^ (-s.re)) (Set.Ioi (N : ℝ)) := by
    have hN : (0 : ℝ) ≤ N := by positivity
    exact integrableOn_add_rpow_Ioi_of_lt (a := -s.re) (c := N) (m := (1 / 2 : ℝ))
      (by linarith) (by linarith)
  refine MeasureTheory.IntegrableOn.congr_fun
    (hadd.const_mul ((2 : ℝ) ^ (-s.re))) ?_ measurableSet_Ioi
  intro x hx
  have hxhalf : 0 ≤ x + (1 / 2 : ℝ) := by
    linarith [Set.mem_Ioi.mp hx]
  calc
    (2 : ℝ) ^ (-s.re) * (x + (1 / 2 : ℝ)) ^ (-s.re)
      = (2 * (x + (1 / 2 : ℝ))) ^ (-s.re) := by
          rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hxhalf]
    _ = (2 * x + 1) ^ (-s.re) := by
          congr 1
          ring

lemma integral_Ioi_odd_rpow_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (N : ℕ) :
    ∫ x : ℝ in Set.Ioi (N : ℝ), (2 * x + 1) ^ (-s.re) =
      (2 : ℝ) ^ (-s.re) * (((N : ℝ) + (1 / 2 : ℝ)) ^ (1 - s.re) / (s.re - 1)) := by
  have hcongr :
      (∫ x : ℝ in Set.Ioi (N : ℝ), (2 * x + 1) ^ (-s.re)) =
        ∫ x : ℝ in Set.Ioi (N : ℝ),
          (2 : ℝ) ^ (-s.re) * (x + (1 / 2 : ℝ)) ^ (-s.re) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hxhalf : 0 ≤ x + (1 / 2 : ℝ) := by
      linarith [Set.mem_Ioi.mp hx]
    calc
      (2 * x + 1) ^ (-s.re)
        = (2 * (x + (1 / 2 : ℝ))) ^ (-s.re) := by
            congr 1
            ring
      _ = (2 : ℝ) ^ (-s.re) * (x + (1 / 2 : ℝ)) ^ (-s.re) := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hxhalf]
  rw [hcongr, MeasureTheory.integral_const_mul]
  have hN : (0 : ℝ) ≤ N := by positivity
  have hshift := integral_Ioi_add_rpow_of_lt (a := -s.re) (c := N) (m := (1 / 2 : ℝ))
    (by linarith) (by linarith)
  rw [hshift]
  rw [show -s.re + 1 = 1 - s.re by ring]
  rw [show 1 - s.re = -(s.re - 1) by ring]
  rw [div_neg]
  ring

lemma oddCoresUpTo_eq_image_range (M : ℕ) :
    oddCoresUpTo M = (Finset.range ((M + 1) / 2)).image (fun n : ℕ => 2 * n + 1) := by
  ext m
  constructor
  · intro hm
    rw [mem_oddCoresUpTo] at hm
    rcases hm.2 with ⟨n, rfl⟩
    exact Finset.mem_image.mpr ⟨n, by
      simp
      omega, rfl⟩
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, hEq⟩
    rw [mem_oddCoresUpTo]
    constructor
    · simp at hn
      omega
    · rw [← hEq]
      exact ⟨n, rfl⟩

lemma rectangularOddCoreSum_eq_oddDirichletPartialSum (s : ℂ) (M : ℕ) :
    rectangularOddCoreSum s M = oddDirichletPartialSum s ((M + 1) / 2) := by
  unfold rectangularOddCoreSum oddDirichletPartialSum
  rw [oddCoresUpTo_eq_image_range]
  rw [Finset.sum_image]
  · intro a _ha b _hb hab
    have hmul : 2 * a = 2 * b := by
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hmul

theorem oddDirichletChannel_eq_partial_add_tail_of_one_lt_re (s : ℂ) (hs : 1 < s.re)
    (N : ℕ) :
    oddDirichletChannel s = oddDirichletPartialSum s N + oddDirichletTail s N := by
  let f : ℕ → ℂ := fun n => complexDirichletCoeff s (2 * n + 1)
  have hf : Summable f := (summable_oddDirichletCoeff_norm_of_one_lt_re s hs).of_norm
  simpa [oddDirichletChannel, oddDirichletPartialSum, oddDirichletTail, f] using
    (hf.sum_add_tsum_nat_add N).symm

/--
Odd-channel truncation error written against the Euler target
`(1 - 2^{-s}) * ζ(s)`.
-/
noncomputable def c2ConcreteOddTruncationErrorEulerTarget
    (coreCutoff : ℕ → ℕ) : ℂ → ℕ → ℂ :=
  fun s j =>
    rectangularOddCoreSum s (coreCutoff j) -
      (1 - complexDirichletCoeff s 2) * riemannZeta s

theorem c2ConcreteOddTruncationError_eq_eulerTarget_of_one_lt_re
    (coreCutoff : ℕ → ℕ) {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    c2ConcreteOddTruncationError coreCutoff s j =
      c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j := by
  unfold c2ConcreteOddTruncationError c2OddTruncationError
    c2ConcreteOddTruncationErrorEulerTarget
  rw [oddDirichletChannel_eulerRelation_of_one_lt_re s hs]

theorem c2ConcreteOddTruncation_bound_of_eulerTarget
    {coreCutoff : ℕ → ℕ} {oddTruncationUpper : ℂ → ℕ → ℝ}
    {s : ℂ} (hs : 1 < s.re)
    (hbound : ∀ j : ℕ,
      ‖c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j‖ ≤
        oddTruncationUpper s j) :
    ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤
        oddTruncationUpper s j := by
  intro j
  rw [c2ConcreteOddTruncationError_eq_eulerTarget_of_one_lt_re coreCutoff hs j]
  exact hbound j

theorem c2ConcreteOddTruncationErrorEulerTarget_eq_neg_oddDirichletTail_of_one_lt_re
    (coreCutoff : ℕ → ℕ) {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j =
      -oddDirichletTail s ((coreCutoff j + 1) / 2) := by
  unfold c2ConcreteOddTruncationErrorEulerTarget
  rw [rectangularOddCoreSum_eq_oddDirichletPartialSum]
  rw [← oddDirichletChannel_eulerRelation_of_one_lt_re s hs]
  rw [oddDirichletChannel_eq_partial_add_tail_of_one_lt_re s hs ((coreCutoff j + 1) / 2)]
  ring

theorem c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailNorm_of_one_lt_re
    (coreCutoff : ℕ → ℕ) {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    ‖c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j‖ ≤
      ∑' n : ℕ, ‖complexDirichletCoeff s (2 * (n + ((coreCutoff j + 1) / 2)) + 1)‖ := by
  let N : ℕ := (coreCutoff j + 1) / 2
  have htail : Summable fun n : ℕ =>
      ‖complexDirichletCoeff s (2 * (n + N) + 1)‖ := by
    exact (summable_oddDirichletCoeff_norm_of_one_lt_re s hs).comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  rw [c2ConcreteOddTruncationErrorEulerTarget_eq_neg_oddDirichletTail_of_one_lt_re
    coreCutoff hs j, norm_neg]
  simpa [oddDirichletTail, N] using norm_tsum_le_tsum_norm htail

theorem c2ConcreteOddTruncation_bound_of_oddDirichletTailNorm
    {coreCutoff : ℕ → ℕ} {oddTruncationUpper : ℂ → ℕ → ℝ}
    {s : ℂ} (hs : 1 < s.re)
    (htail : ∀ j : ℕ,
      (∑' n : ℕ, ‖complexDirichletCoeff s
        (2 * (n + ((coreCutoff j + 1) / 2)) + 1)‖) ≤
        oddTruncationUpper s j) :
    ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j := by
  intro j
  rw [c2ConcreteOddTruncationError_eq_eulerTarget_of_one_lt_re coreCutoff hs j]
  exact le_trans
    (c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailNorm_of_one_lt_re
      coreCutoff hs j)
    (htail j)

theorem oddDirichletTailNorm_eq_upper (s : ℂ) (N : ℕ) :
    (∑' n : ℕ, ‖complexDirichletCoeff s (2 * (n + N) + 1)‖) = oddDirichletTailUpper s N := by
  unfold oddDirichletTailUpper
  apply tsum_congr
  intro n
  simpa [Nat.cast_add, Nat.cast_mul] using
    complexDirichletCoeff_norm_eq_rpow_neg_re s (by omega : 2 * (n + N) + 1 ≠ 0)

theorem oddDirichletChannel_norm_le_oddDirichletTailUpper_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    ‖oddDirichletChannel s‖ ≤ oddDirichletTailUpper s 0 := by
  have hsum : Summable fun n : ℕ => ‖complexDirichletCoeff s (2 * n + 1)‖ :=
    summable_oddDirichletCoeff_norm_of_one_lt_re s hs
  unfold oddDirichletChannel
  calc
    ‖∑' n : ℕ, complexDirichletCoeff s (2 * n + 1)‖
      ≤ ∑' n : ℕ, ‖complexDirichletCoeff s (2 * n + 1)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ = oddDirichletTailUpper s 0 := by
      simpa [oddDirichletTailUpper] using oddDirichletTailNorm_eq_upper s 0

theorem c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailUpper_of_one_lt_re
    (coreCutoff : ℕ → ℕ) {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    ‖c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j‖ ≤
      oddDirichletTailUpper s ((coreCutoff j + 1) / 2) := by
  rw [← oddDirichletTailNorm_eq_upper s ((coreCutoff j + 1) / 2)]
  exact c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailNorm_of_one_lt_re
    coreCutoff hs j

theorem c2ConcreteOddTruncation_bound_of_oddDirichletTailUpper
    {coreCutoff : ℕ → ℕ} {oddTruncationUpper : ℂ → ℕ → ℝ}
    {s : ℂ} (hs : 1 < s.re)
    (htail : ∀ j : ℕ,
      oddDirichletTailUpper s ((coreCutoff j + 1) / 2) ≤ oddTruncationUpper s j) :
    ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j := by
  intro j
  rw [c2ConcreteOddTruncationError_eq_eulerTarget_of_one_lt_re coreCutoff hs j]
  exact le_trans
    (c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailUpper_of_one_lt_re
      coreCutoff hs j)
    (htail j)

theorem oddDirichletTailUpper_le_explicit_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (N : ℕ) :
    oddDirichletTailUpper s N ≤ oddDirichletTailExplicitUpper s N := by
  unfold oddDirichletTailUpper oddDirichletTailExplicitUpper
  let f : ℕ → ℝ := fun n => ((2 * (n + N) + 1 : ℝ) ^ (-s.re))
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact Real.rpow_nonneg (by positivity) _
  have hpartial : ∀ M : ℕ, (∑ n ∈ Finset.range M, f n) ≤ oddDirichletTailExplicitUpper s N := by
    intro M
    cases M with
    | zero =>
        have h1 : 0 ≤ ((2 * N + 1 : ℝ) ^ (-s.re)) := by
          exact Real.rpow_nonneg (by positivity) _
        have h2 : 0 ≤ (2 : ℝ) ^ (-s.re) * (((N : ℝ) + (1 / 2 : ℝ)) ^ (1 - s.re) / (s.re - 1)) := by
          apply mul_nonneg
          · exact Real.rpow_nonneg (by positivity) _
          · apply div_nonneg
            · exact Real.rpow_nonneg (by positivity) _
            · linarith
        unfold oddDirichletTailExplicitUpper
        simp
        linarith
    | succ m =>
        have hanti : AntitoneOn (fun x : ℝ => (2 * x + 1) ^ (-s.re))
            (Set.Icc (N : ℝ) ((N : ℝ) + m)) := by
          intro x hx y hy hxy
          have hrpow := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -s.re) (by linarith)
          have hN : 0 ≤ (N : ℝ) := by positivity
          have hxpos : 0 < 2 * x + 1 := by nlinarith [hN, hx.1]
          have hypos : 0 < 2 * y + 1 := by nlinarith [hN, hy.1]
          exact hrpow hxpos hypos (by nlinarith)
        have hsum_rest :
            (∑ i ∈ Finset.range m, (2 * (N + (i + 1)) + 1 : ℝ) ^ (-s.re)) ≤
              ∫ x in (N : ℝ)..(N : ℝ) + m, (2 * x + 1) ^ (-s.re) := by
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul] using
            (hanti.sum_le_integral (x₀ := (N : ℝ)) (a := m))
        have hInt : MeasureTheory.IntegrableOn
            (fun x : ℝ => (2 * x + 1) ^ (-s.re)) (Set.Ioi (N : ℝ)) :=
          integrableOn_Ioi_odd_rpow_of_one_lt_re s hs N
        have htail_nonneg :
            0 ≤ ∫ x : ℝ in Set.Ioi ((N : ℝ) + m), (2 * x + 1) ^ (-s.re) := by
          apply MeasureTheory.integral_nonneg_of_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
          have hNm : 0 ≤ (N : ℝ) + m := by positivity
          exact Real.rpow_nonneg (by nlinarith [hNm, Set.mem_Ioi.mp hx]) _
        have hinterval_le :
            ∫ x in (N : ℝ)..(N : ℝ) + m, (2 * x + 1) ^ (-s.re) ≤
              ∫ x : ℝ in Set.Ioi (N : ℝ), (2 * x + 1) ^ (-s.re) := by
          have hm0 : (0 : ℝ) ≤ m := by positivity
          have hsub := intervalIntegral.integral_Ioi_sub_Ioi hInt
            (le_add_of_nonneg_right hm0)
          linarith
        calc
          ∑ n ∈ Finset.range (Nat.succ m), f n
            = ((2 * N + 1 : ℝ) ^ (-s.re)) +
                ∑ i ∈ Finset.range m, (2 * (N + (i + 1)) + 1 : ℝ) ^ (-s.re) := by
                  simpa [f, add_comm, add_left_comm, add_assoc] using
                    (Finset.sum_range_succ' (f := fun n : ℕ => f n) m)
          _ ≤ ((2 * N + 1 : ℝ) ^ (-s.re)) +
                ∫ x : ℝ in Set.Ioi (N : ℝ), (2 * x + 1) ^ (-s.re) := by
                  gcongr
                  exact le_trans hsum_rest hinterval_le
          _ = oddDirichletTailExplicitUpper s N := by
                rw [integral_Ioi_odd_rpow_of_one_lt_re s hs N]
                rfl
  exact Real.tsum_le_of_sum_range_le hf_nonneg hpartial

theorem oddDirichletChannel_norm_le_explicit_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    ‖oddDirichletChannel s‖ ≤ oddDirichletChannelExplicitUpper s := by
  unfold oddDirichletChannelExplicitUpper
  exact le_trans
    (oddDirichletChannel_norm_le_oddDirichletTailUpper_of_one_lt_re s hs)
    (oddDirichletTailUpper_le_explicit_of_one_lt_re s hs 0)

theorem c2ConcreteOddTruncation_bound_of_oddDirichletTailExplicitUpper
    {coreCutoff : ℕ → ℕ} {oddTruncationUpper : ℂ → ℕ → ℝ}
    {s : ℂ} (hs : 1 < s.re)
    (htail : ∀ j : ℕ,
      oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤ oddTruncationUpper s j) :
    ∀ j : ℕ,
      ‖c2ConcreteOddTruncationError coreCutoff s j‖ ≤ oddTruncationUpper s j := by
  exact c2ConcreteOddTruncation_bound_of_oddDirichletTailUpper hs (fun j =>
    le_trans (oddDirichletTailUpper_le_explicit_of_one_lt_re s hs ((coreCutoff j + 1) / 2))
      (htail j))

/--
Scalar estimates where the horizontal odd truncation estimate is supplied against
the Euler target `(1 - 2^{-s})ζ(s)` instead of `oddDirichletChannel`.
-/
structure C2BulkEulerOddScalarEstimates
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
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
  oddEulerTruncation_bound : ∀ j : ℕ,
    ‖c2ConcreteOddTruncationErrorEulerTarget coreCutoff s j‖ ≤
      oddTruncationUpper s j
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

def c2BulkEulerOddScalarEstimateRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (oddTruncationUpper : ℂ → ℕ → ℝ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkEulerOddScalarEstimates
    tiltLayerResidual coreCutoff K M oddTruncationUpper
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkEulerOddScalarEstimates_to_concrete_scalar
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkEulerOddScalarEstimateRegion
      tiltLayerResidual coreCutoff K M oddTruncationUpper
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteScalarEstimateRegion
      tiltLayerResidual coreCutoff K M oddTruncationUpper
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
    oddTruncation_bound :=
      c2ConcreteOddTruncation_bound_of_eulerTarget
        hs.one_lt_re hs.oddEulerTruncation_bound
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkEulerOddScalarEstimates_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {oddTruncationUpper : ℂ → ℕ → ℝ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkEulerOddScalarEstimateRegion
      tiltLayerResidual coreCutoff K M oddTruncationUpper
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteScalarEstimates_nonvanishing_of_mem
    (c2BulkEulerOddScalarEstimates_to_concrete_scalar hs)

/--
Scalar estimates where the odd truncation side is bounded directly by the explicit tail upper
`oddDirichletTailExplicitUpper`.
-/
structure C2BulkExplicitOddTailScalarEstimates
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
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
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltRegularizedUpper tiltConstant tiltScale tiltRatio s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2BulkExplicitOddTailScalarEstimateRegion
    (tiltLayerResidual : ℂ → ℕ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkExplicitOddTailScalarEstimates
    tiltLayerResidual coreCutoff K M
    tiltConstant tiltScale tiltRatio
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkExplicitOddTailScalarEstimates_to_euler_region
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkExplicitOddTailScalarEstimateRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkEulerOddScalarEstimateRegion
      tiltLayerResidual coreCutoff K M
      (fun s j => oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2))
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    one_lt_re := hs.one_lt_re
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
    oddEulerTruncation_bound := by
      intro j
      exact le_trans
        (c2ConcreteOddTruncationErrorEulerTarget_norm_le_oddDirichletTailUpper_of_one_lt_re
          coreCutoff hs.one_lt_re j)
        (oddDirichletTailUpper_le_explicit_of_one_lt_re s hs.one_lt_re ((coreCutoff j + 1) / 2))
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkExplicitOddTailScalarEstimates_nonvanishing_of_mem
    {tiltLayerResidual : ℂ → ℕ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkExplicitOddTailScalarEstimateRegion
      tiltLayerResidual coreCutoff K M
      tiltConstant tiltScale tiltRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual tiltLayerResidual)
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkEulerOddScalarEstimates_nonvanishing_of_mem
    (c2BulkExplicitOddTailScalarEstimates_to_euler_region hs)

/--
Fully scalar operational bulk estimates combining the scaled seeded tilt certificate
with the explicit odd-tail horizontal budget.
-/
structure C2BulkScaledSeededExplicitOddTailEstimates
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound : ‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_scaled_bound :
    ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2BulkScaledSeededExplicitOddTailRegion
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkScaledSeededExplicitOddTailEstimates
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkScaledSeededExplicitOddTailRegion_eq_empty
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale = ∅ := by
  ext s
  constructor
  · intro hs
    simpa using false_of_one_lt_re_offCritical hs.one_lt_re hs.offCritical
  · intro hs
    simp at hs

theorem c2BulkScaledSeededExplicitOddTail_mem_explicit_region
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkExplicitOddTailScalarEstimateRegion
      (c2SeededTiltLayerResidual tiltSeed) coreCutoff K M
      tiltConstant tiltScale c2TiltAnalyticRatio
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tiltRatio_nonneg := c2TiltAnalyticRatio_nonneg s
    tiltRatio_lt_one := c2TiltAnalyticRatio_lt_one_of_offCriticalStrip hs.offCritical
    tiltLayer_bound :=
      c2SeededTiltLayerResidual_bound
        (c2TiltSeed_bound_from_scaled hs.tiltScale_pos hs.tilt_scaled_bound)
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := by
      simpa [c2TiltAnalyticRegularizedUpper] using hs.dominance
  }

theorem c2BulkScaledSeededExplicitOddTail_mem_scaled_seeded_analytic_tilt_region
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkConcreteScaledSeededAnalyticTiltRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound := hs.tilt_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontalLayer_bound :=
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
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound := hs.cutoff_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkScaledSeededExplicitOddTail_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkExplicitOddTailScalarEstimates_nonvanishing_of_mem
    (c2BulkScaledSeededExplicitOddTail_mem_explicit_region hs)

theorem c2BulkScaledSeededExplicitOddTail_nonvanishing_of_mem_geometric_truncated
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkConcreteScaledSeededAnalyticTilt_nonvanishing_of_mem_geometric_truncated
    (tiltCutoff := tiltCutoff)
    (c2BulkScaledSeededExplicitOddTail_mem_scaled_seeded_analytic_tilt_region hs)

/--
Operational estimates where the rectangular cutoff is supplied against the
`c0 * ζ` target. In `Re(s) > 1` this is converted to the central cutoff target.
-/
structure C2BulkScaledSeededExplicitOddTailC0ZetaCutoffEstimates
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  offCritical : offCriticalStrip s
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound : ‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_c0Zeta_scaled_bound :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkScaledSeededExplicitOddTailC0ZetaCutoffEstimates
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

/--
Right-half-plane version of the explicit odd-tail cutoff estimates.

This is the usable bulk-right stage: it keeps the `Re(s) > 1` hypothesis needed by
the current `c0 * ζ` cutoff identity and does not mix it with `offCriticalStrip`.
-/
structure C2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtEstimates
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ)
    (s : ℂ) : Prop where
  one_lt_re : 1 < s.re
  tiltScale_pos : 0 < tiltScale s
  tiltConstant_nonneg : 0 ≤ tiltConstant s
  tilt_scaled_bound : ‖tiltSeed s‖ * tiltScale s ≤ tiltConstant s
  horizontalScale_pos : 0 < horizontalScale s
  horizontalConstant_nonneg : 0 ≤ horizontalConstant s
  horizontalRatio_nonneg : 0 ≤ horizontalRatio s
  horizontalRatio_lt_one : horizontalRatio s < 1
  horizontal_budget : ∀ j : ℕ,
    2 * ‖q s‖ ^ (j + 2) * oddDirichletTailExplicitUpper s ((coreCutoff j + 1) / 2) ≤
      (horizontalConstant s / horizontalScale s) * horizontalRatio s ^ j
  cutoffScale_pos : 0 < cutoffScale s
  cutoff_c0Zeta_scaled_bound :
    ‖c2ConcreteCutoffErrorC0Zeta K M s‖ * cutoffScale s ≤ cutoffConstant s
  dominance :
    c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s +
      c2HorizontalRegularizedUpper horizontalConstant horizontalScale horizontalRatio s +
      cutoffConstant s / cutoffScale s < c2AnalyticBulkAllowance s

def c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtRegion
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) : Set ℂ :=
  {s | C2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtEstimates
    tiltSeed coreCutoff K M
    tiltConstant tiltScale
    horizontalConstant horizontalScale horizontalRatio
    cutoffConstant cutoffScale s}

theorem c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLt_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffOneLtRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs.one_lt_re
  have hseed : ‖tiltSeed s‖ ≤ tiltConstant s / tiltScale s :=
    c2TiltSeed_bound_from_scaled hs.tiltScale_pos hs.tilt_scaled_bound
  have htiltLayer :
      ∀ j : ℕ,
        ‖c2SeededTiltLayerResidual tiltSeed s j‖ ≤
          (tiltConstant s / tiltScale s) * c2TiltAnalyticRatio s ^ j :=
    c2SeededTiltLayerResidual_bound hseed
  have htilt :
      ‖c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed) s‖ ≤
        c2TiltAnalyticRegularizedUpper tiltConstant tiltScale s :=
    c2TiltRegularizedResidual_bound_of_analytic_geometric_of_re_pos
      hs0 hs.tiltScale_pos hs.tiltConstant_nonneg htiltLayer
  have hhorizontalLayer :
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
      ‖c2ConcreteOddHorizontalDefect coreCutoff s‖ ≤
        c2HorizontalRegularizedUpper
          horizontalConstant horizontalScale horizontalRatio s := by
    unfold c2ConcreteOddHorizontalDefect
    exact c2HorizontalRegularizedDefect_bound
      hs.horizontalScale_pos hs.horizontalConstant_nonneg
      hs.horizontalRatio_nonneg hs.horizontalRatio_lt_one
      hhorizontalLayer
  have hcutoffScaled :
      ‖c2ConcreteCutoffError K M s‖ * cutoffScale s ≤ cutoffConstant s :=
    c2ConcreteCutoff_scaled_bound_of_c0Zeta
      hs.one_lt_re hs.cutoff_c0Zeta_scaled_bound
  have hcutoff :
      ‖c2BulkEdelta (c2ConcreteCutoffError K M) s‖ ≤
        c2CutoffUpperFromScale cutoffConstant cutoffScale s := by
    simpa [c2BulkEdelta] using
      c2Cutoff_bound_from_scaled hs.cutoffScale_pos hcutoffScaled
  have hG :
      ‖c2BulkGdelta
          (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
          (c2ConcreteOddHorizontalDefect coreCutoff) s‖ ≤
        c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio) s := by
    unfold c2BulkGdelta c2BulkGUpper
    exact le_trans (norm_add_le _ _) (add_le_add htilt hhorizontal)
  have hdom :
      c2BulkGUpper
          (c2TiltAnalyticRegularizedUpper tiltConstant tiltScale)
          (c2HorizontalRegularizedUpper
            horizontalConstant horizontalScale horizontalRatio) s +
        c2CutoffUpperFromScale cutoffConstant cutoffScale s <
          c2AnalyticBulkAllowance s := by
    simpa [c2BulkGUpper, c2CutoffUpperFromScale] using hs.dominance
  exact c2AnalyticBulk_nonvanishing_of_re_pos hs0 hG hcutoff hdom

theorem c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion_eq_empty
    (tiltSeed : ℂ → ℂ)
    (coreCutoff : ℕ → ℕ) (K M : ℕ)
    (tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ) :
    c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale = ∅ := by
  ext s
  constructor
  · intro hs
    simpa using false_of_one_lt_re_offCritical hs.one_lt_re hs.offCritical
  · intro hs
    simp at hs

theorem c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_mem_region
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    s ∈ c2BulkScaledSeededExplicitOddTailRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale := by
  exact {
    one_lt_re := hs.one_lt_re
    offCritical := hs.offCritical
    tiltScale_pos := hs.tiltScale_pos
    tiltConstant_nonneg := hs.tiltConstant_nonneg
    tilt_scaled_bound := hs.tilt_scaled_bound
    horizontalScale_pos := hs.horizontalScale_pos
    horizontalConstant_nonneg := hs.horizontalConstant_nonneg
    horizontalRatio_nonneg := hs.horizontalRatio_nonneg
    horizontalRatio_lt_one := hs.horizontalRatio_lt_one
    horizontal_budget := hs.horizontal_budget
    cutoffScale_pos := hs.cutoffScale_pos
    cutoff_scaled_bound :=
      c2ConcreteCutoff_scaled_bound_of_c0Zeta
        hs.one_lt_re hs.cutoff_c0Zeta_scaled_bound
    dominance := hs.dominance
  }

theorem c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_nonvanishing_of_mem
    {tiltSeed : ℂ → ℂ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkScaledSeededExplicitOddTail_nonvanishing_of_mem
    (c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_mem_region hs)

theorem c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_nonvanishing_of_mem_geometric_truncated
    {tiltSeed : ℂ → ℂ}
    {tiltCutoff : ℂ → ℕ}
    {coreCutoff : ℕ → ℕ} {K M : ℕ}
    {tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale : ℂ → ℝ} {s : ℂ}
    (hs : s ∈ c2BulkScaledSeededExplicitOddTailC0ZetaCutoffRegion
      tiltSeed coreCutoff K M
      tiltConstant tiltScale
      horizontalConstant horizontalScale horizontalRatio
      cutoffConstant cutoffScale) :
    c2AnalyticBulkF
      (c2BulkGdelta
        (c2TiltRegularizedResidual (c2SeededTiltLayerResidual tiltSeed))
        (c2ConcreteOddHorizontalDefect coreCutoff))
      (c2BulkEdelta (c2ConcreteCutoffError K M)) s ≠ 0 := by
  exact c2BulkScaledSeededExplicitOddTail_nonvanishing_of_mem_geometric_truncated
    (tiltCutoff := tiltCutoff)
    (c2BulkScaledSeededExplicitOddTailC0ZetaCutoff_mem_region hs)

end C2
