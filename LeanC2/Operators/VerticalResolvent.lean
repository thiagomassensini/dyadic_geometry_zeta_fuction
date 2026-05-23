import LeanC2.Operators.ComplexDirichlet
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace C2

/-- Vertical C2 ratio `q(s) = 2^{-1} * 2^{-s}` in the positive-real branch. -/
noncomputable def verticalRatio (s : ℂ) : ℂ :=
  depthGeometricRatio (complexDirichletCoeff s 2)

/-- Roadmap notation for the vertical geometric ratio. -/
noncomputable abbrev q (s : ℂ) : ℂ :=
  verticalRatio s

/-- Resolvent of the vertical geometric tower. -/
noncomputable def verticalResolvent (s : ℂ) : ℂ :=
  (1 - verticalRatio s)⁻¹

lemma verticalRatio_eq (s : ℂ) :
    verticalRatio s = (1 / 2 : ℂ) * complexDirichletCoeff s 2 := by
  unfold verticalRatio
  exact complexDirichletDepthRatio_eq s

lemma verticalRatio_norm (s : ℂ) :
    ‖verticalRatio s‖ = (1 / 2 : ℝ) * Real.exp (-(s.re * Real.log (2 : ℝ))) := by
  unfold verticalRatio
  exact complexDirichletDepthRatio_norm s

lemma verticalRatio_norm_lt_one_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ‖verticalRatio s‖ < 1 := by
  unfold verticalRatio
  exact complexDirichletDepthRatio_norm_lt_one_of_re_pos s hs

lemma verticalRatio_norm_lt_one_of_offCriticalStrip (s : ℂ) (hs : offCriticalStrip s) :
    ‖verticalRatio s‖ < 1 :=
  verticalRatio_norm_lt_one_of_re_pos s hs.1

lemma q_norm_lt_one_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ‖q s‖ < 1 :=
  verticalRatio_norm_lt_one_of_re_pos s hs

lemma q_norm_lt_one_of_offCriticalStrip (s : ℂ) (hs : offCriticalStrip s) :
    ‖q s‖ < 1 :=
  verticalRatio_norm_lt_one_of_offCriticalStrip s hs

lemma verticalRatio_ne_one_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    verticalRatio s ≠ 1 := by
  unfold verticalRatio
  exact complexDirichletDepthRatio_ne_one_of_re_pos s hs

lemma verticalResolvent_den_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    1 - verticalRatio s ≠ 0 := by
  have hq : verticalRatio s ≠ 1 := verticalRatio_ne_one_of_re_pos s hs
  intro hzero
  exact hq (sub_eq_zero.mp hzero).symm

lemma summable_vertical_geometric_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    Summable fun j : Nat => verticalRatio s ^ j := by
  exact summable_geometric_of_norm_lt_one (verticalRatio_norm_lt_one_of_re_pos s hs)

lemma vertical_geometric_tsum_eq_resolvent (s : ℂ) (hs : 0 < s.re) :
    (∑' j : Nat, verticalRatio s ^ j) = verticalResolvent s := by
  unfold verticalResolvent
  exact tsum_geometric_of_norm_lt_one (verticalRatio_norm_lt_one_of_re_pos s hs)

lemma vertical_geometric_tsum_eq_resolvent_of_offCriticalStrip
    (s : ℂ) (hs : offCriticalStrip s) :
    (∑' j : Nat, verticalRatio s ^ j) = verticalResolvent s :=
  vertical_geometric_tsum_eq_resolvent s hs.1

/-- Geometric resolvent in the roadmap notation `q(s)`. -/
lemma geom_resolvent (s : ℂ) (h : ‖q s‖ < 1) :
    (∑' j : Nat, q s ^ j) = 1 / (1 - q s) := by
  simpa [q, one_div] using (tsum_geometric_of_norm_lt_one h :
    (∑' j : Nat, verticalRatio s ^ j) = (1 - verticalRatio s)⁻¹)

lemma geom_resolvent_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    (∑' j : Nat, q s ^ j) = 1 / (1 - q s) :=
  geom_resolvent s (q_norm_lt_one_of_re_pos s hs)

lemma geom_resolvent_of_offCriticalStrip (s : ℂ) (hs : offCriticalStrip s) :
    (∑' j : Nat, q s ^ j) = 1 / (1 - q s) :=
  geom_resolvent s (q_norm_lt_one_of_offCriticalStrip s hs)

/-- Infinite vertical depth factor starting at C2 depth `2`. -/
noncomputable def verticalDepthTailFromTwo (s : ℂ) : ℂ :=
  ∑' j : Nat, verticalRatio s ^ (j + 2)

lemma verticalDepthTailFromTwo_eq (s : ℂ) (hs : 0 < s.re) :
    verticalDepthTailFromTwo s = verticalRatio s ^ 2 * verticalResolvent s := by
  unfold verticalDepthTailFromTwo
  simp_rw [pow_add]
  rw [tsum_mul_right]
  rw [vertical_geometric_tsum_eq_resolvent s hs]
  ring

lemma verticalResolvent_norm_le_geometric_upper_of_re_pos
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

lemma verticalDepthTailFromTwo_eq_of_offCriticalStrip
    (s : ℂ) (hs : offCriticalStrip s) :
    verticalDepthTailFromTwo s = verticalRatio s ^ 2 * verticalResolvent s :=
  verticalDepthTailFromTwo_eq s hs.1

/-- Explicit geometric upper bound for the vertical tail `∑_{k≥2} q(s)^k`. -/
noncomputable def verticalDepthTailUpper (s : ℂ) : ℝ :=
  ‖q s‖ ^ 2 / (1 - ‖q s‖)

lemma verticalDepthTailUpper_nonneg_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    0 ≤ verticalDepthTailUpper s := by
  unfold verticalDepthTailUpper
  have hden : 0 ≤ 1 - ‖q s‖ := by
    have hq_lt_one : ‖q s‖ < 1 := q_norm_lt_one_of_re_pos s hs
    linarith [norm_nonneg (q s)]
  exact div_nonneg (by positivity) hden

lemma verticalDepthTailFromTwo_norm_le_upper_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ‖verticalDepthTailFromTwo s‖ ≤ verticalDepthTailUpper s := by
  have hq_nonneg : 0 ≤ ‖q s‖ := norm_nonneg _
  have hq_lt_one : ‖q s‖ < 1 := q_norm_lt_one_of_re_pos s hs
  have hgeom : Summable fun j : ℕ => ‖q s‖ ^ j :=
    summable_geometric_of_lt_one hq_nonneg hq_lt_one
  have hgeomTail : Summable fun j : ℕ => ‖q s‖ ^ (j + 2) :=
    hgeom.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  have htail : Summable fun j : ℕ => ‖verticalRatio s ^ (j + 2)‖ :=
    hgeomTail.congr (by
      intro j
      simp [q, norm_pow])
  calc
    ‖verticalDepthTailFromTwo s‖
      ≤ ∑' j : ℕ, ‖verticalRatio s ^ (j + 2)‖ :=
        norm_tsum_le_tsum_norm htail
    _ = ∑' j : ℕ, ‖q s‖ ^ (j + 2) := by
      apply tsum_congr
      intro j
      simp [q, norm_pow]
    _ = ∑' j : ℕ, ‖q s‖ ^ 2 * ‖q s‖ ^ j := by
      apply tsum_congr
      intro j
      rw [Nat.add_comm j 2, pow_add]
    _ = ‖q s‖ ^ 2 * ∑' j : ℕ, ‖q s‖ ^ j := by
      rw [tsum_mul_left]
    _ = ‖q s‖ ^ 2 * (1 - ‖q s‖)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one]
    _ = verticalDepthTailUpper s := by
      unfold verticalDepthTailUpper
      rw [div_eq_mul_inv]

lemma verticalDepthTailFromTwo_norm_le_upper_of_offCriticalStrip
    (s : ℂ) (hs : offCriticalStrip s) :
    ‖verticalDepthTailFromTwo s‖ ≤ verticalDepthTailUpper s :=
  verticalDepthTailFromTwo_norm_le_upper_of_re_pos s hs.1

lemma verticalResolvent_norm_lower_bound_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    (1 / (1 + ‖verticalRatio s‖) : ℝ) ≤ ‖verticalResolvent s‖ := by
  have hden_ne : 1 - verticalRatio s ≠ 0 := verticalResolvent_den_ne_zero_of_re_pos s hs
  have hden_pos : 0 < ‖(1 : ℂ) - verticalRatio s‖ := norm_pos_iff.mpr hden_ne
  have hle : ‖(1 : ℂ) - verticalRatio s‖ ≤ 1 + ‖verticalRatio s‖ := by
    calc
      ‖(1 : ℂ) - verticalRatio s‖ ≤ ‖(1 : ℂ)‖ + ‖verticalRatio s‖ := norm_sub_le _ _
      _ = 1 + ‖verticalRatio s‖ := by simp
  unfold verticalResolvent
  rw [norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hden_pos hle

lemma verticalResolvent_norm_lower_bound_of_offCriticalStrip
    (s : ℂ) (hs : offCriticalStrip s) :
    (1 / (1 + ‖verticalRatio s‖) : ℝ) ≤ ‖verticalResolvent s‖ :=
  verticalResolvent_norm_lower_bound_of_re_pos s hs.1

/-- Lower bound for the roadmap resolvent `(1 - q(s))⁻¹`. -/
lemma resolvent_lower_bound (s : ℂ) (h : ‖q s‖ < 1) :
    (1 / (1 + ‖q s‖) : ℝ) ≤ ‖1 / (1 - q s)‖ := by
  have hq_ne : q s ≠ 1 := by
    intro hq
    have hnorm : ‖q s‖ = 1 := by simp [hq]
    linarith
  have hden_pos : 0 < ‖(1 : ℂ) - q s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hq_ne.symm)
  have hle : ‖(1 : ℂ) - q s‖ ≤ 1 + ‖q s‖ := by
    calc
      ‖(1 : ℂ) - q s‖ ≤ ‖(1 : ℂ)‖ + ‖q s‖ := norm_sub_le _ _
      _ = 1 + ‖q s‖ := by simp
  have hdiv : (1 / (1 + ‖q s‖) : ℝ) ≤ 1 / ‖(1 : ℂ) - q s‖ :=
    one_div_le_one_div_of_le hden_pos hle
  simpa [one_div, norm_inv] using hdiv

lemma resolvent_lower_bound_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    (1 / (1 + ‖q s‖) : ℝ) ≤ ‖1 / (1 - q s)‖ :=
  resolvent_lower_bound s (q_norm_lt_one_of_re_pos s hs)

lemma resolvent_lower_bound_of_offCriticalStrip (s : ℂ) (hs : offCriticalStrip s) :
    (1 / (1 + ‖q s‖) : ℝ) ≤ ‖1 / (1 - q s)‖ :=
  resolvent_lower_bound s (q_norm_lt_one_of_offCriticalStrip s hs)

/-- Four-floor geometric prefix `1 + z + z² + z³`. -/
noncomputable def verticalQuartetPrefix (z : ℂ) : ℂ :=
  1 + z + z ^ 2 + z ^ 3

lemma verticalQuartetPrefix_factor (z : ℂ) :
    verticalQuartetPrefix z = (1 + z) * (1 + z ^ 2) := by
  unfold verticalQuartetPrefix
  ring

lemma verticalDepthTailFromTwo_eq_quartet_add_tail
    (s : ℂ) (hs : 0 < s.re) :
    verticalDepthTailFromTwo s =
      q s ^ 2 * verticalQuartetPrefix (q s) + q s ^ 6 * verticalResolvent s := by
  rw [verticalDepthTailFromTwo_eq s hs]
  unfold verticalResolvent verticalQuartetPrefix q
  have hden : 1 - verticalRatio s ≠ 0 :=
    verticalResolvent_den_ne_zero_of_re_pos s hs
  field_simp [hden]
  ring

lemma verticalQuartetTail_norm_le_geometric_upper_of_re_pos
    (s : ℂ) (hs : 0 < s.re) :
    ‖q s ^ 6 * verticalResolvent s‖ ≤ ‖q s‖ ^ 6 * (1 - ‖q s‖)⁻¹ := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (verticalResolvent_norm_le_geometric_upper_of_re_pos s hs)
    (pow_nonneg (norm_nonneg _) 6)

lemma one_add_real_mul_exp_ofReal_mul_I_eq (r θ : ℝ) :
    1 + (r : ℂ) * Complex.exp (θ * Complex.I) =
      (1 + r * Real.cos θ) + (r * Real.sin θ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;> simp [mul_add, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm]

lemma sq_norm_one_add_real_mul_exp_ofReal_mul_I (r θ : ℝ) :
    ‖1 + (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 =
      1 + r ^ 2 + 2 * r * Real.cos θ := by
  rw [one_add_real_mul_exp_ofReal_mul_I_eq, Complex.sq_norm]
  calc
    Complex.normSq ((1 + r * Real.cos θ) + (r * Real.sin θ) * Complex.I)
      = (1 + r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
          simpa [add_assoc] using
            (Complex.normSq_add_mul_I (1 + r * Real.cos θ) (r * Real.sin θ))
    _ = 1 + r ^ 2 + 2 * r * Real.cos θ := by
          nlinarith [Real.sin_sq_add_cos_sq θ]

lemma real_mul_exp_ofReal_mul_I_pow_two (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 =
      ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ) * Complex.I) := by
  calc
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2
        = (r : ℂ) ^ 2 * (Complex.exp (θ * Complex.I)) ^ 2 := by
            rw [mul_pow]
    _ = ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ) * Complex.I) := by
          congr 1
          · simp [pow_two]
          · rw [pow_two, ← Complex.exp_add]
            congr 1
            ring

lemma one_add_sq_real_mul_exp_ofReal_mul_I_eq (r θ : ℝ) :
    1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 =
      (1 + r ^ 2 * Real.cos (2 * θ)) +
        (r ^ 2 * Real.sin (2 * θ)) * Complex.I := by
  calc
    1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2
      = 1 + (((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ) * Complex.I)) := by
          rw [real_mul_exp_ofReal_mul_I_pow_two]
    _ = (1 + r ^ 2 * Real.cos (2 * θ)) +
          (r ^ 2 * Real.sin (2 * θ)) * Complex.I := by
          convert one_add_real_mul_exp_ofReal_mul_I_eq (r ^ 2) (2 * θ) using 1
          · simp [pow_two]
          · simp [pow_two]

lemma sq_norm_one_add_sq_real_mul_exp_ofReal_mul_I (r θ : ℝ) :
    ‖1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2‖ ^ 2 =
      1 + r ^ 4 + 2 * r ^ 2 * Real.cos (2 * θ) := by
  calc
    ‖1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2‖ ^ 2
      = ‖1 + (((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ) * Complex.I))‖ ^ 2 := by
          rw [real_mul_exp_ofReal_mul_I_pow_two]
    _ = 1 + (r ^ 2) ^ 2 + 2 * (r ^ 2) * Real.cos (2 * θ) := by
          convert sq_norm_one_add_real_mul_exp_ofReal_mul_I (r ^ 2) (2 * θ) using 1
          · simp [pow_two]
    _ = 1 + r ^ 4 + 2 * r ^ 2 * Real.cos (2 * θ) := by
          ring

lemma sq_norm_one_add_sq_real_mul_exp_ofReal_mul_I' (r θ : ℝ) :
    ‖1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2‖ ^ 2 =
      (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.cos θ ^ 2 := by
  rw [sq_norm_one_add_sq_real_mul_exp_ofReal_mul_I, Real.cos_two_mul]
  ring

lemma verticalQuartetPrefix_sq_norm_on_circle (r θ : ℝ) :
    ‖verticalQuartetPrefix ((r : ℂ) * Complex.exp (θ * Complex.I))‖ ^ 2 =
      (1 + r ^ 2 + 2 * r * Real.cos θ) *
        ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.cos θ ^ 2) := by
  calc
    ‖verticalQuartetPrefix ((r : ℂ) * Complex.exp (θ * Complex.I))‖ ^ 2
      = ‖1 + (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 *
          ‖1 + ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2‖ ^ 2 := by
            rw [verticalQuartetPrefix_factor, norm_mul]
            ring
    _ = (1 + r ^ 2 + 2 * r * Real.cos θ) *
          ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.cos θ ^ 2) := by
            rw [sq_norm_one_add_real_mul_exp_ofReal_mul_I,
              sq_norm_one_add_sq_real_mul_exp_ofReal_mul_I']

lemma verticalQuartetPrefix_sq_lower_bound_aux {r x : ℝ}
    (hr0 : 0 ≤ r) (hx : -1 ≤ x) :
    ((1 - r) * (1 + r ^ 2)) ^ 2 ≤
      (1 + r ^ 2 + 2 * r * x) * ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * x ^ 2) := by
  have hbase : 0 ≤ 1 + r ^ 2 + 2 * r * x := by
    have hsquare : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
    nlinarith
  have hshift : 0 ≤ x + 1 := by
    linarith
  have hnonneg :
      0 ≤ 2 * r * (x + 1) * ((1 - r) ^ 2 * (1 + r ^ 2 + 2 * r * x) + 4 * r ^ 2 * x ^ 2) := by
    have hinner :
        0 ≤ (1 - r) ^ 2 * (1 + r ^ 2 + 2 * r * x) + 4 * r ^ 2 * x ^ 2 := by
      exact add_nonneg (mul_nonneg (sq_nonneg _) hbase) (by positivity)
    have hfront : 0 ≤ 2 * r * (x + 1) := by
      nlinarith
    exact mul_nonneg hfront hinner
  have hfactor :
      (1 + r ^ 2 + 2 * r * x) * ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * x ^ 2)
        - ((1 - r) * (1 + r ^ 2)) ^ 2
        = 2 * r * (x + 1) *
            ((1 - r) ^ 2 * (1 + r ^ 2 + 2 * r * x) + 4 * r ^ 2 * x ^ 2) := by
    ring
  nlinarith

/-- Sharp lower bound for the four-floor geometric prefix on the circle `|z| = r ≤ 1`. -/
lemma verticalQuartetPrefix_norm_lower_bound_on_circle
    (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r) * (1 + r ^ 2) ≤ ‖verticalQuartetPrefix ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  rw [← sq_le_sq₀ (by
      have h1 : 0 ≤ 1 - r := by linarith
      positivity) (norm_nonneg _)]
  rw [verticalQuartetPrefix_sq_norm_on_circle]
  exact verticalQuartetPrefix_sq_lower_bound_aux hr0 (Real.neg_one_le_cos θ)

lemma verticalQuartetPrefix_norm_lower_bound_of_norm_le_one
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1 - ‖z‖) * (1 + ‖z‖ ^ 2) ≤ ‖verticalQuartetPrefix z‖ := by
  calc
    (1 - ‖z‖) * (1 + ‖z‖ ^ 2)
      ≤ ‖verticalQuartetPrefix ((‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I))‖ := by
          exact verticalQuartetPrefix_norm_lower_bound_on_circle ‖z‖ (Complex.arg z)
            (norm_nonneg z) hz
    _ = ‖verticalQuartetPrefix z‖ := by
          rw [Complex.norm_mul_exp_arg_mul_I z]

lemma verticalQuartetPrefix_norm_lower_bound_of_offCriticalStrip
    (s : ℂ) (hs : offCriticalStrip s) :
    (1 - ‖q s‖) * (1 + ‖q s‖ ^ 2) ≤ ‖verticalQuartetPrefix (q s)‖ := by
  exact verticalQuartetPrefix_norm_lower_bound_of_norm_le_one
    (z := q s) (le_of_lt (q_norm_lt_one_of_offCriticalStrip s hs))

lemma verticalQuartetPrefix_eq_lower_bound_at_pi (r : ℝ) :
    verticalQuartetPrefix ((r : ℂ) * Complex.exp (Real.pi * Complex.I)) =
      (((1 - r) : ℝ) : ℂ) * (((1 + r ^ 2) : ℝ) : ℂ) := by
  unfold verticalQuartetPrefix
  rw [Complex.exp_pi_mul_I]
  simp [pow_two, pow_three]
  ring

/-- The quartet lower bound is attained at the worst-case phase `θ = π`. -/
lemma verticalQuartetPrefix_norm_eq_lower_bound_at_pi
  (r : ℝ) (hr1 : r ≤ 1) :
    ‖verticalQuartetPrefix ((r : ℂ) * Complex.exp (Real.pi * Complex.I))‖ =
      (1 - r) * (1 + r ^ 2) := by
  rw [verticalQuartetPrefix_eq_lower_bound_at_pi]
  have h1 : 0 ≤ 1 - r := by linarith
  have h2 : 0 ≤ 1 + r ^ 2 := by positivity
  rw [norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]

end C2
