import Mathlib
import LeanC2.Foundations.Basic

set_option linter.style.whitespace false

namespace C2

/-- Real branch weight `q(σ) = 2^{-2σ}` controlling the quadratic branch mass. -/
noncomputable def branchWeightSigma (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-2 * σ)

/-- Quadratic branch mass, indexed from the first genuine depth `k = 2`. -/
noncomputable def branchNormSqSigma (σ : ℝ) : ℝ :=
  2 * ∑' j : ℕ, branchWeightSigma σ ^ (j + 2)

/-- Complex wrapper: the branch weight depends only on the real part. -/
noncomputable def branchWeightSigmaT (s : ℂ) : ℝ :=
  branchWeightSigma s.re

/-- Complex wrapper: the quadratic branch norm depends only on the real part. -/
noncomputable def branchNormSqSigmaT (s : ℂ) : ℝ :=
  branchNormSqSigma s.re

@[simp] theorem branchWeightSigmaT_indep_t (σ t : ℝ) :
    branchWeightSigmaT ((σ : ℂ) + (t : ℂ) * Complex.I) = branchWeightSigma σ := by
  simp [branchWeightSigmaT]

@[simp] theorem branchNormSqSigmaT_indep_t (σ t : ℝ) :
    branchNormSqSigmaT ((σ : ℂ) + (t : ℂ) * Complex.I) = branchNormSqSigma σ := by
  simp [branchNormSqSigmaT]

lemma branchWeightSigma_nonneg (σ : ℝ) : 0 ≤ branchWeightSigma σ := by
  unfold branchWeightSigma
  exact Real.rpow_nonneg (by norm_num) _

lemma branchWeightSigma_lt_one_of_pos {σ : ℝ} (hσ : 0 < σ) :
    branchWeightSigma σ < 1 := by
  unfold branchWeightSigma
  have hexp : -2 * σ < 0 := by nlinarith
  simpa [Real.rpow_zero] using
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hexp)

lemma branchWeightSigma_lt_half_of_half_lt {σ : ℝ} (hσ : (1 : ℝ) / 2 < σ) :
    branchWeightSigma σ < (1 / 2 : ℝ) := by
  unfold branchWeightSigma
  have hexp : -2 * σ < (-1 : ℝ) := by linarith
  have hpow : (2 : ℝ) ^ (-2 * σ) < (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hexp
  simpa [Real.rpow_neg_one] using hpow

lemma half_lt_branchWeightSigma_of_lt_half {σ : ℝ} (hσ : σ < (1 : ℝ) / 2) :
    (1 / 2 : ℝ) < branchWeightSigma σ := by
  unfold branchWeightSigma
  have hexp : (-1 : ℝ) < -2 * σ := by linarith
  have hpow : (2 : ℝ) ^ (-1 : ℝ) < (2 : ℝ) ^ (-2 * σ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hexp
  simpa [Real.rpow_neg_one] using hpow

lemma branchWeightSigma_half : branchWeightSigma ((1 : ℝ) / 2) = (1 / 2 : ℝ) := by
  unfold branchWeightSigma
  have hexp : -2 * ((1 : ℝ) / 2) = (-1 : ℝ) := by ring
  rw [hexp, Real.rpow_neg_one]
  norm_num

theorem branchNormSq_closed_form (σ : ℝ) (hσ : 0 < σ) :
    branchNormSqSigma σ =
      2 * branchWeightSigma σ ^ 2 / (1 - branchWeightSigma σ) := by
  have hq0 : 0 ≤ branchWeightSigma σ := branchWeightSigma_nonneg σ
  have hq1 : branchWeightSigma σ < 1 := branchWeightSigma_lt_one_of_pos hσ
  unfold branchNormSqSigma
  calc
    2 * ∑' j : ℕ, branchWeightSigma σ ^ (j + 2)
        = 2 * ((∑' j : ℕ, branchWeightSigma σ ^ j) * branchWeightSigma σ ^ 2) := by
            congr 1
            simp_rw [pow_add]
            rw [tsum_mul_right]
    _ = 2 * (branchWeightSigma σ ^ 2 * ∑' j : ℕ, branchWeightSigma σ ^ j) := by
      ring
    _ = 2 * (branchWeightSigma σ ^ 2 * (1 - branchWeightSigma σ)⁻¹) := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = 2 * branchWeightSigma σ ^ 2 / (1 - branchWeightSigma σ) := by
          rw [div_eq_mul_inv]
          ring

theorem branchNormSq_half : branchNormSqSigma ((1 : ℝ) / 2) = 1 := by
  have hσ : 0 < (1 : ℝ) / 2 := by norm_num
  rw [branchNormSq_closed_form ((1 : ℝ) / 2) hσ, branchWeightSigma_half]
  norm_num

theorem branchNormSq_lt_one_of_half_lt {σ : ℝ} (hσ : (1 : ℝ) / 2 < σ) :
    branchNormSqSigma σ < 1 := by
  have hσ0 : 0 < σ := by linarith
  have hq0 : 0 ≤ branchWeightSigma σ := branchWeightSigma_nonneg σ
  have hq1 : branchWeightSigma σ < 1 := branchWeightSigma_lt_one_of_pos hσ0
  have hqHalf : branchWeightSigma σ < (1 / 2 : ℝ) := branchWeightSigma_lt_half_of_half_lt hσ
  rw [branchNormSq_closed_form σ hσ0]
  have hden : 0 < 1 - branchWeightSigma σ := sub_pos.mpr hq1
  have hnum : 2 * branchWeightSigma σ ^ 2 < 1 - branchWeightSigma σ := by
    nlinarith [hq0, hqHalf]
  exact (div_lt_one hden).2 hnum

theorem branchNormSq_gt_one_of_pos_of_lt_half {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1 : ℝ) / 2) :
    1 < branchNormSqSigma σ := by
  have hq0 : 0 ≤ branchWeightSigma σ := branchWeightSigma_nonneg σ
  have hq1 : branchWeightSigma σ < 1 := branchWeightSigma_lt_one_of_pos hσ0
  have hqHalf : (1 / 2 : ℝ) < branchWeightSigma σ := half_lt_branchWeightSigma_of_lt_half hσ
  rw [branchNormSq_closed_form σ hσ0]
  have hden : 0 < 1 - branchWeightSigma σ := sub_pos.mpr hq1
  have hnum : 1 - branchWeightSigma σ < 2 * branchWeightSigma σ ^ 2 := by
    nlinarith [hq0, hqHalf]
  exact (one_lt_div hden).2 hnum

theorem branchNormSqSigmaT_lt_one_of_re_gt_half {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) :
    branchNormSqSigmaT s < 1 := by
  simpa [branchNormSqSigmaT] using branchNormSq_lt_one_of_half_lt hs

theorem branchNormSqSigmaT_eq_one_on_critical (t : ℝ) :
    branchNormSqSigmaT (((1 : ℂ) / 2) + (t : ℂ) * Complex.I) = 1 := by
  simpa [branchNormSqSigmaT] using branchNormSq_half

theorem branchNormSqSigmaT_gt_one_of_re_pos_of_re_lt_half {s : ℂ} (hs0 : 0 < s.re)
  (hs : s.re < (1 : ℝ) / 2) : 1 < branchNormSqSigmaT s := by
  simpa [branchNormSqSigmaT] using branchNormSq_gt_one_of_pos_of_lt_half hs0 hs

/-- Barrier form: below one exactly to the right of the critical line. -/
theorem branchNormSq_barrier_lt_one {σ : ℝ} (hσ : 0 < σ) :
    branchNormSqSigma σ < 1 ↔ (1 : ℝ) / 2 < σ := by
  constructor
  · intro hlt
    rcases lt_trichotomy σ ((1 : ℝ) / 2) with hleft | hline | hright
    · have hgt := branchNormSq_gt_one_of_pos_of_lt_half hσ hleft
      linarith
    · subst σ
      rw [branchNormSq_half] at hlt
      linarith
    · exact hright
  · intro hright
    exact branchNormSq_lt_one_of_half_lt hright

/-- Barrier form: equal to one exactly on the critical line. -/
theorem branchNormSq_barrier_eq_one {σ : ℝ} (hσ : 0 < σ) :
    branchNormSqSigma σ = 1 ↔ σ = (1 : ℝ) / 2 := by
  constructor
  · intro heq
    rcases lt_trichotomy σ ((1 : ℝ) / 2) with hleft | hline | hright
    · have hgt := branchNormSq_gt_one_of_pos_of_lt_half hσ hleft
      linarith
    · exact hline
    · have hlt := branchNormSq_lt_one_of_half_lt hright
      linarith
  · intro hline
    simpa [hline] using branchNormSq_half

/-- Barrier form: above one exactly to the left of the critical line. -/
theorem branchNormSq_barrier_gt_one {σ : ℝ} (hσ : 0 < σ) :
    1 < branchNormSqSigma σ ↔ σ < (1 : ℝ) / 2 := by
  constructor
  · intro hgt
    rcases lt_trichotomy σ ((1 : ℝ) / 2) with hleft | hline | hright
    · exact hleft
    · subst σ
      rw [branchNormSq_half] at hgt
      linarith
    · have hlt := branchNormSq_lt_one_of_half_lt hright
      linarith
  · intro hleft
    exact branchNormSq_gt_one_of_pos_of_lt_half hσ hleft

/-- Compact trichotomy for the branch norm barrier at `σ = 1/2`. -/
theorem branchNormSq_barrier {σ : ℝ} (hσ : 0 < σ) :
    (branchNormSqSigma σ < 1 ↔ (1 : ℝ) / 2 < σ) ∧
      (branchNormSqSigma σ = 1 ↔ σ = (1 : ℝ) / 2) ∧
        (1 < branchNormSqSigma σ ↔ σ < (1 : ℝ) / 2) := by
  exact ⟨branchNormSq_barrier_lt_one hσ,
    branchNormSq_barrier_eq_one hσ, branchNormSq_barrier_gt_one hσ⟩

end C2
