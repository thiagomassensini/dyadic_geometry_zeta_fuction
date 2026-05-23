import Mathlib
import LeanC2.Foundations.Basic

namespace C2

noncomputable def bracket2 (f : ℝ -> ℝ) (c : ℝ) : ℝ :=
  f (c - 1) + f (c + 1) - 2 * f c

noncomputable def tilt (δ x : ℝ) : ℝ :=
  Real.rpow x (-δ)

noncomputable def tiltBracket (δ c : ℝ) : ℝ :=
  bracket2 (tilt δ) c

@[simp] theorem tiltBracket_zero (c : ℝ) :
    tiltBracket 0 c = 0 := by
  simp [tiltBracket, bracket2, tilt]
  ring

@[simp] theorem tiltBracket_neg_one (c : ℝ) :
    tiltBracket (-1) c = 0 := by
  simp [tiltBracket, bracket2, tilt]
  ring

theorem tiltBracket_one_pos {c : ℝ} (hc : 1 < c) :
    0 < tiltBracket 1 c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : 0 < c - 1 := sub_pos.mpr hc
  have hcp1 : 0 < c + 1 := by linarith
  have hrepr : tiltBracket 1 c = (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ := by
    simp [tiltBracket, bracket2, tilt, Real.rpow_neg_one]
  rw [hrepr]
  have hformula :
      (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ = 2 / (c * (c - 1) * (c + 1)) := by
    field_simp [hc0.ne', hcm1.ne', hcp1.ne']
    ring_nf
  rw [hformula]
  have hden : 0 < c * (c - 1) * (c + 1) :=
    mul_pos (mul_pos hc0 hcm1) hcp1
  exact div_pos (by norm_num) hden

lemma centeredSecond_pos_of_strictConvexOn_Ici {f : ℝ -> ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid1 :
      f c < (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [hcomb, smul_eq_mul] using hmid
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  linarith [h2]

lemma centeredSecond_pos_of_strictConvexOn_Ioi {f : ℝ -> ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ioi 0) f) {c : ℝ} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ioi 0 := sub_pos.mpr hc
  have hcp1 : c + 1 ∈ Set.Ioi 0 := add_pos hc0 zero_lt_one
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid1 :
      f c < (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [hcomb, smul_eq_mul] using hmid
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  linarith [h2]

lemma centeredSecond_neg_of_strictConcaveOn_Ici {f : ℝ -> ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 1 < c) :
    f (c - 1) + f (c + 1) - 2 * f c < 0 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconc.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid1 :
      (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) < f c := by
    simpa [hcomb, smul_eq_mul] using hmid
  have h2 : f (c - 1) + f (c + 1) < 2 * f c := by
    nlinarith [hmid1]
  linarith [h2]

theorem tiltBracket_neg_of_neg_one_lt {δ c : ℝ} (hδ0 : -1 < δ) (hδ1 : δ < 0)
    (hc : 1 < c) :
    tiltBracket δ c < 0 := by
  have hp0 : 0 < -δ := by linarith
  have hp1 : -δ < 1 := by linarith
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (-δ)) :=
    Real.strictConcaveOn_rpow hp0 hp1
  have hneg := centeredSecond_neg_of_strictConcaveOn_Ici hconc hc
  simpa [tiltBracket, bracket2, tilt] using hneg

/-- For `p < 0`, `x ↦ x ^ p` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_rpow_of_neg {p : ℝ} (hp : p < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · exact fun x hx =>
      (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt
  intro x hx
  rw [interior_Ioi, Set.mem_Ioi] at hx
  simp only [Real.iter_deriv_rpow_const]
  apply mul_pos
  · have : (descPochhammer ℝ 2).eval p = p * (p - 1) := by
      simp [descPochhammer, Polynomial.eval_mul, Polynomial.eval_sub]
    rw [this]
    exact mul_pos_of_neg_of_neg hp (by linarith)
  · exact Real.rpow_pos_of_pos hx _

theorem tiltBracket_pos_of_pos {δ c : ℝ} (hδ : 0 < δ) (hc : 1 < c) :
    0 < tiltBracket δ c := by
  have hp : -δ < 0 := by linarith
  have hconv := strictConvexOn_rpow_of_neg hp
  have hpos := centeredSecond_pos_of_strictConvexOn_Ioi hconv hc
  simpa [tiltBracket, bracket2, tilt] using hpos

theorem tiltBracket_ne_zero_of_sigma_pos_of_ne_half {sigma c : ℝ}
    (hsigma : 0 < sigma) (hc : 1 < c) (hhalf : sigma ≠ (1 : ℝ) / 2) :
    tiltBracket (sigma - (1 : ℝ) / 2) c ≠ 0 := by
  intro hzero
  have hδ : -1 < sigma - (1 : ℝ) / 2 := by linarith
  by_cases hneg : sigma - (1 : ℝ) / 2 < 0
  · have hlt := tiltBracket_neg_of_neg_one_lt hδ hneg hc
    linarith
  · have hnonneg : 0 ≤ sigma - (1 : ℝ) / 2 := le_of_not_gt hneg
    by_cases hδ0 : sigma - (1 : ℝ) / 2 = 0
    · apply hhalf
      linarith
    · have hposδ : 0 < sigma - (1 : ℝ) / 2 := lt_of_le_of_ne hnonneg (Ne.symm hδ0)
      have hgt := tiltBracket_pos_of_pos hposδ hc
      linarith

/-- Roadmap spelling: the tilt bracket vanishes at `δ = 0`. -/
theorem bracket_tilt_zero (c : ℝ) :
    bracket2 (tilt 0) c = 0 := by
  simpa [tiltBracket] using tiltBracket_zero c

/-- Roadmap spelling: positive tilt curvature for `δ > 0`. -/
theorem bracket_tilt_pos {δ c : ℝ} (hδ : 0 < δ) (hc : 1 < c) :
    0 < bracket2 (tilt δ) c := by
  simpa [tiltBracket] using tiltBracket_pos_of_pos (δ := δ) (c := c) hδ hc

/-- Roadmap spelling: negative tilt curvature for `-1 < δ < 0`. -/
theorem bracket_tilt_neg {δ c : ℝ} (hδ1 : -1 < δ) (hδ2 : δ < 0) (hc : 1 < c) :
    bracket2 (tilt δ) c < 0 := by
  simpa [tiltBracket] using
    tiltBracket_neg_of_neg_one_lt (δ := δ) (c := c) hδ1 hδ2 hc

/--
On the C2 strip-relevant range `-1 < δ`, the centered tilt bracket vanishes exactly
on the critical line displacement `δ = 0`.
-/
theorem bracket_tilt_zero_iff_delta_zero {δ c : ℝ} (hδlow : -1 < δ) (hc : 1 < c) :
    bracket2 (tilt δ) c = 0 ↔ δ = 0 := by
  constructor
  · intro hzero
    have hzero' : tiltBracket δ c = 0 := by
      simpa [tiltBracket] using hzero
    by_cases hneg : δ < 0
    · have hlt := tiltBracket_neg_of_neg_one_lt (δ := δ) (c := c) hδlow hneg hc
      linarith
    · have hnonneg : 0 ≤ δ := le_of_not_gt hneg
      by_cases hδ0 : δ = 0
      · exact hδ0
      · have hpos : 0 < δ := lt_of_le_of_ne hnonneg (Ne.symm hδ0)
        have hgt := tiltBracket_pos_of_pos (δ := δ) (c := c) hpos hc
        linarith
  · intro hδ0
    simpa [hδ0] using bracket_tilt_zero c

end C2
