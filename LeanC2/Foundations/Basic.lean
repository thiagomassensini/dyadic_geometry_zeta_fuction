import Mathlib

namespace C2

abbrev sigmaPart (s : Complex) : ℝ := s.re
abbrev tPart (s : Complex) : ℝ := s.im

/-- Horizontal displacement from the critical line. -/
noncomputable def criticalOffset (s : Complex) : ℝ :=
  s.re - (1 : ℝ) / 2

/-- The open critical strip away from the critical line. -/
def offCriticalStrip (s : Complex) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ s.re ≠ (1 : ℝ) / 2

lemma not_offCriticalStrip_of_one_lt_re {s : Complex} (hs : 1 < s.re) :
    ¬ offCriticalStrip s := by
  intro hoff
  linarith [hs, hoff.2.1]

lemma false_of_one_lt_re_offCritical {s : Complex}
    (hone : 1 < s.re) (hoff : offCriticalStrip s) : False := by
  exact not_offCriticalStrip_of_one_lt_re hone hoff

/-- Nonvanishing throughout the open critical strip away from the critical line. -/
def offCriticalStripNonvanishing (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, offCriticalStrip s -> f s ≠ 0

/-- Transfer off-critical nonvanishing of `ζ` to the official mathlib RH surface. -/
theorem mathlibRiemannHypothesis_of_offCriticalStripNonvanishing
    (hζ : offCriticalStripNonvanishing riemannZeta) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  by_cases hs_ge_one : 1 ≤ s.re
  · exact False.elim ((riemannZeta_ne_zero_of_one_le_re hs_ge_one) hz)
  · have hs_lt_one : s.re < 1 := lt_of_not_ge hs_ge_one
    by_cases hs_pos : 0 < s.re
    · by_contra hhalf
      exact hζ s ⟨hs_pos, hs_lt_one, hhalf⟩ hz
    · have hs_nonpos : s.re ≤ 0 := le_of_not_gt hs_pos
      by_cases hs_zero : s = 0
      · have hz0 : riemannZeta 0 = 0 := by simpa [hs_zero] using hz
        norm_num [riemannZeta_zero] at hz0
      · have h_one_sub_re_ge_one : 1 ≤ (1 - s).re := by
          simp
          linarith
        have h_one_sub_ne_neg_nat : ∀ n : ℕ, 1 - s ≠ -n := by
          intro n h_eq
          have h_one_sub_re_nonpos : (1 - s).re ≤ 0 := by
            rw [h_eq]
            simp
          linarith
        have h_one_sub_ne_one : 1 - s ≠ 1 := by
          intro h_eq
          apply hs_zero
          have h_sub := congrArg (fun z : Complex => z - 1) h_eq
          exact neg_eq_zero.mp <| by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_sub
        have h_func :
            riemannZeta s =
              2 * (2 * (Real.pi : Complex)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
                Complex.cos ((Real.pi : Complex) * (1 - s) / 2) * riemannZeta (1 - s) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (riemannZeta_one_sub (s := 1 - s) h_one_sub_ne_neg_nat h_one_sub_ne_one)
        rw [hz] at h_func
        have h_func_zero :
            2 * (2 * (Real.pi : Complex)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
                Complex.cos ((Real.pi : Complex) * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
          simpa [eq_comm] using h_func
        have h_zeta_one_sub_ne_zero : riemannZeta (1 - s) ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re h_one_sub_re_ge_one
        have h_gamma_ne_zero : Complex.Gamma (1 - s) ≠ 0 :=
          Complex.Gamma_ne_zero h_one_sub_ne_neg_nat
        have h_two_pi_ne_zero : (2 * (Real.pi : Complex)) ≠ 0 := by
          exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        have h_exp_ne_zero : -(1 - s) ≠ 0 := by
          intro h_zero
          apply hs1
          exact (sub_eq_zero.mp (neg_eq_zero.mp h_zero)).symm
        have h_cpow_ne_zero : (2 * (Real.pi : Complex)) ^ (-(1 - s)) ≠ 0 := by
          exact
            (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h_exp_ne_zero).2
              h_two_pi_ne_zero
        have h_front_ne_zero :
            2 * (2 * (Real.pi : Complex)) ^ (-(1 - s)) * Complex.Gamma (1 - s) ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero two_ne_zero h_cpow_ne_zero) h_gamma_ne_zero
        have h_front_cos_zero :
            (2 * (2 * (Real.pi : Complex)) ^ (-(1 - s)) * Complex.Gamma (1 - s)) *
                Complex.cos ((Real.pi : Complex) * (1 - s) / 2) = 0 := by
          have h_grouped :
              ((2 * (2 * (Real.pi : Complex)) ^ (-(1 - s)) * Complex.Gamma (1 - s)) *
                  Complex.cos ((Real.pi : Complex) * (1 - s) / 2)) *
                  riemannZeta (1 - s) = 0 := by
            simpa [mul_assoc] using h_func_zero
          exact (mul_eq_zero.mp h_grouped).resolve_right h_zeta_one_sub_ne_zero
        have h_cos_zero : Complex.cos ((Real.pi : Complex) * (1 - s) / 2) = 0 := by
          exact (mul_eq_zero.mp h_front_cos_zero).resolve_left h_front_ne_zero
        obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h_cos_zero
        have h_pi_half_ne_zero : ((Real.pi : Complex) / 2) ≠ 0 := by
          exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero
        have h_odd_integer : (1 : Complex) - s = ((2 * k + 1 : ℤ) : Complex) := by
          apply (mul_right_injective₀ h_pi_half_ne_zero)
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hk
        have h_s_eq_even_int : s = -(2 * k : Complex) := by
          have h_odd_cast : (((2 * k + 1 : ℤ) : Complex)) = 1 + 2 * (k : Complex) := by
            simp [Int.cast_add, Int.cast_mul, add_comm, mul_comm]
          calc
            s = (1 : Complex) - ((2 * k + 1 : ℤ) : Complex) := by
              apply eq_sub_iff_add_eq.mpr
              simpa [add_assoc, add_left_comm, add_comm] using
                (sub_eq_iff_eq_add.mp h_odd_integer).symm
            _ = (1 : Complex) - (1 + 2 * (k : Complex)) := by rw [h_odd_cast]
            _ = -(2 * k : Complex) := by
              ring
        have h_odd_re_ge_one : (1 : ℝ) ≤ (((2 * k + 1 : ℤ) : Complex).re) := by
          simpa [h_odd_integer] using h_one_sub_re_ge_one
        have h_odd_ge_one : (1 : ℤ) ≤ 2 * k + 1 := by
          exact_mod_cast h_odd_re_ge_one
        have h_k_nonneg : 0 ≤ k := by
          linarith
        have h_k_ne_zero : k ≠ 0 := by
          intro hk_zero
          apply hs_zero
          rw [h_s_eq_even_int, hk_zero]
          norm_num
        have h_k_toNat_ne_zero : k.toNat ≠ 0 := by
          intro hk_toNat_zero
          apply h_k_ne_zero
          rw [← Int.toNat_of_nonneg h_k_nonneg, hk_toNat_zero]
          norm_num
        cases h_toNat : k.toNat with
        | zero => exact False.elim (h_k_toNat_ne_zero h_toNat)
        | succ n =>
            exact False.elim <| htriv ⟨n, by
              have h_k_nat : ((n + 1 : ℕ) : ℤ) = k := by
                rw [← Int.toNat_of_nonneg h_k_nonneg, h_toNat]
              calc
                s = -(2 * k : Complex) := h_s_eq_even_int
                _ = -(2 * (((n + 1 : ℕ) : ℤ) : Complex)) := by
                  rw [← h_k_nat]
                _ = -2 * ((n : ℕ) : Complex) - 2 := by
                  simp [Nat.cast_add, Nat.cast_one]
                  ring
                _ = -2 * (((n : ℕ) : Complex) + 1) := by
                  ring
            ⟩

end C2
