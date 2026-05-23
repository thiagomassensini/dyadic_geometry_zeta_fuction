import Mathlib
import LeanC2.Foundations.Basic

namespace C2

noncomputable def c0 (s : Complex) : Complex :=
  ((2 : Complex) ^ (-2 * s)) * (((2 : Complex) ^ s) - 1) /
    (2 * ((2 : Complex) ^ s) - 1)

lemma twoCpow_ne_one_of_re_pos {s : Complex} (hs : 0 < s.re) :
    ((2 : Complex) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : Complex) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : Real)) (by norm_num) s
  have hnormOne : ‖((2 : Complex) ^ s)‖ = 1 := by
    simp [h]
  have hgt : 1 < ‖((2 : Complex) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  linarith

lemma twoMulTwoCpow_ne_one_of_re_pos {s : Complex} (hs : 0 < s.re) :
    (2 : Complex) * ((2 : Complex) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : Complex) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : Real)) (by norm_num) s
  have hpowGtOne : 1 < ‖((2 : Complex) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  have hmulGtTwo : 2 < ‖(2 : Complex) * ((2 : Complex) ^ s)‖ := by
    rw [Complex.norm_mul]
    norm_num
    nlinarith
  have hmulEqOne : ‖(2 : Complex) * ((2 : Complex) ^ s)‖ = 1 := by
    simp [h]
  linarith

/-- Nonvanishing of the C2 normalization factor on the open right half-plane. -/
theorem c0_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : c0 s ≠ 0 := by
  unfold c0
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
    · exact sub_ne_zero.mpr (twoCpow_ne_one_of_re_pos hs)
  · exact sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)

theorem c0_ne_zero_on_critical (t : ℝ) :
    c0 (((1 : Complex) / 2) + t * Complex.I) ≠ 0 := by
  have hs : 0 < ((((1 : Complex) / 2) + t * Complex.I)).re := by
    simp
  exact c0_ne_zero_of_re_pos hs

/-- Roadmap spelling: `c0` does not vanish on `Re(s) > 0`. -/
theorem c0_ne_zero_sigma_pos (s : Complex) (hs : 0 < s.re) :
    c0 s ≠ 0 :=
  c0_ne_zero_of_re_pos hs

end C2
