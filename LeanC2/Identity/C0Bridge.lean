import LeanC2.Identity.C0
import LeanC2.Operators.VerticalResolvent

namespace C2

/-- The positive-real branch coefficient at `2` agrees with complex power `2^{-s}`. -/
lemma complexDirichletCoeff_two_eq_cpow_neg (s : ℂ) :
    complexDirichletCoeff s 2 = (2 : ℂ) ^ (-s) := by
  unfold complexDirichletCoeff
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  rw [Complex.natCast_log]
  ring_nf

/--
The vertical C2 factor multiplied by the formal odd-channel Euler factor is exactly `c0`.

This is the algebraic core of
`2 * (∑_{k≥2} 2^{-k(1+s)}) * (1 - 2^{-s}) = c0(s)`.
-/
noncomputable def c0FromVerticalFactor (s : ℂ) : ℂ :=
  (2 : ℂ) * verticalDepthTailFromTwo s * (1 - complexDirichletCoeff s 2)

theorem c0_eq_c0FromVerticalFactor_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    c0 s = c0FromVerticalFactor s := by
  unfold c0FromVerticalFactor
  rw [verticalDepthTailFromTwo_eq s hs]
  unfold c0 verticalResolvent
  rw [verticalRatio_eq]
  rw [complexDirichletCoeff_two_eq_cpow_neg]
  rw [Complex.cpow_neg]
  rw [show (-2 : ℂ) * s = (-2 : ℤ) * s by norm_num]
  rw [Complex.cpow_int_mul]
  have hu : (2 : ℂ) ^ s ≠ 0 :=
    (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hden : (2 : ℂ) * (2 : ℂ) ^ s - 1 ≠ 0 :=
    sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)
  field_simp [hu, hden]

theorem c0_eq_c0FromVerticalFactor_of_offCriticalStrip (s : ℂ) (hs : offCriticalStrip s) :
    c0 s = c0FromVerticalFactor s :=
  c0_eq_c0FromVerticalFactor_of_re_pos s hs.1

end C2
