import LeanC2.Operators.DirichletFormal

namespace C2

/-- Positive-real branch of the Dirichlet coefficient `n ↦ n^(-s)` on natural indices. -/
noncomputable def complexDirichletCoeff (s : ℂ) (n : Nat) : ℂ :=
  Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))

lemma complexDirichletCoeff_one (s : ℂ) : complexDirichletCoeff s 1 = 1 := by
  simp [complexDirichletCoeff]

lemma complexDirichletCoeff_ne_zero (s : ℂ) (n : Nat) :
    complexDirichletCoeff s n ≠ 0 := by
  unfold complexDirichletCoeff
  exact Complex.exp_ne_zero _

lemma complexDirichletCoeff_norm_eq_rpow_neg_re (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖complexDirichletCoeff s n‖ = (n : ℝ) ^ (-s.re) := by
  have hcpow : complexDirichletCoeff s n = (n : ℂ) ^ (-s) := by
    unfold complexDirichletCoeff
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hnC]
    congr 1
    rw [Complex.natCast_log]
    ring_nf
  rw [hcpow]
  have hpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) hpos (-s)

lemma complexDirichletCoeff_mul (s : ℂ) {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    complexDirichletCoeff s (a * b) = complexDirichletCoeff s a * complexDirichletCoeff s b := by
  unfold complexDirichletCoeff
  rw [← Complex.exp_add]
  congr 1
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlog : Real.log ((a * b : Nat) : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul haR hbR]
  rw [hlog, Complex.ofReal_add]
  ring

lemma complexDirichletCoeff_two_pow (s : ℂ) (k : Nat) :
    complexDirichletCoeff s (2 ^ k) = complexDirichletCoeff s 2 ^ k := by
  induction k with
  | zero =>
      simp [complexDirichletCoeff_one]
  | succ k ih =>
      have hpow_ne : 2 ^ k ≠ 0 := pow_ne_zero k (by norm_num : (2 : Nat) ≠ 0)
      calc
        complexDirichletCoeff s (2 ^ (k + 1))
            = complexDirichletCoeff s (2 ^ k * 2) := by rw [pow_succ]
        _ = complexDirichletCoeff s (2 ^ k) * complexDirichletCoeff s 2 := by
            exact complexDirichletCoeff_mul s hpow_ne (by norm_num)
        _ = complexDirichletCoeff s 2 ^ k * complexDirichletCoeff s 2 := by rw [ih]
        _ = complexDirichletCoeff s 2 ^ (k + 1) := by rw [pow_succ]

lemma complexDirichletCoeff_multiplicativeOnRectangle (s : ℂ) (K M : Nat) :
    IsC2MultiplicativeOnRectangle (complexDirichletCoeff s) K M := by
  intro k _hk m hm
  have hmOdd : Odd m := (mem_oddCoresUpTo.mp hm).2
  exact complexDirichletCoeff_mul s (pow_ne_zero k (by norm_num : (2 : Nat) ≠ 0))
    (ne_of_gt (odd_nat_pos hmOdd))

lemma complexDirichletCoeff_hasGeometricDepth (s : ℂ) (K : Nat) :
    HasGeometricDepthOnRectangle (complexDirichletCoeff s) K (complexDirichletCoeff s 2) := by
  intro k _hk
  exact complexDirichletCoeff_two_pow s k

lemma complexDirichletDepthRatio_eq (s : ℂ) :
    depthGeometricRatio (complexDirichletCoeff s 2) =
      (1 / 2 : ℂ) * complexDirichletCoeff s 2 := by
  norm_num [depthGeometricRatio]

lemma complexDirichletDepthRatio_ne_zero (s : ℂ) :
    depthGeometricRatio (complexDirichletCoeff s 2) ≠ 0 := by
  rw [complexDirichletDepthRatio_eq]
  exact mul_ne_zero (by norm_num) (complexDirichletCoeff_ne_zero s 2)

lemma complexDirichletDepthRatio_norm (s : ℂ) :
    ‖depthGeometricRatio (complexDirichletCoeff s 2)‖ =
      (1 / 2 : ℝ) * Real.exp (-(s.re * Real.log (2 : ℝ))) := by
  have hre : (-(s * (Real.log ((2 : Nat) : ℝ) : ℂ))).re =
      -(s.re * Real.log ((2 : Nat) : ℝ)) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [complexDirichletDepthRatio_eq, norm_mul]
  unfold complexDirichletCoeff
  rw [Complex.norm_exp, hre]
  norm_num

lemma complexDirichletDepthRatio_norm_lt_one_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ‖depthGeometricRatio (complexDirichletCoeff s 2)‖ < 1 := by
  rw [complexDirichletDepthRatio_norm]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul_pos : 0 < s.re * Real.log (2 : ℝ) := mul_pos hs hlog2
  have hexp_lt_one : Real.exp (-(s.re * Real.log (2 : ℝ))) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-(s.re * Real.log (2 : ℝ))) := Real.exp_pos _
  nlinarith

lemma complexDirichletDepthRatio_ne_one_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    depthGeometricRatio (complexDirichletCoeff s 2) ≠ 1 := by
  intro hq
  have hnorm_lt := complexDirichletDepthRatio_norm_lt_one_of_re_pos s hs
  rw [hq, norm_one] at hnorm_lt
  linarith

/-- Finite C2 Dirichlet kernel induced by the positive-real branch `n ↦ exp(-s log n)`. -/
noncomputable def complexDirichletKernel (s : ℂ) (K M : Nat) : FormalDirichletKernel ℂ K M where
  coeff := complexDirichletCoeff s
  depthBase := complexDirichletCoeff s 2
  multiplicative := complexDirichletCoeff_multiplicativeOnRectangle s K M
  geometricDepth := complexDirichletCoeff_hasGeometricDepth s K

/-- Complex finite C2 factorization for the Dirichlet coefficient `exp(-s log n)`. -/
theorem complexDirichletKernel_lateral_sub_bracket_eq_factoredCenter (s : ℂ) (K M : Nat) :
    (complexDirichletKernel s K M).directLateralSum -
        (complexDirichletKernel s K M).bracketSum =
      (complexDirichletKernel s K M).factoredCenter := by
  exact (complexDirichletKernel s K M).lateral_sub_bracket_eq_factoredCenter

/-- Same factorization with the depth/base rectangle side exposed. -/
theorem complexDirichletKernel_lateral_sub_bracket_eq_geometric_depth (s : ℂ) (K M : Nat) :
    (complexDirichletKernel s K M).directLateralSum -
        (complexDirichletKernel s K M).bracketSum =
      (2 : ℂ) *
        (∑ k ∈ Finset.Icc 2 K, depthGeometricRatio (complexDirichletCoeff s 2) ^ k) *
          (∑ m ∈ oddCoresUpTo M, complexDirichletCoeff s m) := by
  exact rectangular_lateral_cancellation_geometric_depth (complexDirichletCoeff s) K M
    (complexDirichletCoeff s 2)
    (complexDirichletCoeff_multiplicativeOnRectangle s K M)
    (complexDirichletCoeff_hasGeometricDepth s K)

/-- Closed finite C2 factorization when the complex depth ratio is not `1`. -/
theorem complexDirichletKernel_lateral_sub_bracket_eq_closed (s : ℂ) (K M : Nat)
    (hK : 2 ≤ K) (hr : depthGeometricRatio (complexDirichletCoeff s 2) ≠ 1) :
    (complexDirichletKernel s K M).directLateralSum -
        (complexDirichletKernel s K M).bracketSum =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        (complexDirichletKernel s K M).coreSum := by
  exact (complexDirichletKernel s K M).lateral_sub_bracket_eq_closed hK hr

/-- Closed finite C2 factorization in the right half-plane. -/
theorem complexDirichletKernel_lateral_sub_bracket_eq_closed_of_re_pos (s : ℂ) (K M : Nat)
    (hs : 0 < s.re) (hK : 2 ≤ K) :
    (complexDirichletKernel s K M).directLateralSum -
        (complexDirichletKernel s K M).bracketSum =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        (complexDirichletKernel s K M).coreSum := by
  exact complexDirichletKernel_lateral_sub_bracket_eq_closed s K M hK
    (complexDirichletDepthRatio_ne_one_of_re_pos s hs)

/-- Closed finite C2 factorization on the off-critical strip interface. -/
theorem complexDirichletKernel_lateral_sub_bracket_eq_closed_of_offCriticalStrip
    (s : ℂ) (K M : Nat) (hs : offCriticalStrip s) (hK : 2 ≤ K) :
    (complexDirichletKernel s K M).directLateralSum -
        (complexDirichletKernel s K M).bracketSum =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        (complexDirichletKernel s K M).coreSum := by
  exact complexDirichletKernel_lateral_sub_bracket_eq_closed_of_re_pos s K M hs.1 hK

end C2
