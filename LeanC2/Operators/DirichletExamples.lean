import LeanC2.Operators.DirichletFormal

namespace C2

namespace FormalDirichletKernel

/-- The constant-one finite kernel, a concrete smoke test for the formal Dirichlet pipeline. -/
def constantOne (K M : Nat) : FormalDirichletKernel ℚ K M where
  coeff := fun _ => 1
  depthBase := 1
  multiplicative := by
    intro k _hk m _hm
    norm_num
  geometricDepth := by
    intro k _hk
    simp

lemma constantOne_depthRatio_ne_one : depthGeometricRatio (1 : ℚ) ≠ 1 := by
  norm_num [depthGeometricRatio]

/-- The closed finite C2 factorization specialized to the constant-one kernel. -/
theorem constantOne_lateral_sub_bracket_eq_closed (K M : Nat) (hK : 2 ≤ K) :
    (constantOne K M).directLateralSum - (constantOne K M).bracketSum =
      (2 : ℚ) * (constantOne K M).closedDepthFactor * (constantOne K M).coreSum := by
  exact (constantOne K M).lateral_sub_bracket_eq_closed hK constantOne_depthRatio_ne_one

/-- The same specialization with the closed depth factor unfolded. -/
theorem constantOne_lateral_sub_bracket_eq_explicit (K M : Nat) (hK : 2 ≤ K) :
    (constantOne K M).directLateralSum - (constantOne K M).bracketSum =
      (2 : ℚ) * (((1 / 2 : ℚ) ^ (K + 1) - (1 / 2 : ℚ) ^ 2) / ((1 / 2 : ℚ) - 1)) *
        (constantOne K M).coreSum := by
  rw [constantOne_lateral_sub_bracket_eq_closed K M hK]
  unfold closedDepthFactor constantOne
  norm_num [depthGeometricRatio]

end FormalDirichletKernel

end C2
