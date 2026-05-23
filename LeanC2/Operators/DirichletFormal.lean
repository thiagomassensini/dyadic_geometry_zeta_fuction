import LeanC2.Operators.FiniteCancellation

namespace C2

/--
A finite Dirichlet-like kernel on the C2 rectangle `K,M`.

The fields are local finite hypotheses, not global analytic assumptions:
* `multiplicative` separates `f(2^k*m)` on the rectangle;
* `geometricDepth` says the values on powers of two are geometric.
-/
structure FormalDirichletKernel (R : Type*) [CommRing R] [Algebra ℚ R] (K M : Nat) where
  coeff : Nat -> R
  depthBase : R
  multiplicative : IsC2MultiplicativeOnRectangle coeff K M
  geometricDepth : HasGeometricDepthOnRectangle coeff K depthBase

namespace FormalDirichletKernel

variable {R : Type*} [CommRing R] [Algebra ℚ R] {K M : Nat}

/-- The finite depth factor `∑_{k=2}^K (r/2)^k`. -/
def depthFactor (D : FormalDirichletKernel R K M) : R :=
  ∑ k ∈ Finset.Icc 2 K, depthGeometricRatio D.depthBase ^ k

/-- The finite odd-core sum. -/
def coreSum (D : FormalDirichletKernel R K M) : R :=
  ∑ m ∈ oddCoresUpTo M, D.coeff m

/-- The factored center expression `2 * depthFactor * coreSum`. -/
def factoredCenter (D : FormalDirichletKernel R K M) : R :=
  (2 : R) * D.depthFactor * D.coreSum

/-- The direct lateral finite sum over the C2 rectangle. -/
def directLateralSum (D : FormalDirichletKernel R K M) : R :=
  ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm D.coeff k m

/-- The finite bracket sum over the C2 rectangle. -/
def bracketSum (D : FormalDirichletKernel R K M) : R :=
  ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm D.coeff k m

/-- Formal finite C2 factorization for a Dirichlet-like kernel. -/
theorem lateral_sub_bracket_eq_factoredCenter (D : FormalDirichletKernel R K M) :
    D.directLateralSum - D.bracketSum = D.factoredCenter := by
  unfold directLateralSum bracketSum factoredCenter depthFactor coreSum
  exact rectangular_lateral_cancellation_geometric_depth D.coeff K M D.depthBase
    D.multiplicative D.geometricDepth

section FieldClosedForm

variable {F : Type*} [Field F] [Algebra ℚ F]

/-- Closed form of the finite depth factor. -/
def closedDepthFactor (D : FormalDirichletKernel F K M) : F :=
  (depthGeometricRatio D.depthBase ^ (K + 1) - depthGeometricRatio D.depthBase ^ 2) /
    (depthGeometricRatio D.depthBase - 1)

theorem depthFactor_eq_closed (D : FormalDirichletKernel F K M)
    (hK : 2 ≤ K) (hr : depthGeometricRatio D.depthBase ≠ 1) :
    D.depthFactor = D.closedDepthFactor := by
  unfold depthFactor closedDepthFactor
  exact depthGeometricRatioSum_Icc_closed D.depthBase hK hr

/-- Formal finite C2 factorization with the depth geometric sum evaluated in closed form. -/
theorem lateral_sub_bracket_eq_closed (D : FormalDirichletKernel F K M)
    (hK : 2 ≤ K) (hr : depthGeometricRatio D.depthBase ≠ 1) :
    D.directLateralSum - D.bracketSum = (2 : F) * D.closedDepthFactor * D.coreSum := by
  rw [D.lateral_sub_bracket_eq_factoredCenter]
  unfold factoredCenter
  rw [D.depthFactor_eq_closed hK hr]

end FieldClosedForm

end FormalDirichletKernel

end C2
