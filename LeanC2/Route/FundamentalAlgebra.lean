import LeanC2.Identity.C0Bridge
import LeanC2.Route.Transfer

namespace C2

abbrev OddChannel := ℂ -> ℂ

/-- Central C2 expression after the vertical tower has been summed, with an abstract odd channel. -/
noncomputable def centralFromOddChannel (Zodd : OddChannel) (s : ℂ) : ℂ :=
  (2 : ℂ) * verticalDepthTailFromTwo s * Zodd s

/-- Interface for the odd Dirichlet channel `Z_odd(s) = (1 - 2^{-s}) ζ(s)`. -/
def OddChannelEulerRelation (Zodd zetaFun : ℂ -> ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re -> Zodd s = (1 - complexDirichletCoeff s 2) * zetaFun s

/-- The algebraic C2 bridge from the odd-channel relation to `F = c0 * ζ`. -/
theorem centralFromOddChannel_identity
    {Zodd zetaFun : ℂ -> ℂ} (hOdd : OddChannelEulerRelation Zodd zetaFun) :
    FundamentalIdentityOnRightHalfPlane (centralFromOddChannel Zodd) zetaFun := by
  intro s hs
  unfold centralFromOddChannel
  rw [hOdd s hs]
  have hc0 := c0_eq_c0FromVerticalFactor_of_re_pos s hs
  unfold c0FromVerticalFactor at hc0
  calc
    (2 : ℂ) * verticalDepthTailFromTwo s *
        ((1 - complexDirichletCoeff s 2) * zetaFun s)
        = ((2 : ℂ) * verticalDepthTailFromTwo s *
            (1 - complexDirichletCoeff s 2)) * zetaFun s := by ring
    _ = c0 s * zetaFun s := by rw [← hc0]

/-- The same bridge specialized to `riemannZeta`. -/
theorem centralFromOddChannel_riemannZeta_identity
    {Zodd : OddChannel} (hOdd : OddChannelEulerRelation Zodd riemannZeta) :
    FundamentalIdentityOnRightHalfPlane (centralFromOddChannel Zodd) riemannZeta :=
  centralFromOddChannel_identity hOdd

end C2
