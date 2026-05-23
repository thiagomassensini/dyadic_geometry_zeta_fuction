import Mathlib
import LeanC2.Foundations.Basic
import LeanC2.Identity.C0

namespace C2

/--
Interface for the continued C2 identity on the open right half-plane:
`F(s) = c0(s) * ζ(s)`.
-/
def FundamentalIdentityOnRightHalfPlane
    (F zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 0 < s.re -> F s = c0 s * zetaFun s

/--
Interface for the C2 identity only where the RH transfer actually needs it:
the off-critical strip.
-/
def FundamentalIdentityOnOffCriticalStrip
    (F zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, offCriticalStrip s -> F s = c0 s * zetaFun s

theorem FundamentalIdentityOnRightHalfPlane.toOffCriticalStrip
    {F zetaFun : Complex -> Complex}
    (hId : FundamentalIdentityOnRightHalfPlane F zetaFun) :
    FundamentalIdentityOnOffCriticalStrip F zetaFun := by
  intro s hs
  exact hId s hs.1

theorem F_nonzero_iff_zeta_nonzero_of_identity
    {F zetaFun : Complex -> Complex}
    (hId : FundamentalIdentityOnRightHalfPlane F zetaFun)
    {s : Complex} (hs : 0 < s.re) (hc0 : c0 s ≠ 0) :
    F s ≠ 0 ↔ zetaFun s ≠ 0 := by
  constructor
  · intro hF hz
    have hEq := hId s hs
    rw [hz, mul_zero] at hEq
    exact hF hEq
  · intro hz hF
    have hEq := hId s hs
    rw [hF] at hEq
    exact mul_ne_zero hc0 hz hEq.symm

theorem zeta_nonzero_of_F_nonzero
    {F zetaFun : Complex -> Complex}
    (hId : FundamentalIdentityOnRightHalfPlane F zetaFun)
    {s : Complex} (hs : 0 < s.re) (hF : F s ≠ 0) :
    zetaFun s ≠ 0 := by
  intro hz
  have hEq := hId s hs
  rw [hz, mul_zero] at hEq
  exact hF hEq

theorem offCriticalStrip_zeta_nonvanishing_of_F_nonvanishing
    {F zetaFun : Complex -> Complex}
    (hId : FundamentalIdentityOnRightHalfPlane F zetaFun)
    (hF : offCriticalStripNonvanishing F) :
    offCriticalStripNonvanishing zetaFun := by
  intro s hs
  exact zeta_nonzero_of_F_nonzero hId hs.1 (hF s hs)

theorem mathlibRiemannHypothesis_of_F_nonvanishing
    {F : Complex -> Complex}
    (hId : FundamentalIdentityOnRightHalfPlane F riemannZeta)
    (hF : offCriticalStripNonvanishing F) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_offCriticalStripNonvanishing
    (offCriticalStrip_zeta_nonvanishing_of_F_nonvanishing hId hF)

theorem mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity
    {F : Complex -> Complex}
    (hId : FundamentalIdentityOnOffCriticalStrip F riemannZeta)
    (hF : offCriticalStripNonvanishing F) :
    RiemannHypothesis := by
  refine mathlibRiemannHypothesis_of_offCriticalStripNonvanishing ?_
  intro s hs hz
  have hEq := hId s hs
  rw [hz, mul_zero] at hEq
  exact hF s hs hEq

end C2
