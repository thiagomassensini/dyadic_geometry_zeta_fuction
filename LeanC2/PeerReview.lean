import LeanC2.Analytic.GenuineBulkConcrete

/-!
# Peer-review facade for the C2 route

This module provides review-facing names for the formal route to mathlib's
`RiemannHypothesis` statement.

It is intentionally thin: it does not replace the internal development names.
It only gives the paper and theorem map a stable public namespace.
-/

namespace C2
namespace PeerReview

abbrev C2FundamentalIdentityOnRightHalfPlane :=
  C2.FundamentalIdentityOnRightHalfPlane

abbrev C2FundamentalIdentityOnOffCriticalStrip :=
  C2.FundamentalIdentityOnOffCriticalStrip

abbrev OffCriticalNonvanishing := C2.offCriticalStripNonvanishing

abbrev NearCriticalZeroCertificate := C2.NearAxisCertificate

abbrev MiddleRegionDominanceCertificate := C2.RegionalVerticalBulkRouteData

abbrev MiddleRegionBoundsCertificate := C2.RegionalVerticalBulkBoundsData

abbrev EdgeRegionCertificate := C2.EdgeRouteData

abbrev OffCriticalRegionalCover := C2.OffCriticalCoverData

abbrev GenuineC2ContinuationData := C2.GenuineFInfiniteContinuationData

noncomputable abbrev GenuineC2Operator : ℂ → ℂ := C2.genuineFInfinite

abbrev RiemannHypothesisTerminalCertificate := C2.RiemannHypothesisTerminalData

noncomputable abbrev CalibratedContinuedBulkModel
    (coreCutoff : ℕ → ℕ) (K M : ℕ) : ℂ → ℂ :=
  C2.c2OddTailContinuedBalancingSeedBulkModel coreCutoff K M

theorem RiemannHypothesis_of_offCriticalNonvanishing
    (hζ : OffCriticalNonvanishing riemannZeta) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_offCriticalStripNonvanishing hζ

theorem ZetaNonvanishing_of_C2Nonvanishing
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnRightHalfPlane F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    OffCriticalNonvanishing riemannZeta := by
  exact C2.offCriticalStrip_zeta_nonvanishing_of_F_nonvanishing hId hF

theorem RiemannHypothesis_of_C2Nonvanishing
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnRightHalfPlane F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_F_nonvanishing hId hF

theorem RiemannHypothesis_of_C2Nonvanishing_offCriticalIdentity
    {F : ℂ → ℂ}
    (hId : C2FundamentalIdentityOnOffCriticalStrip F riemannZeta)
    (hF : OffCriticalNonvanishing F) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_F_nonvanishing_offCriticalIdentity hId hF

theorem OffCriticalNonvanishing_of_regionalCover
    (cover : OffCriticalRegionalCover) :
    OffCriticalNonvanishing cover.F := by
  exact C2.offCriticalStripNonvanishing_of_coverData cover

theorem RiemannHypothesis_of_regionalCover
    (cover : OffCriticalRegionalCover)
    (hId : C2FundamentalIdentityOnOffCriticalStrip cover.F riemannZeta) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_coverData_offCriticalIdentity cover hId

theorem RiemannHypothesis_of_terminalCertificate
    (cert : RiemannHypothesisTerminalCertificate) :
    RiemannHypothesis := by
  exact C2.mathlibRiemannHypothesis_of_terminalData cert

end PeerReview
end C2
