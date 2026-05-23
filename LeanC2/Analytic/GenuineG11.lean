import LeanC2.Analytic.GenuineCover
import LeanC2.Route.TiltSectorialRectangular

namespace C2

open scoped Topology

/-!
Pinned G11 and near-axis interfaces for `genuineFInfinite`.

This module does not add new analytic content.  It fixes the generic route-level
G11 / rectangular-central machinery at the actual roadmap operator
`genuineFInfinite`, so future concrete theorems can land directly in the final
pipeline without carrying repeated `F = genuineFInfinite` specializations.
-/

theorem IsCriticalZero.mem_puncturedOpenRightHalfPlane
    {zetaFun : ℂ → ℂ} {ρ : ℂ} (hρ : IsCriticalZero zetaFun ρ) :
    ρ ∈ puncturedOpenRightHalfPlane := by
  refine ⟨?_, ?_⟩
  · linarith [hρ.re_eq_half]
  · intro hEq
    have hre : ρ.re = 1 := by simp [hEq]
    linarith [hρ.re_eq_half]

theorem genuineFInfinite_analyticAt_of_analyticOnNhd_punctured
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    {ρ : ℂ} (hρ : IsCriticalZero riemannZeta ρ) :
    AnalyticAt ℂ genuineFInfinite ρ :=
  hGenuine ρ hρ.mem_puncturedOpenRightHalfPlane

abbrev GenuineFInfiniteTaylorBoundsFamilyData :=
  G11TaylorBoundsFamilyData genuineFInfinite riemannZeta

abbrev GenuineFInfiniteLeibnizTaylorBoundsFamilyData :=
  G11LeibnizTaylorBoundsFamilyData genuineFInfinite riemannZeta

abbrev GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData :=
  C2RectangularCentralRotatedConeMomentG11BoundsData genuineFInfinite riemannZeta

namespace GenuineFInfiniteNearAxisData

theorem genuineFInfinite_nonzero_at_two_of_continuation
    (continuation : GenuineFInfiniteContinuationData) :
    genuineFInfinite (2 : ℂ) ≠ 0 := by
  have hPos : 0 < ((2 : ℂ).re) := by norm_num
  rw [continuation.fundamentalIdentity (2 : ℂ) hPos]
  exact mul_ne_zero
    (c0_ne_zero_of_re_pos hPos)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

theorem not_eventually_zero_of_continuation
    (continuation : GenuineFInfiniteContinuationData)
    {ρ : ℂ} (hρ : IsCriticalZero riemannZeta ρ) :
    ¬ ∀ᶠ z in 𝓝 ρ, genuineFInfinite z = 0 := by
  intro hZero
  have hEqZero : Set.EqOn genuineFInfinite 0 puncturedOpenRightHalfPlane :=
    continuation.analyticOnNhd_punctured.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      puncturedOpenRightHalfPlane_isPreconnected
      hρ.mem_puncturedOpenRightHalfPlane
      hZero
  have hTwoMem : (2 : ℂ) ∈ puncturedOpenRightHalfPlane := by
    constructor
    · norm_num
    · norm_num
  exact genuineFInfinite_nonzero_at_two_of_continuation continuation (hEqZero hTwoMem)

theorem eventually_ne_zero_of_continuation
    (continuation : GenuineFInfiniteContinuationData)
    {ρ : ℂ} (hρ : IsCriticalZero riemannZeta ρ) :
    ∀ᶠ z in 𝓝[≠] ρ, genuineFInfinite z ≠ 0 := by
  let hAnalytic :=
    genuineFInfinite_analyticAt_of_analyticOnNhd_punctured
      continuation.analyticOnNhd_punctured hρ
  exact hAnalytic.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (not_eventually_zero_of_continuation continuation hρ)

noncomputable def of_continuation
    (continuation : GenuineFInfiniteContinuationData) :
    GenuineFInfiniteNearAxisData where
  near_axis := NearAxisCertificate.of_eventually_ne_zero
    (fun _ hρ => eventually_ne_zero_of_continuation continuation hρ)

noncomputable def ofLeibnizJet_c0_of_analyticOnNhd
    (hGenuine : AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane)
    (hJet : ∀ ρ, IsCriticalZero riemannZeta ρ ->
      ∃ m : ℕ, ∃ c z : ℕ → ℂ,
        (∀ k < m, z k = 0) ∧
        c 0 = c0 ρ ∧
        z m ≠ 0 ∧
        iteratedDeriv m genuineFInfinite ρ = leibnizJet m c z) :
    GenuineFInfiniteNearAxisData where
  near_axis := NearAxisCertificate.of_leibnizJet_c0
    (fun _ hρ =>
      genuineFInfinite_analyticAt_of_analyticOnNhd_punctured hGenuine hρ)
    hJet

noncomputable def ofLeibnizJet_c0_of_continuation
    (continuation : GenuineFInfiniteContinuationData)
    (hJet : ∀ ρ, IsCriticalZero riemannZeta ρ ->
      ∃ m : ℕ, ∃ c z : ℕ → ℂ,
        (∀ k < m, z k = 0) ∧
        c 0 = c0 ρ ∧
        z m ≠ 0 ∧
        iteratedDeriv m genuineFInfinite ρ = leibnizJet m c z) :
    GenuineFInfiniteNearAxisData :=
  ofLeibnizJet_c0_of_analyticOnNhd
    continuation.analyticOnNhd_punctured
    hJet

end GenuineFInfiniteNearAxisData

namespace GenuineFInfiniteTaylorBoundsFamilyData

noncomputable def toG11Certificate_of_affineLogRatioBound
    (data : GenuineFInfiniteTaylorBoundsFamilyData)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) genuineFInfinite ≤
          A + C * Real.log (2 + g11Height ρ)) :
    G11Certificate genuineFInfinite riemannZeta :=
  G11TaylorBoundsFamilyData.toG11Certificate_of_affineLogRatioBound
    data A C hA hC ratio_bound

noncomputable def toG11Certificate_of_logLinearRatioBound
    (data : GenuineFInfiniteTaylorBoundsFamilyData)
    (C : ℝ) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) genuineFInfinite ≤
          C * Real.log (2 + g11Height ρ)) :
    G11Certificate genuineFInfinite riemannZeta :=
  G11TaylorBoundsFamilyData.toG11Certificate_of_logLinearRatioBound
    data C hC ratio_bound

end GenuineFInfiniteTaylorBoundsFamilyData

namespace GenuineFInfiniteLeibnizTaylorBoundsFamilyData

noncomputable def toG11Certificate_of_affineLogRatioBound
    (data : GenuineFInfiniteLeibnizTaylorBoundsFamilyData)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) genuineFInfinite ≤
          A + C * Real.log (2 + g11Height ρ)) :
    G11Certificate genuineFInfinite riemannZeta :=
  G11LeibnizTaylorBoundsFamilyData.toG11Certificate_of_affineLogRatioBound
    data A C hA hC ratio_bound

noncomputable def toG11Certificate_of_logLinearRatioBound
    (data : GenuineFInfiniteLeibnizTaylorBoundsFamilyData)
    (C : ℝ) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) genuineFInfinite ≤
          C * Real.log (2 + g11Height ρ)) :
    G11Certificate genuineFInfinite riemannZeta :=
  G11LeibnizTaylorBoundsFamilyData.toG11Certificate_of_logLinearRatioBound
    data C hC ratio_bound

end GenuineFInfiniteLeibnizTaylorBoundsFamilyData

namespace GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData

noncomputable def ofTaylorBoundsFamily
    (localTaylor : GenuineFInfiniteTaylorBoundsFamilyData)
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (depthCutoff : ∀ ρ, IsCriticalZero riemannZeta ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero riemannZeta ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero riemannZeta ρ → ℝ)
    (phaseAngle : ∀ ρ, IsCriticalZero riemannZeta ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 +
          Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      |tiltDelta ρ hρ| ≤
        1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (rotatedCone : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ) a,
      a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
        Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
          (sectorialPhase (phaseAngle ρ hρ) *
            c2RectangularCentralContribution ρ a).re)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      principalTaylorScale ρ (localTaylor.multiplicity ρ hρ) genuineFInfinite =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      localTaylor.remainderCoeff ρ hρ ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localTaylor.multiplicity ρ hρ) + 1 : ℝ)) :
    GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData :=
  C2RectangularCentralRotatedConeMomentG11BoundsData.ofTaylorBoundsFamily
    localTaylor
    supportConstant
    aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    depthCutoff
    coreCutoff
    tiltDelta
    phaseAngle
    coreCutoff_pos
    explicitTopBound
    tiltDelta_mem
    rotatedCone
    principalCoeff_eq
    remainderCoeff_le

noncomputable def ofLeibnizTaylorBoundsFamily
    (localTaylor : GenuineFInfiniteLeibnizTaylorBoundsFamilyData)
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (depthCutoff : ∀ ρ, IsCriticalZero riemannZeta ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero riemannZeta ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero riemannZeta ρ → ℝ)
    (phaseAngle : ∀ ρ, IsCriticalZero riemannZeta ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 +
          Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      |tiltDelta ρ hρ| ≤
        1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (rotatedCone : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ) a,
      a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
        Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
          (sectorialPhase (phaseAngle ρ hρ) *
            c2RectangularCentralContribution ρ a).re)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      principalTaylorScale ρ (localTaylor.multiplicity ρ hρ) genuineFInfinite =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero riemannZeta ρ),
      localTaylor.remainderCoeff ρ hρ ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localTaylor.multiplicity ρ hρ) + 1 : ℝ)) :
    GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData :=
  C2RectangularCentralRotatedConeMomentG11BoundsData.ofLeibnizTaylorBoundsFamily
    localTaylor
    supportConstant
    aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    depthCutoff
    coreCutoff
    tiltDelta
    phaseAngle
    coreCutoff_pos
    explicitTopBound
    tiltDelta_mem
    rotatedCone
    principalCoeff_eq
    remainderCoeff_le

noncomputable def toNearAxisData
    (data : GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData) :
    GenuineFInfiniteNearAxisData where
  near_axis := data.toG11Certificate.toNearAxisCertificate

theorem near_axis_nonzero
    (data : GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData)
    {s : ℂ}
    (hs : s ∈ nearAxisRegion riemannZeta data.toNearAxisData.near_axis.radius) :
    genuineFInfinite s ≠ 0 := by
  exact near_axis_nonzero_from_G11 data.toG11Certificate <| by
    simpa [toNearAxisData] using hs

end GenuineFInfiniteRectangularCentralRotatedConeMomentG11BoundsData

end C2
