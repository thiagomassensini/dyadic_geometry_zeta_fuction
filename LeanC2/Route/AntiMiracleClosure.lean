import LeanC2.Route.BulkResolventNonCancellationTilt
import LeanC2.Analytic.GenuineLateralInfinite
import LeanC2.Analytic.GenuineContinuation

/-!
# Anti-miracle closure to the Riemann Hypothesis

This module wires the bulk anti-miracle (`BulkResolventNonCancellationTiltData`,
i.e. resolvent non-cancellation at the vertical phase scale `q(s) = ½·2^{-s}`
with the positivity inequality `‖K₂‖ / (1 + ‖q‖) > ‖G_δ‖ + ‖E_δ‖`) to the
mathlib `RiemannHypothesis` surface via the C2 identity

  `F = c₀ · ζ`

extended from `Re(s) > 1` to the open right half-plane.  No new analytic
content is introduced here: this file is a thin assembly that chains the
existing `nonvanishing` exit of the tilt data with the existing identity
transfer `mathlibRiemannHypothesis_of_F_nonvanishing`.
-/

namespace C2

/--
Off-critical non-vanishing of `F` from a bulk tilt resolvent non-cancellation
certificate whose region covers the entire off-critical strip.
-/
theorem offCriticalStripNonvanishing_of_bulkResolventNonCancellationTilt
    (data : BulkResolventNonCancellationTiltData)
    (hRegion : ∀ ⦃s : ℂ⦄, offCriticalStrip s → s ∈ data.bulkRegion) :
    offCriticalStripNonvanishing data.F := by
  intro s hs
  exact data.nonvanishing (hRegion hs)

/--
Off-critical non-vanishing of `genuineFInfinite` from a bulk tilt certificate
whose numerator coincides with `genuineFInfinite` and whose region covers the
entire off-critical strip.
-/
theorem offCriticalStripNonvanishing_genuineFInfinite_of_bulkResolventNonCancellationTilt
    (data : BulkResolventNonCancellationTiltData)
    (hF : data.F = genuineFInfinite)
    (hRegion : ∀ ⦃s : ℂ⦄, offCriticalStrip s → s ∈ data.bulkRegion) :
    offCriticalStripNonvanishing genuineFInfinite := by
  have hdata := offCriticalStripNonvanishing_of_bulkResolventNonCancellationTilt
    data hRegion
  intro s hs
  have := hdata s hs
  rwa [hF] at this

/--
**Anti-miracle closure for RH** (limit-level data):

From the bulk resolvent non-cancellation tilt witness over the entire
off-critical strip with `F = genuineFInfinite`, together with a continuation
witness extending the `Re(s) > 1` identity `F = c₀ · ζ` to the open right
half-plane, conclude `RiemannHypothesis`.
-/
theorem mathlibRiemannHypothesis_of_bulkResolventNonCancellationTilt_genuineFInfinite
    (data : BulkResolventNonCancellationTiltData)
    (hF : data.F = genuineFInfinite)
    (hRegion : ∀ ⦃s : ℂ⦄, offCriticalStrip s → s ∈ data.bulkRegion)
    (continuation : GenuineFInfiniteContinuationData) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_F_nonvanishing
    continuation.fundamentalIdentity
    (offCriticalStripNonvanishing_genuineFInfinite_of_bulkResolventNonCancellationTilt
      data hF hRegion)

/--
**Anti-miracle closure for RH** (bounds-level data):

Same conclusion as
`mathlibRiemannHypothesis_of_bulkResolventNonCancellationTilt_genuineFInfinite`
but with the bound-level scalar data `BulkResolventNonCancellationTiltBoundsData`
(four explicit scalar bounds `K2Lower, GUpper, EUpper` with
`GUpper + EUpper < K2Lower / (1 + ‖q‖)`).
-/
theorem mathlibRiemannHypothesis_of_bulkResolventNonCancellationTiltBounds_genuineFInfinite
    (data : BulkResolventNonCancellationTiltBoundsData)
    (hF : data.F = genuineFInfinite)
    (hRegion : ∀ ⦃s : ℂ⦄, offCriticalStrip s → s ∈ data.bulkRegion)
    (continuation : GenuineFInfiniteContinuationData) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_of_bulkResolventNonCancellationTilt_genuineFInfinite
    data.toTiltData hF hRegion continuation

end C2
