import LeanC2.Route.NearAxisTaylor

namespace C2

open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
G11 analytic certificate for the near-axis route.

The genuinely analytic estimates are represented as explicit certificate data:
for each critical zero, a transversal Taylor lower bound and the G11 ratio
`Bρ/Aρ ≤ A + C log²(2 + |γ|)`.  This file proves the route-level consequence:
such a certificate produces a `NearAxisCertificate`, hence zero-freeness in the
near-axis region.
-/

/-- Height parameter used in the G11 envelope. -/
def g11Height (ρ : ℂ) : ℝ :=
  |ρ.im|

/-- The global G11 envelope `A + C log²(2 + |γ|)`. -/
def g11Envelope (A C : ℝ) (ρ : ℂ) : ℝ :=
  A + C * (Real.log (2 + g11Height ρ)) ^ 2

/-- The G11-certified transversal radius `min(r, 1 / envelope)`. -/
def g11CertifiedRadius (A C r : ℝ) (ρ : ℂ) : ℝ :=
  min r (1 / g11Envelope A C ρ)

theorem g11Envelope_pos {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C) (ρ : ℂ) :
    0 < g11Envelope A C ρ := by
  have hheight_nonneg : 0 ≤ g11Height ρ := abs_nonneg _
  have hlog_pos : 0 < Real.log (2 + g11Height ρ) := by
    apply Real.log_pos
    linarith
  have hsq_pos : 0 < (Real.log (2 + g11Height ρ)) ^ 2 :=
    pow_pos hlog_pos 2
  unfold g11Envelope
  nlinarith [mul_pos hC hsq_pos]

theorem g11CertifiedRadius_pos {A C r : ℝ} (hA : 0 ≤ A) (hC : 0 < C)
    (hr : 0 < r) (ρ : ℂ) :
    0 < g11CertifiedRadius A C r ρ := by
  unfold g11CertifiedRadius
  exact lt_min hr (one_div_pos.mpr (g11Envelope_pos hA hC ρ))

theorem g11CertifiedRadius_le_baseRadius (A C r : ℝ) (ρ : ℂ) :
    g11CertifiedRadius A C r ρ ≤ r := by
  unfold g11CertifiedRadius
  exact min_le_left _ _

theorem one_div_envelope_le_A_div_B
    {A0 B envelope : ℝ}
    (hA0 : 0 < A0) (hB : 0 < B) (henv : 0 < envelope)
    (hratio : B / A0 ≤ envelope) :
    1 / envelope ≤ A0 / B := by
  have hB_le : B ≤ envelope * A0 := by
    have := (div_le_iff₀ hA0).mp hratio
    simpa [mul_comm] using this
  have hB_over_env : B / envelope ≤ A0 := by
    exact (div_le_iff₀ henv).mpr (by simpa [mul_comm] using hB_le)
  have hmul : B * (1 / envelope) ≤ A0 := by
    simpa [div_eq_mul_inv, mul_comm] using hB_over_env
  exact (le_div_iff₀ hB).mpr (by simpa [mul_comm] using hmul)

theorem g11CertifiedRadius_le_localZeroFreeRadius
    {globalA globalC r Aρ Bρ : ℝ} {ρ : ℂ}
    (hglobalA : 0 ≤ globalA)
    (hglobalC : 0 < globalC)
    (hAρ : 0 < Aρ)
    (hBρ : 0 ≤ Bρ)
    (hratio : Bρ / Aρ ≤ g11Envelope globalA globalC ρ) :
    g11CertifiedRadius globalA globalC r ρ ≤ localZeroFreeRadius Aρ Bρ r := by
  by_cases hB0 : Bρ = 0
  · rw [hB0]
    exact le_localZeroFreeRadius_of_zero_remainder
      (g11CertifiedRadius_le_baseRadius globalA globalC r ρ)
  · have hBpos : 0 < Bρ := lt_of_le_of_ne hBρ (Ne.symm hB0)
    have henv_pos : 0 < g11Envelope globalA globalC ρ :=
      g11Envelope_pos hglobalA hglobalC ρ
    rw [localZeroFreeRadius_of_pos_remainder hBpos]
    unfold g11CertifiedRadius
    exact min_le_min le_rfl
      (one_div_envelope_le_A_div_B hAρ hBpos henv_pos hratio)

/--
Local analytic data at one critical zero.

`principalCoeff` is `Aρ`, `remainderCoeff` is `Bρ(r)`, and `taylor_lower`
is the lower-bound form of the arbitrary-multiplicity transversal Taylor theorem.
-/
structure G11LocalTaylorData (F : ℂ → ℂ) (ρ : ℂ) where
  multiplicity : ℕ
  admissibleRadius : ℝ
  principalCoeff : ℝ
  remainderCoeff : ℝ
  admissibleRadius_pos : 0 < admissibleRadius
  principalCoeff_pos : 0 < principalCoeff
  remainderCoeff_nonneg : 0 ≤ remainderCoeff
  taylor_lower : ∀ δ : ℝ,
    0 < |δ| →
    |δ| ≤ admissibleRadius →
    |δ| ^ multiplicity * (principalCoeff - remainderCoeff * |δ|) ≤
      ‖F (ρ + (δ : ℂ))‖

namespace G11LocalTaylorData

/--
Package a theorem-11 style local Taylor lower bound into `G11LocalTaylorData`.

This is the direct bridge from the analytic statement
`|F(ρ + δ)| ≥ |δ|^m (Aρ - Bρ |δ|)` with
`Aρ = ‖F^(m)(ρ)‖ / m!` to the route-level G11 interface.
-/
noncomputable def ofTaylorLowerBound
    {F : ℂ → ℂ} {ρ : ℂ}
    (m : ℕ) (admissibleRadius remainderCoeff : ℝ)
    (admissibleRadius_pos : 0 < admissibleRadius)
    (remainderCoeff_nonneg : 0 ≤ remainderCoeff)
    (hprincipal : iteratedDeriv m F ρ ≠ 0)
    (hLower : ∀ δ : ℝ,
      0 < |δ| →
      |δ| ≤ admissibleRadius →
      |δ| ^ m *
          (principalTaylorScale ρ m F - remainderCoeff * |δ|) ≤
        ‖F (ρ + (δ : ℂ))‖) :
    G11LocalTaylorData F ρ where
  multiplicity := m
  admissibleRadius := admissibleRadius
  principalCoeff := principalTaylorScale ρ m F
  remainderCoeff := remainderCoeff
  admissibleRadius_pos := admissibleRadius_pos
  principalCoeff_pos :=
    principalTaylorScale_pos_of_iteratedDeriv_ne_zero hprincipal
  remainderCoeff_nonneg := remainderCoeff_nonneg
  taylor_lower := hLower

/--
Variant of `ofTaylorLowerBound` where theorem 8 is supplied in the current
Leibniz-jet form.
-/
noncomputable def ofLeibnizJetTaylorLowerBound
    {F : ℂ → ℂ} {ρ : ℂ}
    (hρre : 0 < ρ.re)
    (m : ℕ) (c z : ℕ → ℂ)
    (admissibleRadius remainderCoeff : ℝ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 ρ)
    (hzm : z m ≠ 0)
    (hLeibniz : iteratedDeriv m F ρ = leibnizJet m c z)
    (admissibleRadius_pos : 0 < admissibleRadius)
    (remainderCoeff_nonneg : 0 ≤ remainderCoeff)
    (hLower : ∀ δ : ℝ,
      0 < |δ| →
      |δ| ≤ admissibleRadius →
      |δ| ^ m *
          (principalTaylorScale ρ m F - remainderCoeff * |δ|) ≤
        ‖F (ρ + (δ : ℂ))‖) :
    G11LocalTaylorData F ρ :=
  ofTaylorLowerBound
    m
    admissibleRadius
    remainderCoeff
    admissibleRadius_pos
    remainderCoeff_nonneg
    (iteratedDeriv_ne_zero_of_leibnizJet_c0_of_re_pos
      hρre m c z hz hc hzm hLeibniz)
    hLower

end G11LocalTaylorData

/--
Global G11 certificate.

The ratio bound is intentionally explicit rather than hidden in an axiom: any later
Hadamard/C2 proof must construct this structure by filling these fields.
-/
structure G11Certificate (F zetaFun : ℂ → ℂ) where
  globalA : ℝ
  globalC : ℝ
  globalA_nonneg : 0 ≤ globalA
  globalC_pos : 0 < globalC
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff / (localData ρ hρ).principalCoeff ≤
      g11Envelope globalA globalC ρ

/--
The tilt/H2 route is expected to produce the stronger log-linear bound
`Bρ / Aρ ≤ A + C * log(2 + |γ|)`.  This elementary inequality upgrades that bound to
the conservative `(A + C) + C log²` envelope already consumed by `G11Certificate`.
-/
theorem affineLogRatioBound_le_g11Envelope
  {A C : ℝ} (hC : 0 ≤ C) (ρ : ℂ) :
    A + C * Real.log (2 + g11Height ρ) ≤ g11Envelope (A + C) C ρ := by
  let y : ℝ := Real.log (2 + g11Height ρ)
  have hy : C * y ≤ C + C * y ^ 2 := by
    nlinarith [hC, sq_nonneg (y - (1 / 2 : ℝ))]
  unfold g11Envelope
  change A + C * y ≤ A + C + C * y ^ 2
  linarith [hy]

/--
Special case of `affineLogRatioBound_le_g11Envelope` with zero constant term.
-/
theorem logLinearRatioBound_le_g11Envelope
    {C : ℝ} (hC : 0 ≤ C) (ρ : ℂ) :
    C * Real.log (2 + g11Height ρ) ≤ g11Envelope C C ρ := by
  simpa [g11Envelope] using
    (affineLogRatioBound_le_g11Envelope (A := 0) (C := C) hC ρ)

/--
Package an affine log-linear G11 ratio bound into the standard `G11Certificate`
interface.

This matches the roadmap statements in the notes: the C2-internal tilt route is
expected to produce `Bρ / Aρ ≤ A + C * log(2 + |γ|)`, which Lean can then convert to
the conservative `A' + C log²` envelope used by the current near-axis route.
-/
noncomputable def G11Certificate.of_affineLogRatioBound
    {F zetaFun : ℂ → ℂ}
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff / (localData ρ hρ).principalCoeff ≤
        A + C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun where
  globalA := A + C
  globalC := C
  globalA_nonneg := add_nonneg hA (le_of_lt hC)
  globalC_pos := hC
  localData := localData
  ratio_bound := by
    intro ρ hρ
    exact le_trans (ratio_bound ρ hρ)
      (affineLogRatioBound_le_g11Envelope (A := A) (C := C) (le_of_lt hC) ρ)

/--
Package a log-linear G11 ratio bound into the standard `G11Certificate` interface.

This is the intended entry point for the C2-internal tilt route: once H1 + H2 + the
horizontal/vertical resolvent analysis provide `Bρ / Aρ ≤ C * log(2 + |γ|)`, Lean can
immediately reuse the existing near-axis/G11 machinery.
-/
noncomputable def G11Certificate.of_logLinearRatioBound
    {F zetaFun : ℂ → ℂ}
    (C : ℝ) (hC : 0 < C)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff / (localData ρ hρ).principalCoeff ≤
        C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun :=
  G11Certificate.of_affineLogRatioBound 0 C (by positivity) hC localData <| by
    intro ρ hρ
    simpa using ratio_bound ρ hρ

/--
Family version of theorem-11 local Taylor data.

This packages the local quantitative input zero-by-zero before any global G11 or
tilt-sectorial ratio bound is supplied.
-/
structure G11TaylorBoundsFamilyData (F zetaFun : ℂ → ℂ) where
  multiplicity : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  admissibleRadius : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  remainderCoeff : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  admissibleRadius_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    0 < admissibleRadius ρ hρ
  remainderCoeff_nonneg : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    0 ≤ remainderCoeff ρ hρ
  principal_ne_zero : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    iteratedDeriv (multiplicity ρ hρ) F ρ ≠ 0
  taylor_lower : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) (δ : ℝ),
    0 < |δ| →
    |δ| ≤ admissibleRadius ρ hρ →
    |δ| ^ multiplicity ρ hρ *
        (principalTaylorScale ρ (multiplicity ρ hρ) F -
          remainderCoeff ρ hρ * |δ|) ≤
      ‖F (ρ + (δ : ℂ))‖

namespace G11TaylorBoundsFamilyData

noncomputable def toLocalData
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun) :
    ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ :=
  fun ρ hρ =>
    G11LocalTaylorData.ofTaylorLowerBound
      (data.multiplicity ρ hρ)
      (data.admissibleRadius ρ hρ)
      (data.remainderCoeff ρ hρ)
      (data.admissibleRadius_pos ρ hρ)
      (data.remainderCoeff_nonneg ρ hρ)
      (data.principal_ne_zero ρ hρ)
      (data.taylor_lower ρ hρ)

@[simp] theorem toLocalData_multiplicity
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.toLocalData ρ hρ).multiplicity = data.multiplicity ρ hρ := rfl

@[simp] theorem toLocalData_admissibleRadius
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.toLocalData ρ hρ).admissibleRadius = data.admissibleRadius ρ hρ := rfl

@[simp] theorem toLocalData_principalCoeff
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.toLocalData ρ hρ).principalCoeff =
      principalTaylorScale ρ (data.multiplicity ρ hρ) F := rfl

@[simp] theorem toLocalData_remainderCoeff
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.toLocalData ρ hρ).remainderCoeff = data.remainderCoeff ρ hρ := rfl

noncomputable def toG11Certificate_of_affineLogRatioBound
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) F ≤
          A + C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun :=
  G11Certificate.of_affineLogRatioBound A C hA hC data.toLocalData <| by
    intro ρ hρ
    simpa using ratio_bound ρ hρ

noncomputable def toG11Certificate_of_logLinearRatioBound
    {F zetaFun : ℂ → ℂ}
    (data : G11TaylorBoundsFamilyData F zetaFun)
    (C : ℝ) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) F ≤
          C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun :=
  G11Certificate.of_logLinearRatioBound C hC data.toLocalData <| by
    intro ρ hρ
    simpa using ratio_bound ρ hρ

end G11TaylorBoundsFamilyData

/--
Theorem-8 aware family version of theorem-11 local Taylor data.

This is the current roadmap-faithful local target: a Leibniz-jet witness for the
principal derivative, plus the quantitative Taylor lower bound.
-/
structure G11LeibnizTaylorBoundsFamilyData (F zetaFun : ℂ → ℂ) where
  multiplicity : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  cJet : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ → ℂ
  zJet : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ → ℂ
  admissibleRadius : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  remainderCoeff : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  vanishingLowerOrder : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) k,
    k < multiplicity ρ hρ →
      zJet ρ hρ k = 0
  c0_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    cJet ρ hρ 0 = c0 ρ
  top_ne_zero : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    zJet ρ hρ (multiplicity ρ hρ) ≠ 0
  leibnizJet_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    iteratedDeriv (multiplicity ρ hρ) F ρ =
      leibnizJet (multiplicity ρ hρ) (cJet ρ hρ) (zJet ρ hρ)
  admissibleRadius_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    0 < admissibleRadius ρ hρ
  remainderCoeff_nonneg : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    0 ≤ remainderCoeff ρ hρ
  taylor_lower : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) (δ : ℝ),
    0 < |δ| →
    |δ| ≤ admissibleRadius ρ hρ →
    |δ| ^ multiplicity ρ hρ *
        (principalTaylorScale ρ (multiplicity ρ hρ) F -
          remainderCoeff ρ hρ * |δ|) ≤
      ‖F (ρ + (δ : ℂ))‖

namespace G11LeibnizTaylorBoundsFamilyData

noncomputable def toTaylorBoundsFamilyData
    {F zetaFun : ℂ → ℂ}
    (data : G11LeibnizTaylorBoundsFamilyData F zetaFun) :
    G11TaylorBoundsFamilyData F zetaFun where
  multiplicity := data.multiplicity
  admissibleRadius := data.admissibleRadius
  remainderCoeff := data.remainderCoeff
  admissibleRadius_pos := data.admissibleRadius_pos
  remainderCoeff_nonneg := data.remainderCoeff_nonneg
  principal_ne_zero := by
    intro ρ hρ
    have hρre : 0 < ρ.re := by
      linarith [hρ.re_eq_half]
    exact iteratedDeriv_ne_zero_of_leibnizJet_c0_of_re_pos
      hρre
      (data.multiplicity ρ hρ)
      (data.cJet ρ hρ)
      (data.zJet ρ hρ)
      (data.vanishingLowerOrder ρ hρ)
      (data.c0_eq ρ hρ)
      (data.top_ne_zero ρ hρ)
      (data.leibnizJet_eq ρ hρ)
  taylor_lower := data.taylor_lower

noncomputable def toLocalData
    {F zetaFun : ℂ → ℂ}
    (data : G11LeibnizTaylorBoundsFamilyData F zetaFun) :
    ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ :=
  data.toTaylorBoundsFamilyData.toLocalData

noncomputable def toG11Certificate_of_affineLogRatioBound
    {F zetaFun : ℂ → ℂ}
    (data : G11LeibnizTaylorBoundsFamilyData F zetaFun)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) F ≤
          A + C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun :=
  data.toTaylorBoundsFamilyData.toG11Certificate_of_affineLogRatioBound
    A C hA hC ratio_bound

noncomputable def toG11Certificate_of_logLinearRatioBound
    {F zetaFun : ℂ → ℂ}
    (data : G11LeibnizTaylorBoundsFamilyData F zetaFun)
    (C : ℝ) (hC : 0 < C)
    (ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      data.remainderCoeff ρ hρ /
        principalTaylorScale ρ (data.multiplicity ρ hρ) F ≤
          C * Real.log (2 + g11Height ρ)) :
    G11Certificate F zetaFun :=
  data.toTaylorBoundsFamilyData.toG11Certificate_of_logLinearRatioBound
    C hC ratio_bound

end G11LeibnizTaylorBoundsFamilyData

namespace G11Certificate

/-- Radius exported by the G11 certificate for the near-axis route. -/
noncomputable def radius {F zetaFun : ℂ → ℂ} (cert : G11Certificate F zetaFun) (ρ : ℂ) : ℝ := by
  classical
  exact
    if hρ : IsCriticalZero zetaFun ρ then
      min ((1 : ℝ) / 2)
        (g11CertifiedRadius cert.globalA cert.globalC
          (cert.localData ρ hρ).admissibleRadius ρ)
    else
      (1 : ℝ) / 2

theorem radius_pos {F zetaFun : ℂ → ℂ} (cert : G11Certificate F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    0 < cert.radius ρ := by
  classical
  unfold radius
  rw [dif_pos hρ]
  exact lt_min (by norm_num)
    (g11CertifiedRadius_pos cert.globalA_nonneg cert.globalC_pos
      (cert.localData ρ hρ).admissibleRadius_pos ρ)

theorem radius_le_half {F zetaFun : ℂ → ℂ} (cert : G11Certificate F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    cert.radius ρ ≤ (1 : ℝ) / 2 := by
  classical
  unfold radius
  rw [dif_pos hρ]
  exact min_le_left _ _

theorem radius_le_g11CertifiedRadius {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) (ρ : ℂ)
    (hρ : IsCriticalZero zetaFun ρ) :
    cert.radius ρ ≤
      g11CertifiedRadius cert.globalA cert.globalC
        (cert.localData ρ hρ).admissibleRadius ρ := by
  classical
  unfold radius
  rw [dif_pos hρ]
  exact min_le_right _ _

theorem radius_le_admissibleRadius {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) (ρ : ℂ)
    (hρ : IsCriticalZero zetaFun ρ) :
    cert.radius ρ ≤ (cert.localData ρ hρ).admissibleRadius := by
  exact le_trans (radius_le_g11CertifiedRadius cert ρ hρ)
    (g11CertifiedRadius_le_baseRadius cert.globalA cert.globalC
      (cert.localData ρ hρ).admissibleRadius ρ)

theorem radius_le_localZeroFreeRadius {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) (ρ : ℂ)
    (hρ : IsCriticalZero zetaFun ρ) :
    cert.radius ρ ≤
      localZeroFreeRadius
        (cert.localData ρ hρ).principalCoeff
        (cert.localData ρ hρ).remainderCoeff
        (cert.localData ρ hρ).admissibleRadius := by
  have hAρ : 0 < (cert.localData ρ hρ).principalCoeff :=
    (cert.localData ρ hρ).principalCoeff_pos
  have hBρ : 0 ≤ (cert.localData ρ hρ).remainderCoeff :=
    (cert.localData ρ hρ).remainderCoeff_nonneg
  exact le_trans (radius_le_g11CertifiedRadius cert ρ hρ)
    (g11CertifiedRadius_le_localZeroFreeRadius
      cert.globalA_nonneg cert.globalC_pos hAρ hBρ
      (cert.ratio_bound ρ hρ))

theorem nonvanishing_of_mem_transversalWindow {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) {ρ s : ℂ}
    (hρ : IsCriticalZero zetaFun ρ)
    (hs : s ∈ transversalWindow ρ (cert.radius ρ)) :
    F s ≠ 0 := by
  rcases hs with ⟨hsIm, hδpos, hδlt⟩
  let δ : ℝ := s.re - ρ.re
  have hδ_admissible : |δ| ≤ (cert.localData ρ hρ).admissibleRadius := by
    exact le_trans (le_of_lt hδlt) (radius_le_admissibleRadius cert ρ hρ)
  have hδ_local : |δ| <
      localZeroFreeRadius
        (cert.localData ρ hρ).principalCoeff
        (cert.localData ρ hρ).remainderCoeff
        (cert.localData ρ hρ).admissibleRadius := by
    exact lt_of_lt_of_le hδlt (radius_le_localZeroFreeRadius cert ρ hρ)
  have hs_eq : s = ρ + (δ : ℂ) := by
    apply Complex.ext
    · simp [δ]
    · simp [δ, hsIm]
  have hlower :=
    (cert.localData ρ hρ).taylor_lower δ hδpos hδ_admissible
  have hnonzero :
      F (ρ + (δ : ℂ)) ≠ 0 :=
    nonzero_of_taylorLowerBound
      (cert.localData ρ hρ).principalCoeff_pos
      (cert.localData ρ hρ).remainderCoeff_nonneg
      hδpos hδ_local hlower
  simpa [hs_eq]

/-- A G11 certificate is exactly enough to produce the near-axis roadmap certificate. -/
def toNearAxisCertificate {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) :
    NearAxisCertificate F zetaFun where
  radius := cert.radius
  radius_pos := cert.radius_pos
  radius_le_half := cert.radius_le_half
  nonvanishing := by
    intro ρ s hρ hs
    exact cert.nonvanishing_of_mem_transversalWindow hρ hs

end G11Certificate

/-- Roadmap theorem: G11 gives zero-freeness in the near-axis region. -/
theorem near_axis_nonzero_from_G11 {F zetaFun : ℂ → ℂ}
    (cert : G11Certificate F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun cert.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  cert.toNearAxisCertificate.nonvanishing_of_mem hs

end
end C2
