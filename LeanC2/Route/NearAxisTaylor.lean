import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Norm
import LeanC2.Identity.C0
import LeanC2.Route.NearAxis

namespace C2

open scoped Topology

noncomputable section

/-!
Generic near-axis Taylor utilities.

This file provides the reusable algebraic and analytic lemmas used to assemble a
`NearAxisCertificate`: the finite Leibniz jet at a zero of multiplicity `m`, the
elementary radius bookkeeping for Taylor lower bounds, and the generic analytic
step that turns a nonzero `m`th iterated derivative into local punctured
nonvanishing.
-/

/-- Finite Leibniz jet for the `m`th derivative of a product. -/
def leibnizJet (m : ℕ) (c z : ℕ → ℂ) : ℂ :=
  Finset.sum (Finset.range (m + 1)) fun j =>
    (Nat.choose m j : ℂ) * c j * z (m - j)

theorem leibnizJet_eq_leadingTerm_of_vanishingLowerOrder
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) :
    leibnizJet m c z = c 0 * z m := by
  unfold leibnizJet
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hjmem hj0
    have hjlt : j < m + 1 := Finset.mem_range.mp hjmem
    have hjle : j ≤ m := Nat.lt_succ_iff.mp hjlt
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hmpos : 0 < m := lt_of_lt_of_le hjpos hjle
    have hmjlt : m - j < m := Nat.sub_lt hmpos hjpos
    have hzj : z (m - j) = 0 := hz (m - j) hmjlt
    simp [hzj]
  · intro h0
    simp at h0

theorem leibnizJet_ne_zero_of_vanishingLowerOrder
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc0 : c 0 ≠ 0)
    (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  rw [leibnizJet_eq_leadingTerm_of_vanishingLowerOrder m c z hz]
  exact mul_ne_zero hc0 hzm

theorem leibnizJet_ne_zero_of_c0_of_re_pos
    {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 s)
    (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  have hc0s : c0 s ≠ 0 := c0_ne_zero_of_re_pos hs
  have hc0 : c 0 ≠ 0 := by
    intro hc0z
    apply hc0s
    simpa [hc] using hc0z
  exact leibnizJet_ne_zero_of_vanishingLowerOrder m c z hz hc0 hzm

/-- The Leibniz-jet witness forces the `m`th iterated derivative to be nonzero. -/
theorem iteratedDeriv_ne_zero_of_leibnizJet_c0_of_re_pos
    {s : ℂ} (hs : 0 < s.re)
    {F : ℂ → ℂ}
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 s)
    (hzm : z m ≠ 0)
    (hLeibniz : iteratedDeriv m F s = leibnizJet m c z) :
    iteratedDeriv m F s ≠ 0 := by
  intro hzero
  have hsum0 : leibnizJet m c z = 0 := by
    simpa [hLeibniz] using hzero
  exact (leibnizJet_ne_zero_of_c0_of_re_pos hs m c z hz hc hzm) hsum0

theorem not_eventually_zero_of_iteratedDeriv_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (m : ℕ)
    (hFm : iteratedDeriv m F ρ ≠ 0) :
    ¬ ∀ᶠ z in 𝓝 ρ, F z = 0 := by
  intro hZero
  have hEq : F =ᶠ[𝓝 ρ] fun _ : ℂ => (0 : ℂ) := by
    simpa [Filter.EventuallyEq] using hZero
  have hDerivEq :
      iteratedDeriv m F ρ = iteratedDeriv m (fun _ : ℂ => (0 : ℂ)) ρ := by
    simpa using hEq.iteratedDeriv_eq m
  exact hFm (by simpa using hDerivEq)

theorem analyticOrderAt_ne_top_of_iteratedDeriv_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (m : ℕ)
    (hFm : iteratedDeriv m F ρ ≠ 0) :
    analyticOrderAt F ρ ≠ ⊤ := by
  intro hTop
  exact not_eventually_zero_of_iteratedDeriv_ne_zero m hFm
    (analyticOrderAt_eq_top.mp hTop)

theorem eventually_ne_zero_of_iteratedDeriv_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (hF : AnalyticAt ℂ F ρ)
    (m : ℕ)
    (hFm : iteratedDeriv m F ρ ≠ 0) :
    ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0 := by
  have hNotZero : ¬ ∀ᶠ z in 𝓝 ρ, F z = 0 :=
    not_eventually_zero_of_iteratedDeriv_ne_zero m hFm
  exact (hF.eventually_eq_zero_or_eventually_ne_zero).resolve_left hNotZero

theorem finiteOrderZero_and_eventually_ne_zero_of_iteratedDeriv_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (hF : AnalyticAt ℂ F ρ)
    (hFρ : F ρ = 0)
    (m : ℕ)
    (hFm : iteratedDeriv m F ρ ≠ 0) :
    analyticOrderAt F ρ ≠ 0 ∧
      analyticOrderAt F ρ ≠ ⊤ ∧
      ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0 := by
  refine ⟨(hF.analyticOrderAt_ne_zero).2 hFρ,
    analyticOrderAt_ne_top_of_iteratedDeriv_ne_zero m hFm,
    eventually_ne_zero_of_iteratedDeriv_ne_zero hF m hFm⟩

theorem eventually_ne_zero_of_leibnizJet_c0_of_re_pos
    {s : ℂ} (hs : 0 < s.re)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F s)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 s)
    (hzm : z m ≠ 0)
    (hLeibniz : iteratedDeriv m F s = leibnizJet m c z) :
    ∀ᶠ w in 𝓝[≠] s, F w ≠ 0 := by
  have hFm : iteratedDeriv m F s ≠ 0 :=
    iteratedDeriv_ne_zero_of_leibnizJet_c0_of_re_pos hs m c z hz hc hzm hLeibniz
  exact eventually_ne_zero_of_iteratedDeriv_ne_zero hF m hFm

theorem finiteOrderZero_and_eventually_ne_zero_of_leibnizJet_c0_of_re_pos
    {s : ℂ} (hs : 0 < s.re)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F s) (hFs : F s = 0)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 s)
    (hzm : z m ≠ 0)
    (hLeibniz : iteratedDeriv m F s = leibnizJet m c z) :
    analyticOrderAt F s ≠ 0 ∧
      analyticOrderAt F s ≠ ⊤ ∧
      ∀ᶠ w in 𝓝[≠] s, F w ≠ 0 := by
  have hFm : iteratedDeriv m F s ≠ 0 :=
    iteratedDeriv_ne_zero_of_leibnizJet_c0_of_re_pos hs m c z hz hc hzm hLeibniz
  exact finiteOrderZero_and_eventually_ne_zero_of_iteratedDeriv_ne_zero
    hF hFs m hFm

/-- The leading Taylor scale `‖F^(m)(ρ)‖ / m!`. -/
def principalTaylorScale (ρ : ℂ) (m : ℕ) (F : ℂ → ℂ) : ℝ :=
  ‖iteratedDeriv m F ρ‖ / (m.factorial : ℝ)

/-- Radius allowed by a Taylor lower bound `A - B |δ|`. -/
def localZeroFreeRadius (A B r : ℝ) : ℝ :=
  if B = 0 then r else min r (A / B)

theorem principalTaylorScale_pos_of_iteratedDeriv_ne_zero
    {ρ : ℂ} {m : ℕ} {F : ℂ → ℂ}
    (hF : iteratedDeriv m F ρ ≠ 0) :
    0 < principalTaylorScale ρ m F := by
  unfold principalTaylorScale
  have hnorm : 0 < ‖iteratedDeriv m F ρ‖ := norm_pos_iff.mpr hF
  have hfac : 0 < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  exact div_pos hnorm hfac

@[simp] theorem localZeroFreeRadius_of_zero_remainder (A r : ℝ) :
    localZeroFreeRadius A 0 r = r := by
  simp [localZeroFreeRadius]

theorem localZeroFreeRadius_of_pos_remainder
    {A B r : ℝ} (hB : 0 < B) :
    localZeroFreeRadius A B r = min r (A / B) := by
  simp [localZeroFreeRadius, hB.ne']

theorem localZeroFreeRadius_pos
    {A B r : ℝ}
    (hA : 0 < A)
    (hB : 0 ≤ B)
    (hr : 0 < r) :
    0 < localZeroFreeRadius A B r := by
  by_cases hB0 : B = 0
  · simpa [localZeroFreeRadius, hB0] using hr
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    rw [localZeroFreeRadius_of_pos_remainder hBpos]
    exact lt_min hr (div_pos hA hBpos)

theorem localZeroFreeRadius_le_radius (A B r : ℝ) :
    localZeroFreeRadius A B r ≤ r := by
  by_cases hB0 : B = 0
  · simp [localZeroFreeRadius, hB0]
  · rw [localZeroFreeRadius, if_neg hB0]
    exact min_le_left _ _

theorem le_localZeroFreeRadius_of_zero_remainder
    {x A r : ℝ}
    (hx : x ≤ r) :
    x ≤ localZeroFreeRadius A 0 r := by
  simpa [localZeroFreeRadius] using hx

theorem le_localZeroFreeRadius_of_bounds
    {x A B r : ℝ}
    (hB : B ≠ 0)
    (hxR : x ≤ r)
    (hxAB : x ≤ A / B) :
    x ≤ localZeroFreeRadius A B r := by
  rw [localZeroFreeRadius, if_neg hB]
  exact le_min hxR hxAB

theorem principalPart_pos_of_abs_lt_localZeroFreeRadius
    {A B r δ : ℝ}
    (hA : 0 < A)
    (hB : 0 ≤ B)
    (hδ : |δ| < localZeroFreeRadius A B r) :
    0 < A - B * |δ| := by
  by_cases hB0 : B = 0
  · simp [hB0, hA]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    rw [localZeroFreeRadius_of_pos_remainder hBpos] at hδ
    have hlt : |δ| < A / B := lt_of_lt_of_le hδ (min_le_right _ _)
    have hmul : B * |δ| < A := by
      have := (lt_div_iff₀ hBpos).mp hlt
      simpa [mul_comm] using this
    linarith

theorem nonzero_of_taylorLowerBound
    {Fδ : ℂ} {m : ℕ} {A B r δ : ℝ}
    (hA : 0 < A)
    (hB : 0 ≤ B)
    (hδ0 : 0 < |δ|)
    (hδ : |δ| < localZeroFreeRadius A B r)
    (hLower : |δ| ^ m * (A - B * |δ|) ≤ ‖Fδ‖) :
    Fδ ≠ 0 := by
  have hmain : 0 < A - B * |δ| :=
    principalPart_pos_of_abs_lt_localZeroFreeRadius hA hB hδ
  have hpow : 0 < |δ| ^ m := pow_pos hδ0 _
  have hnorm : 0 < ‖Fδ‖ := lt_of_lt_of_le (mul_pos hpow hmain) hLower
  exact norm_pos_iff.mp hnorm

theorem exists_transversalRadius_of_eventually_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (hEventually : ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0) :
    ∃ r : ℝ,
      0 < r ∧
      r ≤ (1 : ℝ) / 2 ∧
      ∀ ⦃s : ℂ⦄, s ∈ transversalWindow ρ r -> F s ≠ 0 := by
  let t : Set ℂ := {z : ℂ | F z ≠ 0}
  rcases (mem_nhdsWithin.mp hEventually) with ⟨u, huOpen, hρu, huSub⟩
  rcases Metric.mem_nhds_iff.mp (huOpen.mem_nhds hρu) with ⟨ε, hεpos, hεball⟩
  refine ⟨min ε ((1 : ℝ) / 2), lt_min hεpos (by norm_num), min_le_right _ _, ?_⟩
  intro s hs
  rcases hs with ⟨hsIm, hsPos, hsLt⟩
  have hsNe : s ≠ ρ := by
    intro hsEq
    have : |s.re - ρ.re| = 0 := by simp [hsEq]
    linarith
  have hsDist : dist s ρ = |s.re - ρ.re| := by
    rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
    simp [hsIm]
    simpa [pow_two] using (Real.sqrt_sq_eq_abs (s.re - ρ.re))
  have hsBall : s ∈ Metric.ball ρ ε := by
    change dist s ρ < ε
    rw [hsDist]
    exact lt_of_lt_of_le hsLt (min_le_left _ _)
  have hsU : s ∈ u := hεball hsBall
  have hsComp : s ∈ ({ρ}ᶜ : Set ℂ) := by
    simpa using hsNe
  exact huSub ⟨hsU, hsComp⟩

theorem exists_transversalRadius_of_iteratedDeriv_ne_zero
    {F : ℂ → ℂ} {ρ : ℂ}
    (hF : AnalyticAt ℂ F ρ)
    {m : ℕ}
    (hFm : iteratedDeriv m F ρ ≠ 0) :
    ∃ r : ℝ,
      0 < r ∧
      r ≤ (1 : ℝ) / 2 ∧
      ∀ ⦃s : ℂ⦄, s ∈ transversalWindow ρ r -> F s ≠ 0 := by
  exact exists_transversalRadius_of_eventually_ne_zero
    (eventually_ne_zero_of_iteratedDeriv_ne_zero hF m hFm)

theorem exists_transversalRadius_of_leibnizJet_c0_of_re_pos
    {s : ℂ} (hs : 0 < s.re)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F s)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hc : c 0 = c0 s)
    (hzm : z m ≠ 0)
    (hLeibniz : iteratedDeriv m F s = leibnizJet m c z) :
    ∃ r : ℝ,
      0 < r ∧
      r ≤ (1 : ℝ) / 2 ∧
      ∀ ⦃w : ℂ⦄, w ∈ transversalWindow s r -> F w ≠ 0 := by
  exact exists_transversalRadius_of_eventually_ne_zero
    (eventually_ne_zero_of_leibnizJet_c0_of_re_pos hs hF m c z hz hc hzm hLeibniz)

/--
Local Leibniz-jet witnesses along the critical line produce a
`NearAxisCertificate` for the route.
-/
noncomputable def NearAxisCertificate.of_leibnizJet_c0
    {F zetaFun : ℂ → ℂ}
    (hAnalytic : ∀ rho, IsCriticalZero zetaFun rho -> AnalyticAt ℂ F rho)
    (hJet : ∀ rho, IsCriticalZero zetaFun rho ->
      ∃ m : ℕ, ∃ c z : ℕ → ℂ,
        (∀ k < m, z k = 0) ∧
        c 0 = c0 rho ∧
        z m ≠ 0 ∧
        iteratedDeriv m F rho = leibnizJet m c z) :
    NearAxisCertificate F zetaFun := by
  classical
  have hex : ∀ rho, IsCriticalZero zetaFun rho ->
      ∃ r : ℝ,
        0 < r ∧
        r ≤ (1 : ℝ) / 2 ∧
        ∀ ⦃w : ℂ⦄, w ∈ transversalWindow rho r -> F w ≠ 0 := by
    intro rho hrho
    rcases hJet rho hrho with ⟨m, c, z, hz, hc, hzm, hLeibniz⟩
    have hs : 0 < rho.re := by
      linarith [hrho.re_eq_half]
    exact exists_transversalRadius_of_leibnizJet_c0_of_re_pos
      hs (hAnalytic rho hrho) m c z hz hc hzm hLeibniz
  let radius : ℂ → ℝ := fun rho =>
    if hrho : IsCriticalZero zetaFun rho then
      Classical.choose (hex rho hrho)
    else
      (1 : ℝ) / 2
  refine
    { radius := radius
      radius_pos := ?_
      radius_le_half := ?_
      nonvanishing := ?_ }
  · intro rho hrho
    simpa [radius, hrho] using (Classical.choose_spec (hex rho hrho)).1
  · intro rho hrho
    simpa [radius, hrho] using (Classical.choose_spec (hex rho hrho)).2.1
  · intro rho s hrho hs
    have hnonzero := (Classical.choose_spec (hex rho hrho)).2.2
    exact hnonzero (by simpa [radius, hrho] using hs)

noncomputable def NearAxisCertificate.of_eventually_ne_zero
    {F zetaFun : ℂ → ℂ}
    (hEventually : ∀ rho, IsCriticalZero zetaFun rho ->
      ∀ᶠ z in 𝓝[≠] rho, F z ≠ 0) :
    NearAxisCertificate F zetaFun := by
  classical
  have hex : ∀ rho, IsCriticalZero zetaFun rho ->
      ∃ r : ℝ,
        0 < r ∧
        r ≤ (1 : ℝ) / 2 ∧
        ∀ ⦃w : ℂ⦄, w ∈ transversalWindow rho r -> F w ≠ 0 := by
    intro rho hrho
    exact exists_transversalRadius_of_eventually_ne_zero (hEventually rho hrho)
  let radius : ℂ → ℝ := fun rho =>
    if hrho : IsCriticalZero zetaFun rho then
      Classical.choose (hex rho hrho)
    else
      (1 : ℝ) / 2
  refine
    { radius := radius
      radius_pos := ?_
      radius_le_half := ?_
      nonvanishing := ?_ }
  · intro rho hrho
    simpa [radius, hrho] using (Classical.choose_spec (hex rho hrho)).1
  · intro rho hrho
    simpa [radius, hrho] using (Classical.choose_spec (hex rho hrho)).2.1
  · intro rho s hrho hs
    have hnonzero := (Classical.choose_spec (hex rho hrho)).2.2
    exact hnonzero (by simpa [radius, hrho] using hs)

end
end C2
