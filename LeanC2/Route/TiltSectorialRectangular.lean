import LeanC2.Route.TiltSectorial
import LeanC2.Operators.TruncatedGenuine

namespace C2

noncomputable section

/-!
Concrete rectangular support for the tilt-sectorial G11 route.

`TiltSectorial.lean` packages the abstract finite-family H1+H2 route.  This file
specializes that interface to the explicit finite C2 rectangle of bracket addresses
`(k, m)` with `2 ≤ k ≤ K` and `m ≤ M` odd, together with the concrete log-height
`H_C2(n) = log n` on the center `n = 2^k m`.
-/

/-- Log-height `H_C2(n) = log n` attached to a finite C2 address. -/
noncomputable def c2AddressLogHeight (a : C2Address) : ℝ :=
  Real.log (c2Center a.depth a.core : ℝ)

theorem c2Center_pos_of_validAddress {a : C2Address} (ha : IsValidC2Address a) :
    0 < c2Center a.depth a.core := by
  rcases ha with ⟨_hk, hodd⟩
  rcases hodd with ⟨n, hn⟩
  rw [hn]
  unfold c2Center
  positivity

theorem c2AddressLogHeight_nonneg_of_validAddress {a : C2Address}
    (ha : IsValidC2Address a) :
    0 ≤ c2AddressLogHeight a := by
  unfold c2AddressLogHeight
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_of_lt (c2Center_pos_of_validAddress ha)

theorem c2AddressLogHeight_nonneg_of_mem_c2Rectangle
    {a : C2Address} {K M : ℕ} (ha : a ∈ c2Rectangle K M) :
    0 ≤ c2AddressLogHeight a :=
  c2AddressLogHeight_nonneg_of_validAddress (c2Rectangle_valid K M a ha)

theorem c2Center_le_of_mem_c2Rectangle
    {a : C2Address} {K M : ℕ} (ha : a ∈ c2Rectangle K M) :
    c2Center a.depth a.core ≤ c2Center K M := by
  rw [mem_c2Rectangle] at ha
  unfold c2Center
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_right (by norm_num) ha.2.1)
    ha.2.2.1

theorem c2Center_top_pos_of_mem_c2Rectangle
    {a : C2Address} {K M : ℕ} (ha : a ∈ c2Rectangle K M) :
    0 < c2Center K M := by
  rw [mem_c2Rectangle] at ha
  rcases ha.2.2.2 with ⟨n, hn⟩
  have hcore_pos : 0 < a.core := by
    rw [hn]
    positivity
  have hM_pos : 0 < M := lt_of_lt_of_le hcore_pos ha.2.2.1
  unfold c2Center
  exact Nat.mul_pos (pow_pos (by norm_num) _) hM_pos

theorem c2AddressLogHeight_le_logTop_of_mem_c2Rectangle
    {a : C2Address} {K M : ℕ} (ha : a ∈ c2Rectangle K M) :
    c2AddressLogHeight a ≤ Real.log (c2Center K M : ℝ) := by
  unfold c2AddressLogHeight
  have hcenter_pos : 0 < (c2Center a.depth a.core : ℝ) := by
    exact_mod_cast c2Center_pos_of_validAddress (c2Rectangle_valid K M a ha)
  have hcenter_le :
      (c2Center a.depth a.core : ℝ) ≤ (c2Center K M : ℝ) := by
    exact_mod_cast c2Center_le_of_mem_c2Rectangle ha
  exact Real.log_le_log hcenter_pos hcenter_le

theorem c2AddressLogHeight_le_of_topHeightBound
    {ρ : ℂ} {a : C2Address} {K M : ℕ} {supportConstant : ℝ}
    (ha : a ∈ c2Rectangle K M)
    (htop : Real.log (c2Center K M : ℝ) ≤
      supportConstant * Real.log (2 + g11Height ρ)) :
    c2AddressLogHeight a ≤ supportConstant * Real.log (2 + g11Height ρ) := by
  exact le_trans
    (c2AddressLogHeight_le_logTop_of_mem_c2Rectangle ha)
    htop

theorem log_c2Center_eq_depth_mul_log_two_add_log_core
    {K M : ℕ} (hM : 0 < M) :
    Real.log (c2Center K M : ℝ) = (K : ℝ) * Real.log 2 + Real.log (M : ℝ) := by
  unfold c2Center
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow]
  · ring_nf
  · exact_mod_cast pow_ne_zero K (by norm_num : (2 : ℕ) ≠ 0)
  · exact_mod_cast Nat.ne_of_gt hM

theorem c2AddressLogHeight_le_explicitCutoffLog_of_mem_c2Rectangle
    {a : C2Address} {K M : ℕ} (ha : a ∈ c2Rectangle K M) (hM : 0 < M) :
    c2AddressLogHeight a ≤ (K : ℝ) * Real.log 2 + Real.log (M : ℝ) := by
  rw [← log_c2Center_eq_depth_mul_log_two_add_log_core hM]
  exact c2AddressLogHeight_le_logTop_of_mem_c2Rectangle ha

theorem c2TopHeightBound_of_explicitCutoffLog
    {ρ : ℂ} {K M : ℕ} {supportConstant : ℝ}
    (hM : 0 < M)
    (hexplicit : (K : ℝ) * Real.log 2 + Real.log (M : ℝ) ≤
      supportConstant * Real.log (2 + g11Height ρ)) :
    Real.log (c2Center K M : ℝ) ≤ supportConstant * Real.log (2 + g11Height ρ) := by
  rw [log_c2Center_eq_depth_mul_log_two_add_log_core hM]
  exact hexplicit

/-- Explicit central summand on the finite C2 rectangle. -/
noncomputable def genuineCentralRectangularAddressTerm (s : ℂ) (a : C2Address) : ℂ :=
  (2 : ℂ) * (verticalRatio s ^ a.depth * complexDirichletCoeff s a.core)

theorem centerRemainderTerm_eq_genuineCentralRectangularAddressTerm
    (s : ℂ) {a : C2Address} (ha : IsValidC2Address a) :
    centerRemainderTerm (complexDirichletCoeff s) a.depth a.core =
      genuineCentralRectangularAddressTerm s a := by
  rcases ha with ⟨_hk, hodd⟩
  have hcore_pos : 0 < a.core := by
    rcases hodd with ⟨n, hn⟩
    rw [hn]
    positivity
  have hcore_ne : a.core ≠ 0 := Nat.ne_of_gt hcore_pos
  unfold genuineCentralRectangularAddressTerm
  rw [centerRemainderTerm_eq_geometric]
  unfold centerGeometricTerm
  rw [complexDirichletCoeff_mul s (pow_ne_zero a.depth (by norm_num : (2 : ℕ) ≠ 0)) hcore_ne]
  rw [complexDirichletCoeff_two_pow]
  have hhalf : algebraMap ℚ ℂ ((2 : ℚ)⁻¹) = (1 / 2 : ℂ) := by norm_num
  rw [dyadicWeight_eq_inv_pow, map_pow, hhalf]
  calc
    (2 : ℂ) * ((1 / 2 : ℂ) ^ a.depth) *
        (complexDirichletCoeff s 2 ^ a.depth * complexDirichletCoeff s a.core)
      = (2 : ℂ) *
          ((((1 / 2 : ℂ) ^ a.depth) * complexDirichletCoeff s 2 ^ a.depth) *
            complexDirichletCoeff s a.core) := by ring
    _ = (2 : ℂ) *
          ((((1 / 2 : ℂ) * complexDirichletCoeff s 2) ^ a.depth) *
            complexDirichletCoeff s a.core) := by
            rw [← mul_pow]
    _ = (2 : ℂ) * (verticalRatio s ^ a.depth * complexDirichletCoeff s a.core) := by
            rw [verticalRatio_eq]

theorem rectangularCentral_eq_centerRemainderFiniteSum (s : ℂ) (K M : ℕ) :
    rectangularCentral s K M =
      centerRemainderFiniteSum (complexDirichletCoeff s) (c2Rectangle K M) := by
  unfold rectangularCentral
  rw [← complexDirichletKernel_lateral_sub_bracket_eq_factoredCenter]
  change
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M,
        directPairTerm (complexDirichletCoeff s) k m) -
      (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M,
        bracketTerm (complexDirichletCoeff s) k m) =
        centerRemainderFiniteSum (complexDirichletCoeff s) (c2Rectangle K M)
  rw [← directPairFiniteSum_c2Rectangle (f := complexDirichletCoeff s) K M]
  rw [← bracketFiniteSum_c2Rectangle (f := complexDirichletCoeff s) K M]
  exact rectangular_lateral_cancellation (R := ℂ) (complexDirichletCoeff s) K M

theorem rectangularCentral_eq_genuineCentralRectangularSum (s : ℂ) (K M : ℕ) :
    rectangularCentral s K M =
      Finset.sum (c2Rectangle K M) (genuineCentralRectangularAddressTerm s) := by
  rw [rectangularCentral_eq_centerRemainderFiniteSum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  exact centerRemainderTerm_eq_genuineCentralRectangularAddressTerm s
    (c2Rectangle_valid K M a ha)

/-- Canonical C2 rectangular central contribution indexed by finite addresses. -/
noncomputable def c2RectangularCentralContribution (s : ℂ) : C2Address → ℂ :=
  genuineCentralRectangularAddressTerm s

theorem norm_rectangularCentral_eq_norm_sum_c2RectangularCentralContribution
    (s : ℂ) (K M : ℕ) :
    ‖rectangularCentral s K M‖ =
      ‖Finset.sum (c2Rectangle K M) (c2RectangularCentralContribution s)‖ := by
  rw [rectangularCentral_eq_genuineCentralRectangularSum]
  simp [c2RectangularCentralContribution]

/--
Bound-level H1+H2 data specialized to the explicit finite C2 rectangle.

Compared with `SectorialMomentG11BoundsData`, the support is no longer arbitrary:
future concrete proofs only need to populate the contributions on the rectangle
`c2Rectangle (Kρ) (Mρ)` and verify the logarithmic support / sectorial coherence
hypotheses on that explicit finite family.
-/
structure C2RectangularMomentG11BoundsData (F zetaFun : ℂ → ℂ) where
  supportConstant : ℝ
  aperture : ℝ
  supportConstant_pos : 0 < supportConstant
  aperture_nonneg : 0 ≤ aperture
  aperture_lt_pi_div_two : aperture < Real.pi / 2
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  contribution : ∀ ρ, IsCriticalZero zetaFun ρ → C2Address → ℂ
  tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  height_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) {a : C2Address},
    a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
      c2AddressLogHeight a ≤ supportConstant * Real.log (2 + g11Height ρ)
  tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ))
  sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    SectorialNormCoherence
      (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
      (contribution ρ hρ)
      aperture
  principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).principalCoeff =
      ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
          (contribution ρ hρ)‖
  remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff ≤
      ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
          (fun a =>
            (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
              contribution ρ hρ a))‖ /
        ((localData ρ hρ).multiplicity + 1 : ℝ)

noncomputable def C2RectangularMomentG11BoundsData.ofTopHeightBound
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (contribution : ∀ ρ, IsCriticalZero zetaFun ρ → C2Address → ℂ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (topHeightBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      Real.log (c2Center (depthCutoff ρ hρ) (coreCutoff ρ hρ) : ℝ) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      SectorialNormCoherence
        (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
        (contribution ρ hρ)
        aperture)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (contribution ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                contribution ρ hρ a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularMomentG11BoundsData F zetaFun where
  supportConstant := supportConstant
  aperture := aperture
  supportConstant_pos := supportConstant_pos
  aperture_nonneg := aperture_nonneg
  aperture_lt_pi_div_two := aperture_lt_pi_div_two
  localData := localData
  depthCutoff := depthCutoff
  coreCutoff := coreCutoff
  contribution := contribution
  tiltDelta := tiltDelta
  height_bound := by
    intro ρ hρ a ha
    exact c2AddressLogHeight_le_of_topHeightBound ha (topHeightBound ρ hρ)
  tiltDelta_mem := tiltDelta_mem
  sectorial := sectorial
  principalCoeff_eq := principalCoeff_eq
  remainderCoeff_le := remainderCoeff_le

noncomputable def C2RectangularMomentG11BoundsData.ofCentralTerms
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (centralPoint : ∀ ρ, IsCriticalZero zetaFun ρ → ℂ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (topHeightBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      Real.log (c2Center (depthCutoff ρ hρ) (coreCutoff ρ hρ) : ℝ) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      SectorialNormCoherence
        (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
        (c2RectangularCentralContribution (centralPoint ρ hρ))
        aperture)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖rectangularCentral (centralPoint ρ hρ) (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution (centralPoint ρ hρ) a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularMomentG11BoundsData F zetaFun :=
  C2RectangularMomentG11BoundsData.ofTopHeightBound
    supportConstant aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    localData
    depthCutoff
    coreCutoff
    (fun ρ hρ => c2RectangularCentralContribution (centralPoint ρ hρ))
    tiltDelta
    topHeightBound
    tiltDelta_mem
    sectorial
    (by
      intro ρ hρ
      calc
        (localData ρ hρ).principalCoeff =
            ‖rectangularCentral (centralPoint ρ hρ)
                (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖ :=
          principalCoeff_eq ρ hρ
        _ = ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
              (c2RectangularCentralContribution (centralPoint ρ hρ))‖ := by
            simpa [c2RectangularCentralContribution] using
              norm_rectangularCentral_eq_norm_sum_c2RectangularCentralContribution
                (centralPoint ρ hρ) (depthCutoff ρ hρ) (coreCutoff ρ hρ))
    remainderCoeff_le

noncomputable def C2RectangularMomentG11BoundsData.ofCriticalZeroCentralTerms
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (topHeightBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      Real.log (c2Center (depthCutoff ρ hρ) (coreCutoff ρ hρ) : ℝ) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      SectorialNormCoherence
        (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
        (c2RectangularCentralContribution ρ)
        aperture)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularMomentG11BoundsData F zetaFun :=
  C2RectangularMomentG11BoundsData.ofCentralTerms
    supportConstant aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    localData
    depthCutoff
    coreCutoff
    (fun ρ _hρ => ρ)
    tiltDelta
    topHeightBound
    tiltDelta_mem
    sectorial
    principalCoeff_eq
    remainderCoeff_le

def C2RectangularMomentG11BoundsData.support
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) : Finset C2Address :=
  c2Rectangle (data.depthCutoff ρ hρ) (data.coreCutoff ρ hρ)

noncomputable def C2RectangularMomentG11BoundsData.toSectorialMomentG11BoundsData
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun) :
    SectorialMomentG11BoundsData F zetaFun where
  supportConstant := data.supportConstant
  aperture := data.aperture
  supportConstant_pos := data.supportConstant_pos
  aperture_nonneg := data.aperture_nonneg
  aperture_lt_pi_div_two := data.aperture_lt_pi_div_two
  localData := data.localData
  index := fun _ρ _hρ => C2Address
  support := data.support
  contribution := data.contribution
  height := fun _ρ _hρ a => c2AddressLogHeight a
  tiltDelta := data.tiltDelta
  height_mem_support := by
    intro ρ hρ a ha
    exact ⟨c2AddressLogHeight_nonneg_of_mem_c2Rectangle ha, data.height_bound ρ hρ ha⟩
  tiltDelta_mem := data.tiltDelta_mem
  sectorial := data.sectorial
  principalCoeff_eq := data.principalCoeff_eq
  remainderCoeff_le := data.remainderCoeff_le

theorem C2RectangularMomentG11BoundsData.moment_ratio_bound
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.localData ρ hρ).remainderCoeff / (data.localData ρ hρ).principalCoeff ≤
      ((1 : ℝ) / ((data.localData ρ hρ).multiplicity + 1 : ℝ)) *
        sectorialLogConstant data.supportConstant data.aperture *
        Real.log (2 + g11Height ρ) := by
  exact data.toSectorialMomentG11BoundsData.moment_ratio_bound ρ hρ

noncomputable def C2RectangularMomentG11BoundsData.toG11Data
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun) :
    SectorialMomentG11Data F zetaFun :=
  data.toSectorialMomentG11BoundsData.toG11Data

noncomputable def C2RectangularMomentG11BoundsData.toG11Certificate
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun) :
    G11Certificate F zetaFun :=
  data.toSectorialMomentG11BoundsData.toG11Certificate

theorem near_axis_nonzero_from_rectangularMomentG11Bounds
    {F zetaFun : ℂ → ℂ} (data : C2RectangularMomentG11BoundsData F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun data.toG11Certificate.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  near_axis_nonzero_from_G11 data.toG11Certificate hs

/--
Concrete H1+H2 package already specialized to the actual rectangular central family
evaluated at the critical zero `ρ` itself.

This is the narrow interface the future concrete tilt proof is expected to fill:
one top-height bound for H1, one sectorial-coherence statement for H2, and the
comparison of the tilted first nonzero moment with the local Taylor remainder.
-/
structure C2RectangularCentralMomentG11BoundsData (F zetaFun : ℂ → ℂ) where
  supportConstant : ℝ
  aperture : ℝ
  supportConstant_pos : 0 < supportConstant
  aperture_nonneg : 0 ≤ aperture
  aperture_lt_pi_div_two : aperture < Real.pi / 2
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  topHeightBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    Real.log (c2Center (depthCutoff ρ hρ) (coreCutoff ρ hρ) : ℝ) ≤
      supportConstant * Real.log (2 + g11Height ρ)
  tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ))
  sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    SectorialNormCoherence
      (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
      (c2RectangularCentralContribution ρ)
      aperture
  principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).principalCoeff =
      ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖
  remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff ≤
      ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
          (fun a =>
            (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
              c2RectangularCentralContribution ρ a))‖ /
        ((localData ρ hρ).multiplicity + 1 : ℝ)

noncomputable def C2RectangularCentralMomentG11BoundsData.toRectangularMomentG11BoundsData
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun) :
    C2RectangularMomentG11BoundsData F zetaFun :=
  C2RectangularMomentG11BoundsData.ofCriticalZeroCentralTerms
    data.supportConstant
    data.aperture
    data.supportConstant_pos
    data.aperture_nonneg
    data.aperture_lt_pi_div_two
    data.localData
    data.depthCutoff
    data.coreCutoff
    data.tiltDelta
    data.topHeightBound
    data.tiltDelta_mem
    data.sectorial
    data.principalCoeff_eq
    data.remainderCoeff_le

noncomputable def C2RectangularCentralMomentG11BoundsData.toSectorialMomentG11BoundsData
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun) :
    SectorialMomentG11BoundsData F zetaFun :=
  data.toRectangularMomentG11BoundsData.toSectorialMomentG11BoundsData

theorem C2RectangularCentralMomentG11BoundsData.moment_ratio_bound
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.localData ρ hρ).remainderCoeff / (data.localData ρ hρ).principalCoeff ≤
      ((1 : ℝ) / ((data.localData ρ hρ).multiplicity + 1 : ℝ)) *
        sectorialLogConstant data.supportConstant data.aperture *
        Real.log (2 + g11Height ρ) := by
  exact data.toRectangularMomentG11BoundsData.moment_ratio_bound ρ hρ

noncomputable def C2RectangularCentralMomentG11BoundsData.toG11Data
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun) :
    SectorialMomentG11Data F zetaFun :=
  data.toRectangularMomentG11BoundsData.toG11Data

noncomputable def C2RectangularCentralMomentG11BoundsData.toG11Certificate
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun) :
    G11Certificate F zetaFun :=
  data.toRectangularMomentG11BoundsData.toG11Certificate

theorem near_axis_nonzero_from_rectangularCentralMomentG11Bounds
    {F zetaFun : ℂ → ℂ} (data : C2RectangularCentralMomentG11BoundsData F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun data.toG11Certificate.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  near_axis_nonzero_from_G11 data.toG11Certificate hs

noncomputable def C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLog
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      SectorialNormCoherence
        (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
        (c2RectangularCentralContribution ρ)
        aperture)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularCentralMomentG11BoundsData F zetaFun where
  supportConstant := supportConstant
  aperture := aperture
  supportConstant_pos := supportConstant_pos
  aperture_nonneg := aperture_nonneg
  aperture_lt_pi_div_two := aperture_lt_pi_div_two
  localData := localData
  depthCutoff := depthCutoff
  coreCutoff := coreCutoff
  tiltDelta := tiltDelta
  topHeightBound := by
    intro ρ hρ
    exact c2TopHeightBound_of_explicitCutoffLog
      (coreCutoff_pos ρ hρ)
      (explicitTopBound ρ hρ)
  tiltDelta_mem := tiltDelta_mem
  sectorial := sectorial
  principalCoeff_eq := principalCoeff_eq
  remainderCoeff_le := remainderCoeff_le

/--
Concrete H2 for the rectangular central family in phase-cone form.

This is the pointwise cone condition from the notes, specialized to
`c2RectangularCentralContribution ρ`.
-/
def C2RectangularCentralPhaseConeH2
    (zetaFun : ℂ → ℂ)
    (aperture : ℝ)
    (depthCutoff coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (phase : ∀ ρ, IsCriticalZero zetaFun ρ → ℂ) : Prop :=
  ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    SectorialPhaseConeCoherence
      (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
      (c2RectangularCentralContribution ρ)
      aperture
      (phase ρ hρ)

/--
Same constructor as `ofExplicitCutoffLog`, but H2 is supplied in the phase-cone
form.  Lean then derives the norm coherence required by the G11 sectorial route.
-/
noncomputable def C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLogPhaseCone
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (phase : ∀ ρ, IsCriticalZero zetaFun ρ → ℂ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (sectorialCone : C2RectangularCentralPhaseConeH2
      zetaFun aperture depthCutoff coreCutoff phase)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularCentralMomentG11BoundsData F zetaFun :=
  C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLog
    supportConstant aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    localData
    depthCutoff
    coreCutoff
    tiltDelta
    coreCutoff_pos
    explicitTopBound
    tiltDelta_mem
    (by
      intro ρ hρ
      exact sectorialNormCoherence_of_phaseCone (sectorialCone ρ hρ))
    principalCoeff_eq
    remainderCoeff_le

/--
Angle-parameter version of `ofExplicitCutoffLogPhaseCone`.

This is often the most convenient H2 shape: choose a real phase angle `φ(ρ)` and
prove every rotated contribution has real part at least `cos α` times its norm.
-/
noncomputable def C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLogRotatedCone
    {F zetaFun : ℂ → ℂ}
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (phaseAngle : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (rotatedCone : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) a,
      a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
        Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
          (sectorialPhase (phaseAngle ρ hρ) *
            c2RectangularCentralContribution ρ a).re)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).principalCoeff =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      (localData ρ hρ).remainderCoeff ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localData ρ hρ).multiplicity + 1 : ℝ)) :
    C2RectangularCentralMomentG11BoundsData F zetaFun :=
  C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLogPhaseCone
    supportConstant aperture
    supportConstant_pos
    aperture_nonneg
    aperture_lt_pi_div_two
    localData
    depthCutoff
    coreCutoff
    tiltDelta
    (fun ρ hρ => sectorialPhase (phaseAngle ρ hρ))
    coreCutoff_pos
    explicitTopBound
    tiltDelta_mem
    (by
      intro ρ hρ
      exact ⟨sectorialPhase_norm (phaseAngle ρ hρ), rotatedCone ρ hρ⟩)
    principalCoeff_eq
    remainderCoeff_le

/--
Fully specialized rectangular-central H1+H2 package in the most explicit current
analytic form: H1 is stated directly in the cutoffs `Kρ/Mρ`, and H2 is supplied
as a rotated-cone inequality with a real phase angle `φ(ρ)`.
-/
structure C2RectangularCentralRotatedConeMomentG11BoundsData
    (F zetaFun : ℂ → ℂ) where
  supportConstant : ℝ
  aperture : ℝ
  supportConstant_pos : 0 < supportConstant
  aperture_nonneg : 0 ≤ aperture
  aperture_lt_pi_div_two : aperture < Real.pi / 2
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ
  tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  phaseAngle : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ
  explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
      supportConstant * Real.log (2 + g11Height ρ)
  tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ))
  rotatedCone : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) a,
    a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
      Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
        (sectorialPhase (phaseAngle ρ hρ) * c2RectangularCentralContribution ρ a).re
  principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).principalCoeff =
      ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖
  remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff ≤
      ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
          (fun a =>
            (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
              c2RectangularCentralContribution ρ a))‖ /
        ((localData ρ hρ).multiplicity + 1 : ℝ)

noncomputable def C2RectangularCentralRotatedConeMomentG11BoundsData.ofTaylorBoundsFamily
    {F zetaFun : ℂ → ℂ}
    (localTaylor : G11TaylorBoundsFamilyData F zetaFun)
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (phaseAngle : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (rotatedCone : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) a,
      a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
        Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
          (sectorialPhase (phaseAngle ρ hρ) *
            c2RectangularCentralContribution ρ a).re)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      principalTaylorScale ρ (localTaylor.multiplicity ρ hρ) F =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      localTaylor.remainderCoeff ρ hρ ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localTaylor.multiplicity ρ hρ) + 1 : ℝ)) :
    C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun where
  supportConstant := supportConstant
  aperture := aperture
  supportConstant_pos := supportConstant_pos
  aperture_nonneg := aperture_nonneg
  aperture_lt_pi_div_two := aperture_lt_pi_div_two
  localData := localTaylor.toLocalData
  depthCutoff := depthCutoff
  coreCutoff := coreCutoff
  tiltDelta := tiltDelta
  phaseAngle := phaseAngle
  coreCutoff_pos := coreCutoff_pos
  explicitTopBound := explicitTopBound
  tiltDelta_mem := tiltDelta_mem
  rotatedCone := rotatedCone
  principalCoeff_eq := by
    intro ρ hρ
    simpa using principalCoeff_eq ρ hρ
  remainderCoeff_le := by
    intro ρ hρ
    simpa using remainderCoeff_le ρ hρ

noncomputable def C2RectangularCentralRotatedConeMomentG11BoundsData.ofLeibnizTaylorBoundsFamily
    {F zetaFun : ℂ → ℂ}
    (localTaylor : G11LeibnizTaylorBoundsFamilyData F zetaFun)
    (supportConstant aperture : ℝ)
    (supportConstant_pos : 0 < supportConstant)
    (aperture_nonneg : 0 ≤ aperture)
    (aperture_lt_pi_div_two : aperture < Real.pi / 2)
    (depthCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (coreCutoff : ∀ ρ, IsCriticalZero zetaFun ρ → ℕ)
    (tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (phaseAngle : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ)
    (coreCutoff_pos : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), 0 < coreCutoff ρ hρ)
    (explicitTopBound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      ((depthCutoff ρ hρ : ℝ) * Real.log 2 + Real.log (coreCutoff ρ hρ : ℝ)) ≤
        supportConstant * Real.log (2 + g11Height ρ))
    (tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ)))
    (rotatedCone : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) a,
      a ∈ c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ) →
        Real.cos aperture * ‖c2RectangularCentralContribution ρ a‖ ≤
          (sectorialPhase (phaseAngle ρ hρ) *
            c2RectangularCentralContribution ρ a).re)
    (principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      principalTaylorScale ρ (localTaylor.multiplicity ρ hρ) F =
        ‖rectangularCentral ρ (depthCutoff ρ hρ) (coreCutoff ρ hρ)‖)
    (remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
      localTaylor.remainderCoeff ρ hρ ≤
        ‖Finset.sum (c2Rectangle (depthCutoff ρ hρ) (coreCutoff ρ hρ))
            (fun a =>
              (((tiltWeight (tiltDelta ρ hρ) (c2AddressLogHeight a) : ℝ) : ℂ) *
                c2RectangularCentralContribution ρ a))‖ /
          ((localTaylor.multiplicity ρ hρ) + 1 : ℝ)) :
    C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun :=
  C2RectangularCentralRotatedConeMomentG11BoundsData.ofTaylorBoundsFamily
    localTaylor.toTaylorBoundsFamilyData
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

namespace C2RectangularCentralRotatedConeMomentG11BoundsData

noncomputable def toRectangularCentralMomentG11BoundsData
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) :
    C2RectangularCentralMomentG11BoundsData F zetaFun :=
  C2RectangularCentralMomentG11BoundsData.ofExplicitCutoffLogRotatedCone
    data.supportConstant
    data.aperture
    data.supportConstant_pos
    data.aperture_nonneg
    data.aperture_lt_pi_div_two
    data.localData
    data.depthCutoff
    data.coreCutoff
    data.tiltDelta
    data.phaseAngle
    data.coreCutoff_pos
    data.explicitTopBound
    data.tiltDelta_mem
    data.rotatedCone
    data.principalCoeff_eq
    data.remainderCoeff_le

noncomputable def toRectangularMomentG11BoundsData
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) :
    C2RectangularMomentG11BoundsData F zetaFun :=
  data.toRectangularCentralMomentG11BoundsData.toRectangularMomentG11BoundsData

noncomputable def toSectorialMomentG11BoundsData
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) :
    SectorialMomentG11BoundsData F zetaFun :=
  data.toRectangularCentralMomentG11BoundsData.toSectorialMomentG11BoundsData

theorem moment_ratio_bound
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.localData ρ hρ).remainderCoeff / (data.localData ρ hρ).principalCoeff ≤
      ((1 : ℝ) / ((data.localData ρ hρ).multiplicity + 1 : ℝ)) *
        sectorialLogConstant data.supportConstant data.aperture *
        Real.log (2 + g11Height ρ) := by
  exact data.toRectangularCentralMomentG11BoundsData.moment_ratio_bound ρ hρ

noncomputable def toG11Data
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) :
    SectorialMomentG11Data F zetaFun :=
  data.toRectangularCentralMomentG11BoundsData.toG11Data

noncomputable def toG11Certificate
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) :
    G11Certificate F zetaFun :=
  data.toRectangularCentralMomentG11BoundsData.toG11Certificate

theorem near_axis_nonzero_from_rectangularCentralRotatedConeMomentG11Bounds
    {F zetaFun : ℂ → ℂ}
    (data : C2RectangularCentralRotatedConeMomentG11BoundsData F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun data.toG11Certificate.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  near_axis_nonzero_from_G11 data.toG11Certificate hs

end C2RectangularCentralRotatedConeMomentG11BoundsData

end
end C2
