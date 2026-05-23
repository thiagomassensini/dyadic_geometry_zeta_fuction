import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import LeanC2.Analytic.GenuineLateralInfinite
import LeanC2.Identity.C0Bridge
import LeanC2.Roadmap

namespace C2

/-!
Continuation interface for the complete infinite genuine operator.

The file does not assert analytic continuation as an axiom.  It packages the future
continuation argument as explicit data: if an identity is known on `Re(s) > 1`,
the data transports it to the open right half-plane.
-/

/-- The absolute-convergence half-plane used by the Dirichlet-series proof. -/
def oneLtHalfPlane : Set ℂ :=
  {s | 1 < s.re}

/-- The open right half-plane used by the roadmap transfer interface. -/
def openRightHalfPlane : Set ℂ :=
  {s | 0 < s.re}

/-- The open right half-plane with the distinguished point `s = 1` removed. -/
def puncturedOpenRightHalfPlane : Set ℂ :=
  {s | 0 < s.re ∧ s ≠ 1}

/-- The continued odd channel `(1 - 2^{-s}) ζ(s)` on the punctured right half-plane. -/
noncomputable def continuedOddDirichletChannel (s : ℂ) : ℂ :=
  (1 - complexDirichletCoeff s 2) * riemannZeta s

/-- The corresponding continued central C2 expression obtained from the odd channel bridge. -/
noncomputable def continuedCentralOddChannel (s : ℂ) : ℂ :=
  centralFromOddChannel continuedOddDirichletChannel s

theorem puncturedOpenRightHalfPlane_isOpen : IsOpen puncturedOpenRightHalfPlane := by
  simpa [puncturedOpenRightHalfPlane] using
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).inter isOpen_compl_singleton

theorem complexDirichletCoeff_analyticOnNhd (n : ℕ) (domain : Set ℂ) :
    AnalyticOnNhd ℂ (fun s => complexDirichletCoeff s n) domain := by
  simpa [complexDirichletCoeff] using
    (((analyticOnNhd_id.mul analyticOnNhd_const).neg).cexp :
      AnalyticOnNhd ℂ
        (fun s : ℂ => Complex.exp (-(s * ((Real.log (n : ℝ) : ℂ)))))
        domain)

theorem riemannZeta_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ riemannZeta puncturedOpenRightHalfPlane := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) puncturedOpenRightHalfPlane_isOpen
  exact (differentiableAt_riemannZeta hs.2).differentiableWithinAt

theorem q_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ q puncturedOpenRightHalfPlane := by
  have hvertical : AnalyticOnNhd ℂ verticalRatio puncturedOpenRightHalfPlane := by
    refine
      ((complexDirichletCoeff_analyticOnNhd 2 puncturedOpenRightHalfPlane).const_smul
        (c := (1 / 2 : ℂ))).congr puncturedOpenRightHalfPlane_isOpen ?_
    intro s _hs
    simp [verticalRatio_eq]
  simpa [q] using hvertical

theorem verticalDepthTailFromTwo_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ verticalDepthTailFromTwo puncturedOpenRightHalfPlane := by
  have hq : AnalyticOnNhd ℂ q puncturedOpenRightHalfPlane :=
    q_analyticOnNhd_punctured
  have hden : AnalyticOnNhd ℂ (fun s => 1 - q s) puncturedOpenRightHalfPlane :=
    analyticOnNhd_const.sub hq
  have hinv : AnalyticOnNhd ℂ (fun s => (1 - q s)⁻¹) puncturedOpenRightHalfPlane :=
    hden.inv (fun s hs => verticalResolvent_den_ne_zero_of_re_pos s hs.1)
  have hexpr : AnalyticOnNhd ℂ (fun s => q s ^ 2 * (1 - q s)⁻¹) puncturedOpenRightHalfPlane :=
    (hq.pow 2).mul hinv
  refine hexpr.congr puncturedOpenRightHalfPlane_isOpen ?_
  intro s hs
  symm
  simpa [q, verticalResolvent, one_div] using verticalDepthTailFromTwo_eq s hs.1

theorem continuedOddDirichletChannel_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ continuedOddDirichletChannel puncturedOpenRightHalfPlane := by
  unfold continuedOddDirichletChannel
  exact
    ((analyticOnNhd_const.sub
      (complexDirichletCoeff_analyticOnNhd 2 puncturedOpenRightHalfPlane)).mul
      riemannZeta_analyticOnNhd_punctured)

theorem continuedCentralOddChannel_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ continuedCentralOddChannel puncturedOpenRightHalfPlane := by
  unfold continuedCentralOddChannel centralFromOddChannel
  exact
    (analyticOnNhd_const.mul verticalDepthTailFromTwo_analyticOnNhd_punctured).mul
      continuedOddDirichletChannel_analyticOnNhd_punctured

theorem c0_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ c0 puncturedOpenRightHalfPlane := by
  have hfactor : AnalyticOnNhd ℂ c0FromVerticalFactor puncturedOpenRightHalfPlane := by
    unfold c0FromVerticalFactor
    exact
      (analyticOnNhd_const.mul verticalDepthTailFromTwo_analyticOnNhd_punctured).mul
        (analyticOnNhd_const.sub
          (complexDirichletCoeff_analyticOnNhd 2 puncturedOpenRightHalfPlane))
  refine hfactor.congr puncturedOpenRightHalfPlane_isOpen ?_
  intro s hs
  symm
  exact c0_eq_c0FromVerticalFactor_of_re_pos s hs.1

theorem continuedOddDirichletChannel_eq_oddDirichletChannel_on_oneLtHalfPlane :
    ∀ s : ℂ, s ∈ oneLtHalfPlane → continuedOddDirichletChannel s = oddDirichletChannel s := by
  intro s hs
  simpa [continuedOddDirichletChannel] using
    (oddDirichletChannel_eulerRelation_of_one_lt_re s hs).symm

theorem continuedCentralOddChannel_eq_genuineCentralDoubleSeries_on_oneLtHalfPlane :
    ∀ s : ℂ, s ∈ oneLtHalfPlane → continuedCentralOddChannel s = genuineCentralDoubleSeries s := by
  intro s hs
  rw [genuineCentralDoubleSeries_eq_centralFromOddChannel s hs]
  unfold continuedCentralOddChannel continuedOddDirichletChannel centralFromOddChannel
  simpa using
    congrArg (fun z => (2 : ℂ) * verticalDepthTailFromTwo s * z)
      ((oddDirichletChannel_eulerRelation_of_one_lt_re s hs).symm)

theorem genuineFInfinite_eq_continuedCentralOddChannel_on_oneLtHalfPlane :
    ∀ s : ℂ, s ∈ oneLtHalfPlane → genuineFInfinite s = continuedCentralOddChannel s := by
  intro s hs
  calc
    genuineFInfinite s = genuineCentralDoubleSeries s :=
      genuineFInfinite_eq_central_of_one_lt_re s hs
    _ = continuedCentralOddChannel s := by
      symm
      exact continuedCentralOddChannel_eq_genuineCentralDoubleSeries_on_oneLtHalfPlane s hs

theorem continuedCentralOddChannel_fundamentalIdentity :
    FundamentalIdentityOnRightHalfPlane continuedCentralOddChannel riemannZeta := by
  exact centralFromOddChannel_riemannZeta_identity (fun s hs => by
    simp [continuedOddDirichletChannel])

theorem puncturedOpenRightHalfPlane_isPreconnected :
    IsPreconnected puncturedOpenRightHalfPlane := by
  letI : ContinuousSMul ℝ ℂ := ⟨by
    simpa [Algebra.smul_def] using
      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  let D : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  let A : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}
  let B : Set ℂ := {s | 0 < s.re ∧ s.im < 0}
  let C : Set ℂ := {s | 1 < s.re}
  have hD : IsPreconnected D := by
    change IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
    exact ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hA : IsPreconnected A := by
    change IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im})
    exact ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected B := by
    change IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0})
    exact ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected C := by
    change IsPreconnected ({s : ℂ | 1 < s.re})
    exact (convex_halfSpace_re_gt 1).isPreconnected
  have hDA : (D ∩ A).Nonempty := by
    refine ⟨((1 : ℂ) / 2) + Complex.I, ?_⟩
    norm_num [D, A]
  have hDAB : ((D ∪ A) ∩ B).Nonempty := by
    refine ⟨((1 : ℂ) / 2) - Complex.I, ?_⟩
    norm_num [D, A, B]
  have hDABC : (((D ∪ A) ∪ B) ∩ C).Nonempty := by
    refine ⟨(2 : ℂ) + Complex.I, ?_⟩
    norm_num [D, A, B, C]
  have hDA_pre : IsPreconnected (D ∪ A) :=
    hD.union' hDA hA
  have hDAB_pre : IsPreconnected ((D ∪ A) ∪ B) :=
    hDA_pre.union' hDAB hB
  have hUnion : IsPreconnected (((D ∪ A) ∪ B) ∪ C) :=
    hDAB_pre.union' hDABC hC
  have hEq : puncturedOpenRightHalfPlane = (((D ∪ A) ∪ B) ∪ C) := by
    ext s
    constructor
    · intro hs
      rcases hs with ⟨hsre, hsne⟩
      rcases lt_trichotomy s.re 1 with hlt | heq | hgt
      · have hsD : s ∈ D := ⟨hsre, hlt⟩
        exact Or.inl (Or.inl (Or.inl hsD))
      · rcases lt_trichotomy s.im 0 with himneg | himzero | himpos
        · have hsB : s ∈ B := ⟨by simp [heq], himneg⟩
          exact Or.inl (Or.inr hsB)
        · exfalso
          apply hsne
          apply Complex.ext <;> simp [heq, himzero]
        · have hsA : s ∈ A := ⟨by simp [heq], himpos⟩
          exact Or.inl (Or.inl (Or.inr hsA))
      · have hsC : s ∈ C := hgt
        exact Or.inr hsC
    · intro hs
      simp only [D, A, B, C] at hs
      rcases hs with hs | hsC
      · rcases hs with hs | hsB
        · rcases hs with hsD | hsA
          · rcases hsD with ⟨hsre, hslt⟩
            refine ⟨hsre, ?_⟩
            intro h
            simp [h] at hslt
          · rcases hsA with ⟨hsre, hsim⟩
            refine ⟨hsre, ?_⟩
            intro h
            simp [h] at hsim
        · rcases hsB with ⟨hsre, hsim⟩
          refine ⟨hsre, ?_⟩
          intro h
          simp [h] at hsim
      · refine ⟨lt_trans zero_lt_one hsC, ?_⟩
        intro h
        simp [h] at hsC
  rw [hEq]
  exact hUnion

/-- Identity `F = c0 * zetaFun` restricted to a domain. -/
def C2IdentityOn (domain : Set ℂ) (F zetaFun : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, s ∈ domain → F s = c0 s * zetaFun s

theorem C2IdentityOn.to_rightHalfPlane
    {F zetaFun : ℂ → ℂ}
    (h : C2IdentityOn openRightHalfPlane F zetaFun) :
    FundamentalIdentityOnRightHalfPlane F zetaFun := by
  intro s hs
  exact h s hs

theorem C2IdentityOn.of_fundamentalRightHalfPlane
    {F zetaFun : ℂ → ℂ}
    (h : FundamentalIdentityOnRightHalfPlane F zetaFun) :
    C2IdentityOn openRightHalfPlane F zetaFun := by
  intro s hs
  exact h s hs

/--
Continuation bridge from the absolutely convergent half-plane to the open right
half-plane.
-/
structure ContinuationFromOneLtData (F zetaFun : ℂ → ℂ) where
  continue_identity :
    C2IdentityOn oneLtHalfPlane F zetaFun →
      C2IdentityOn openRightHalfPlane F zetaFun

/--
Continuation interface for equality between two numerators from `Re(s) > 1` to
the open right half-plane.
-/
structure ComparisonFromOneLtData (F G : ℂ → ℂ) where
  continue_equality :
    (∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) →
      ∀ s : ℂ, s ∈ openRightHalfPlane → F s = G s

/--
Comparison interface split across the punctured right half-plane and the special
value at `s = 1`.
-/
structure ComparisonFromOneLtAtOneData (F G : ℂ → ℂ) where
  continue_equality_punctured :
    (∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) →
      ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane → F s = G s
  eq_at_one : F 1 = G 1

/--
Comparison interface from `Re(s) > 1` to the punctured open right half-plane.
This is the natural interface when the point `s = 1` should be kept separate.
-/
structure ComparisonFromOneLtPuncturedData (F G : ℂ → ℂ) where
  continue_equality_punctured :
    (∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) →
      ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane → F s = G s

noncomputable def ComparisonFromOneLtAtOneData.toComparisonFromOneLtData
    {F G : ℂ → ℂ}
    (data : ComparisonFromOneLtAtOneData F G) :
    ComparisonFromOneLtData F G where
  continue_equality := by
    intro hOneLt s hs
    by_cases h1 : s = 1
    · simpa [h1] using data.eq_at_one
    · exact data.continue_equality_punctured hOneLt s ⟨hs, h1⟩

def ComparisonFromOneLtAtOneData.of_analyticOnNhd_punctured
    {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F puncturedOpenRightHalfPlane)
    (hG : AnalyticOnNhd ℂ G puncturedOpenRightHalfPlane)
    (hEqOne : F 1 = G 1) :
    ComparisonFromOneLtAtOneData F G where
  continue_equality_punctured := by
    intro hOneLt s hs
    have hTwo_mem : (2 : ℂ) ∈ puncturedOpenRightHalfPlane := by
      simp [puncturedOpenRightHalfPlane]
    have hOneLt_nhds : oneLtHalfPlane ∈ nhds (2 : ℂ) := by
      simpa [oneLtHalfPlane] using
        (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
          (by norm_num : 1 < ((2 : ℂ).re))
    have hFG : F =ᶠ[nhds (2 : ℂ)] G :=
      Filter.eventually_of_mem hOneLt_nhds (fun t ht => hOneLt t ht)
    have hEq : Set.EqOn F G puncturedOpenRightHalfPlane :=
      hF.eqOn_of_preconnected_of_eventuallyEq hG
        puncturedOpenRightHalfPlane_isPreconnected hTwo_mem hFG
    exact hEq hs
  eq_at_one := hEqOne

def ComparisonFromOneLtPuncturedData.of_analyticOnNhd_punctured
    {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F puncturedOpenRightHalfPlane)
    (hG : AnalyticOnNhd ℂ G puncturedOpenRightHalfPlane) :
    ComparisonFromOneLtPuncturedData F G where
  continue_equality_punctured := by
    intro hOneLt s hs
    have hTwo_mem : (2 : ℂ) ∈ puncturedOpenRightHalfPlane := by
      simp [puncturedOpenRightHalfPlane]
    have hOneLt_nhds : oneLtHalfPlane ∈ nhds (2 : ℂ) := by
      simpa [oneLtHalfPlane] using
        (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
          (by norm_num : 1 < ((2 : ℂ).re))
    have hFG : F =ᶠ[nhds (2 : ℂ)] G :=
      Filter.eventually_of_mem hOneLt_nhds (fun t ht => hOneLt t ht)
    have hEq : Set.EqOn F G puncturedOpenRightHalfPlane :=
      hF.eqOn_of_preconnected_of_eventuallyEq hG
        puncturedOpenRightHalfPlane_isPreconnected hTwo_mem hFG
    exact hEq hs

def ComparisonFromOneLtPuncturedData.of_eqOnPuncturedOpenRightHalfPlane
    {F G : ℂ → ℂ}
    (hEq : Set.EqOn F G puncturedOpenRightHalfPlane) :
    ComparisonFromOneLtPuncturedData F G where
  continue_equality_punctured := by
    intro _hOneLt s hs
    exact hEq hs

theorem ComparisonFromOneLtPuncturedData.eqOnPuncturedOpenRightHalfPlane
    {F G : ℂ → ℂ}
    (data : ComparisonFromOneLtPuncturedData F G)
    (hEq : ∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) :
    ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane → F s = G s :=
  data.continue_equality_punctured hEq

theorem ComparisonFromOneLtData.eqOnOpenRightHalfPlane
    {F G : ℂ → ℂ}
    (data : ComparisonFromOneLtData F G)
    (hEq : ∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) :
    ∀ s : ℂ, s ∈ openRightHalfPlane → F s = G s :=
  data.continue_equality hEq

theorem ComparisonFromOneLtPuncturedData.transferOffCriticalIdentity
    {F G zetaFun : ℂ → ℂ}
    (comparison : ComparisonFromOneLtPuncturedData F G)
    (hG : FundamentalIdentityOnRightHalfPlane G zetaFun)
    (hEq : ∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) :
    FundamentalIdentityOnOffCriticalStrip F zetaFun := by
  intro s hs
  have hsPunct : s ∈ puncturedOpenRightHalfPlane := by
    refine ⟨hs.1, ?_⟩
    intro h1
    have hre : s.re = 1 := by simp [h1]
    linarith [hs.2.1, hre]
  calc
    F s = G s := comparison.continue_equality_punctured hEq s hsPunct
    _ = c0 s * zetaFun s := hG s hs.1

noncomputable def ContinuationFromOneLtData.of_eqOnOpenRightHalfPlane
    {F G zetaFun : ℂ → ℂ}
    (data : ContinuationFromOneLtData G zetaFun)
    (hEq : ∀ s : ℂ, s ∈ openRightHalfPlane → F s = G s) :
    ContinuationFromOneLtData F zetaFun where
  continue_identity := by
    intro hOneLt
    have hOneLtG : C2IdentityOn oneLtHalfPlane G zetaFun := by
      intro s hs
      calc
        G s = F s := by
          symm
          exact hEq s (by
            simpa [oneLtHalfPlane, openRightHalfPlane] using
              (lt_trans zero_lt_one hs))
        _ = c0 s * zetaFun s := hOneLt s hs
    intro s hs
    calc
      F s = G s := hEq s hs
      _ = c0 s * zetaFun s := data.continue_identity hOneLtG s hs

noncomputable def ComparisonFromOneLtData.transferContinuation
    {F G zetaFun : ℂ → ℂ}
    (comparison : ComparisonFromOneLtData F G)
    (data : ContinuationFromOneLtData G zetaFun)
    (hEq : ∀ s : ℂ, s ∈ oneLtHalfPlane → F s = G s) :
    ContinuationFromOneLtData F zetaFun :=
  ContinuationFromOneLtData.of_eqOnOpenRightHalfPlane data
    (comparison.eqOnOpenRightHalfPlane hEq)

theorem ContinuationFromOneLtData.to_fundamentalRightHalfPlane
    {F zetaFun : ℂ → ℂ}
    (data : ContinuationFromOneLtData F zetaFun)
    (hOneLt : C2IdentityOn oneLtHalfPlane F zetaFun) :
    FundamentalIdentityOnRightHalfPlane F zetaFun :=
  (data.continue_identity hOneLt).to_rightHalfPlane

theorem FundamentalIdentityOnRightHalfPlane.analyticOnNhd_punctured
    {F zetaFun : ℂ → ℂ}
    (hId : FundamentalIdentityOnRightHalfPlane F zetaFun)
    (hc0 : AnalyticOnNhd ℂ c0 puncturedOpenRightHalfPlane)
    (hzeta : AnalyticOnNhd ℂ zetaFun puncturedOpenRightHalfPlane) :
    AnalyticOnNhd ℂ F puncturedOpenRightHalfPlane := by
  have hprod : AnalyticOnNhd ℂ (fun s => c0 s * zetaFun s)
      puncturedOpenRightHalfPlane :=
    hc0.mul hzeta
  refine hprod.congr puncturedOpenRightHalfPlane_isOpen ?_
  intro s hs
  exact (hId s hs.1).symm

noncomputable def ContinuationFromOneLtData.toGenuineRouteData
    {F : GenuineNumerator}
    (data : ContinuationFromOneLtData F riemannZeta)
    (hOneLt : C2IdentityOn oneLtHalfPlane F riemannZeta)
    (hNonvanishing : offCriticalStripNonvanishing F) :
    GenuineRouteData where
  F := F
  identity := data.to_fundamentalRightHalfPlane hOneLt
  genuine_nonvanishing := hNonvanishing

theorem mathlibRiemannHypothesis_of_continuationFromOneLt
    {F : GenuineNumerator}
    (data : ContinuationFromOneLtData F riemannZeta)
    (hOneLt : C2IdentityOn oneLtHalfPlane F riemannZeta)
    (hNonvanishing : offCriticalStripNonvanishing F) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteData hOneLt hNonvanishing)

noncomputable def ContinuationFromOneLtData.toGenuineRouteDataOfCover
    {F : GenuineNumerator}
    (data : ContinuationFromOneLtData F riemannZeta)
    (hOneLt : C2IdentityOn oneLtHalfPlane F riemannZeta)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = F) :
    GenuineRouteData where
  F := F
  identity := data.to_fundamentalRightHalfPlane hOneLt
  genuine_nonvanishing := by
    simpa [hCoverF] using offCriticalStripNonvanishing_of_coverData cover

theorem mathlibRiemannHypothesis_of_continuationFromOneLt_cover
    {F : GenuineNumerator}
    (data : ContinuationFromOneLtData F riemannZeta)
    (hOneLt : C2IdentityOn oneLtHalfPlane F riemannZeta)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = F) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteDataOfCover hOneLt cover hCoverF)

theorem genuineFInfinite_identity_on_oneLtHalfPlane :
    C2IdentityOn oneLtHalfPlane genuineFInfinite riemannZeta := by
  intro s hs
  exact genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re s hs

/-- Continuation data specialized to the complete infinite genuine operator. -/
abbrev GenuineFInfiniteContinuationData :=
  ContinuationFromOneLtData genuineFInfinite riemannZeta

theorem GenuineFInfiniteContinuationData.fundamentalIdentity
    (data : GenuineFInfiniteContinuationData) :
    FundamentalIdentityOnRightHalfPlane genuineFInfinite riemannZeta :=
  data.to_fundamentalRightHalfPlane genuineFInfinite_identity_on_oneLtHalfPlane

theorem GenuineFInfiniteContinuationData.analyticOnNhd_punctured
    (data : GenuineFInfiniteContinuationData) :
    AnalyticOnNhd ℂ genuineFInfinite puncturedOpenRightHalfPlane :=
  data.fundamentalIdentity.analyticOnNhd_punctured
    c0_analyticOnNhd_punctured
    riemannZeta_analyticOnNhd_punctured

theorem GenuineFInfiniteContinuationData.eq_continuedCentralOddChannel_on_punctured
    (data : GenuineFInfiniteContinuationData) :
    ∀ s : ℂ, s ∈ puncturedOpenRightHalfPlane →
      genuineFInfinite s = continuedCentralOddChannel s :=
  ComparisonFromOneLtPuncturedData.eqOnPuncturedOpenRightHalfPlane
    (ComparisonFromOneLtPuncturedData.of_analyticOnNhd_punctured
      data.analyticOnNhd_punctured
      continuedCentralOddChannel_analyticOnNhd_punctured)
    genuineFInfinite_eq_continuedCentralOddChannel_on_oneLtHalfPlane

/--
Roadmap spelling: after supplying continuation data, the genuine identity holds on
the open right half-plane.
-/
theorem F_eq_c0_mul_zeta_sigma_gt_zero
    (data : GenuineFInfiniteContinuationData) (s : ℂ) (hs : 0 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s :=
  data.fundamentalIdentity s hs

/-- Roadmap spelling for the continued `Re(s) > 0` C2 identity. -/
theorem C2_identity_sigma_gt_zero
    (data : GenuineFInfiniteContinuationData) (s : ℂ) (hs : 0 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s :=
  F_eq_c0_mul_zeta_sigma_gt_zero data s hs

noncomputable def GenuineFInfiniteContinuationData.toGenuineRouteData
    (data : GenuineFInfiniteContinuationData)
    (hNonvanishing : offCriticalStripNonvanishing genuineFInfinite) :
    GenuineRouteData where
  F := genuineFInfinite
  identity := data.fundamentalIdentity
  genuine_nonvanishing := hNonvanishing

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation
    (data : GenuineFInfiniteContinuationData)
    (hNonvanishing : offCriticalStripNonvanishing genuineFInfinite) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteData hNonvanishing)

noncomputable def GenuineFInfiniteContinuationData.toGenuineRouteDataOfCover
    (data : GenuineFInfiniteContinuationData)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = genuineFInfinite) :
    GenuineRouteData where
  F := genuineFInfinite
  identity := data.fundamentalIdentity
  genuine_nonvanishing := by
    simpa [hCoverF] using offCriticalStripNonvanishing_of_coverData cover

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_cover
    (data : GenuineFInfiniteContinuationData)
    (cover : OffCriticalCoverData)
    (hCoverF : cover.F = genuineFInfinite) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineRouteData
    (data.toGenuineRouteDataOfCover cover hCoverF)

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_nearBulkEdge
    (data : GenuineFInfiniteContinuationData)
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkRouteData)
    (edge : EdgeRouteData)
    (hNearF : near.F = genuineFInfinite)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_cover data
    (OffCriticalCoverData.ofNearBulkEdge near bulk edge hBulkF hEdgeF hcover)
    hNearF

theorem mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_nearBulkBoundsEdge
    (data : GenuineFInfiniteContinuationData)
    (near : NearAxisRouteData)
    (bulk : RegionalVerticalBulkBoundsData)
    (edge : EdgeRouteData)
    (hNearF : near.F = genuineFInfinite)
    (hBulkF : bulk.F = near.F)
    (hEdgeF : edge.F = near.F)
    (hcover : ∀ s : Complex, offCriticalStrip s →
      s ∈ nearAxisRegion riemannZeta near.near_axis.radius ∨
        s ∈ bulk.bulkRegion ∨ s ∈ edge.edgeRegion) :
    RiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_genuineFInfiniteContinuation_cover data
    (OffCriticalCoverData.ofNearBulkBoundsEdge near bulk edge hBulkF hEdgeF hcover)
    hNearF

end C2
