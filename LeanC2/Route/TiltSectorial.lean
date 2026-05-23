import LeanC2.Route.G11Certificate
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace C2

noncomputable section

/-!
Route-level abstraction for the tilt-sectorial H1+H2 path to G11.

This file isolates three reusable pieces from the notes:

* a finite sectorial linear-form estimate, including the phase-cone H2 closure;
* the universal bound `h * exp (-δ h) ≤ e * L` on `[0, L]` when `|δ| ≤ 1 / L`;
* a route data structure whose output is already consumable by
  `G11Certificate.of_logLinearRatioBound`.

The analytic C2 proof of the concrete phase-cone inequality is still an external
input; once supplied, this module turns it into the norm coherence consumed by
the G11 route.
-/

/--
Norm form of sectorial coherence on a finite family.

This is the numeric consequence of the angle hypothesis used in the notes:
if all terms lie in a cone of half-aperture `α`, then the norm of the sum controls
the sum of the norms up to `cos α`.
-/
def SectorialNormCoherence {ι : Type*} (s : Finset ι) (u : ι → ℂ) (α : ℝ) : Prop :=
  Real.cos α * Finset.sum s (fun i => ‖u i‖) ≤ ‖Finset.sum s u‖

/--
Phase-cone form of H2.

After multiplication by a unit complex phase, every contribution has real part at
least `cos α` times its norm.  This is the Lean version of the note-level condition
`|arg(e^{-iφ}uᵢ)| ≤ α`, but stated without choosing an argument function.
-/
def SectorialPhaseConeCoherence {ι : Type*}
    (s : Finset ι) (u : ι → ℂ) (α : ℝ) (phase : ℂ) : Prop :=
  ‖phase‖ = 1 ∧
    ∀ i ∈ s, Real.cos α * ‖u i‖ ≤ (phase * u i).re

/--
H2 closure: the phase-cone formulation implies the norm coherence field consumed
by the G11 sectorial route.
-/
theorem sectorialNormCoherence_of_phaseCone
    {ι : Type*} {s : Finset ι} {u : ι → ℂ} {α : ℝ} {phase : ℂ}
    (hcone : SectorialPhaseConeCoherence s u α phase) :
    SectorialNormCoherence s u α := by
  rcases hcone with ⟨hphase_norm, hcone⟩
  unfold SectorialNormCoherence
  calc
    Real.cos α * Finset.sum s (fun i => ‖u i‖)
        = Finset.sum s (fun i => Real.cos α * ‖u i‖) := by
            rw [Finset.mul_sum]
    _ ≤ Finset.sum s (fun i => (phase * u i).re) := by
        exact Finset.sum_le_sum fun i hi => hcone i hi
    _ = (Finset.sum s (fun i => phase * u i)).re := by
        simp
    _ = (phase * Finset.sum s u).re := by
        rw [Finset.mul_sum]
    _ ≤ ‖phase * Finset.sum s u‖ := Complex.re_le_norm _
    _ = ‖Finset.sum s u‖ := by
        rw [norm_mul, hphase_norm, one_mul]

/-- Unit complex phase attached to a real angle. -/
def sectorialPhase (φ : ℝ) : ℂ :=
  Complex.exp (-(φ : ℂ) * Complex.I)

theorem sectorialPhase_norm (φ : ℝ) :
    ‖sectorialPhase φ‖ = 1 := by
  unfold sectorialPhase
  rw [Complex.norm_exp]
  have hre : (-(φ : ℂ) * Complex.I).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- Angle-parameter version of `sectorialNormCoherence_of_phaseCone`. -/
theorem sectorialNormCoherence_of_rotatedCone
    {ι : Type*} {s : Finset ι} {u : ι → ℂ} {α φ : ℝ}
    (hcone : ∀ i ∈ s, Real.cos α * ‖u i‖ ≤ (sectorialPhase φ * u i).re) :
    SectorialNormCoherence s u α :=
  sectorialNormCoherence_of_phaseCone
    ⟨sectorialPhase_norm φ, hcone⟩

theorem sectorialCos_pos {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2) :
    0 < Real.cos α := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have hlow : -(Real.pi / 2) < α := by linarith
  exact Real.cos_pos_of_mem_Ioo ⟨hlow, hα_lt⟩

theorem sum_norm_le_div_cos_of_sectorialNormCoherence
    {ι : Type*} {s : Finset ι} {u : ι → ℂ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2)
    (hsector : SectorialNormCoherence s u α) :
    Finset.sum s (fun i => ‖u i‖) ≤ ‖Finset.sum s u‖ / Real.cos α := by
  have hcos : 0 < Real.cos α := sectorialCos_pos hα_nonneg hα_lt
  exact (le_div_iff₀ hcos).2 (by simpa [mul_comm] using hsector)

theorem norm_sum_weighted_le_of_sectorialNormCoherence
    {ι : Type*} {s : Finset ι} {u : ι → ℂ} {w : ι → ℂ} {α M : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2)
    (hsector : SectorialNormCoherence s u α)
    (hM : 0 ≤ M)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ M) :
    ‖Finset.sum s (fun i => w i * u i)‖ ≤ (M / Real.cos α) * ‖Finset.sum s u‖ := by
  have hsum_norm :
      Finset.sum s (fun i => ‖u i‖) ≤ ‖Finset.sum s u‖ / Real.cos α :=
    sum_norm_le_div_cos_of_sectorialNormCoherence hα_nonneg hα_lt hsector
  calc
    ‖Finset.sum s (fun i => w i * u i)‖
      ≤ Finset.sum s (fun i => ‖w i * u i‖) := by
          simpa using norm_sum_le s (fun i => w i * u i)
    _ = Finset.sum s (fun i => ‖w i‖ * ‖u i‖) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [norm_mul]
    _ ≤ Finset.sum s (fun i => M * ‖u i‖) := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg _)
    _ = M * Finset.sum s (fun i => ‖u i‖) := by
          rw [Finset.mul_sum]
    _ ≤ M * (‖Finset.sum s u‖ / Real.cos α) := by
          exact mul_le_mul_of_nonneg_left hsum_norm hM
    _ = (M / Real.cos α) * ‖Finset.sum s u‖ := by
          ring

/-- Weight appearing in the tilted moment `h * exp (-δ h)`. -/
def tiltWeight (δ h : ℝ) : ℝ :=
  h * Real.exp (-δ * h)

theorem tiltWeight_nonneg {δ h : ℝ} (hh : 0 ≤ h) :
    0 ≤ tiltWeight δ h := by
  unfold tiltWeight
  positivity

theorem one_div_natSucc_le_one (m : ℕ) :
    (1 : ℝ) / (m + 1 : ℝ) ≤ 1 := by
  have hpos : 0 < (m + 1 : ℝ) := by positivity
  have hm : (1 : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos m
  exact (div_le_iff₀ hpos).2 (by linarith)

theorem g11Log_nonneg (ρ : ℂ) :
    0 ≤ Real.log (2 + g11Height ρ) := by
  apply Real.log_nonneg
  have hheight : 0 ≤ g11Height ρ := abs_nonneg _
  linarith

theorem g11Log_pos (ρ : ℂ) :
    0 < Real.log (2 + g11Height ρ) := by
  apply Real.log_pos
  have hheight : 0 ≤ g11Height ρ := abs_nonneg _
  linarith

theorem tiltWeight_le_exp_mul_support
    {δ h L : ℝ}
    (hL : 0 < L)
    (hδ : |δ| ≤ 1 / L)
    (hh_nonneg : 0 ≤ h)
    (hh_le : h ≤ L) :
    tiltWeight δ h ≤ Real.exp 1 * L := by
  have hscaled : |δ| * h ≤ 1 := by
    have hLinv_nonneg : 0 ≤ 1 / L := by positivity
    calc
      |δ| * h ≤ (1 / L) * h := by
        exact mul_le_mul_of_nonneg_right hδ hh_nonneg
      _ ≤ (1 / L) * L := by
        exact mul_le_mul_of_nonneg_left hh_le hLinv_nonneg
      _ = 1 := by
        field_simp [hL.ne']
  have habs : |δ * h| ≤ 1 := by
    calc
      |δ * h| = |δ| * |h| := by rw [abs_mul]
      _ = |δ| * h := by simp [abs_of_nonneg hh_nonneg]
      _ ≤ 1 := hscaled
  have hexp : Real.exp (-δ * h) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have hneg : -(δ * h) ≤ |δ * h| := neg_le_abs (δ * h)
    linarith
  calc
    tiltWeight δ h = h * Real.exp (-δ * h) := rfl
    _ ≤ h * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left hexp hh_nonneg
    _ ≤ L * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_right hh_le (le_of_lt (Real.exp_pos 1))
    _ = Real.exp 1 * L := by ring

theorem norm_sum_tiltWeight_le_of_sectorialNormCoherence
    {ι : Type*} {s : Finset ι} {u : ι → ℂ} {h : ι → ℝ} {δ L α : ℝ}
    (hL : 0 < L)
    (hδ : |δ| ≤ 1 / L)
    (hheight : ∀ i ∈ s, 0 ≤ h i ∧ h i ≤ L)
    (hα_nonneg : 0 ≤ α)
    (hα_lt : α < Real.pi / 2)
    (hsector : SectorialNormCoherence s u α) :
    ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖ ≤
      (Real.exp 1 * L / Real.cos α) * ‖Finset.sum s u‖ := by
  refine norm_sum_weighted_le_of_sectorialNormCoherence hα_nonneg hα_lt hsector ?_ ?_
  · positivity
  · intro i hi
    rcases hheight i hi with ⟨hi_nonneg, hi_le⟩
    have hbound : tiltWeight δ (h i) ≤ Real.exp 1 * L :=
      tiltWeight_le_exp_mul_support hL hδ hi_nonneg hi_le
    have hnonneg : 0 ≤ tiltWeight δ (h i) := tiltWeight_nonneg hi_nonneg
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, hbound]

/-- The log-linear constant predicted by the tilt-sectorial route. -/
def sectorialLogConstant (K α : ℝ) : ℝ :=
  Real.exp 1 * K / Real.cos α

theorem sectorialLogConstant_pos
    {K α : ℝ} (hK : 0 < K) (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2) :
    0 < sectorialLogConstant K α := by
  unfold sectorialLogConstant
  exact div_pos (mul_pos (Real.exp_pos 1) hK) (sectorialCos_pos hα_nonneg hα_lt)

theorem multiplicityScaled_sectorialLogBound_le
    {m : ℕ} {K α : ℝ} (hK : 0 < K) (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2)
    (ρ : ℂ) :
    ((1 : ℝ) / (m + 1 : ℝ)) *
        sectorialLogConstant K α * Real.log (2 + g11Height ρ) ≤
      sectorialLogConstant K α * Real.log (2 + g11Height ρ) := by
  have hfac : (1 : ℝ) / (m + 1 : ℝ) ≤ 1 := one_div_natSucc_le_one m
  have hnonneg : 0 ≤ sectorialLogConstant K α * Real.log (2 + g11Height ρ) := by
    exact mul_nonneg
      (le_of_lt (sectorialLogConstant_pos hK hα_nonneg hα_lt))
      (g11Log_nonneg ρ)
  nlinarith [hfac, hnonneg]

theorem moment_ratio_bound_of_tiltWeight_family
    {F : ℂ → ℂ} {ρ : ℂ} {ι : Type*} {s : Finset ι}
    {u : ι → ℂ} {h : ι → ℝ} {δ K α : ℝ}
    (localTaylor : G11LocalTaylorData F ρ)
    (hK : 0 < K) (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2)
    (hheight : ∀ i ∈ s, 0 ≤ h i ∧ h i ≤ K * Real.log (2 + g11Height ρ))
    (hδ : |δ| ≤ 1 / (K * Real.log (2 + g11Height ρ)))
    (hsector : SectorialNormCoherence s u α)
    (hprincipal : localTaylor.principalCoeff = ‖Finset.sum s u‖)
    (hremainder :
      localTaylor.remainderCoeff ≤
        ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖ /
          ((localTaylor.multiplicity + 1 : ℝ))) :
    localTaylor.remainderCoeff / localTaylor.principalCoeff ≤
      ((1 : ℝ) / ((localTaylor.multiplicity + 1 : ℝ))) *
        sectorialLogConstant K α * Real.log (2 + g11Height ρ) := by
  have hL : 0 < K * Real.log (2 + g11Height ρ) :=
    mul_pos hK (g11Log_pos ρ)
  have hweighted :
      ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖ ≤
        (Real.exp 1 * (K * Real.log (2 + g11Height ρ)) / Real.cos α) *
          ‖Finset.sum s u‖ :=
    norm_sum_tiltWeight_le_of_sectorialNormCoherence
      hL hδ hheight hα_nonneg hα_lt hsector
  have hweighted' :
      ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖ ≤
        sectorialLogConstant K α * Real.log (2 + g11Height ρ) * localTaylor.principalCoeff := by
    calc
      ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖
        ≤ (Real.exp 1 * (K * Real.log (2 + g11Height ρ)) / Real.cos α) *
            ‖Finset.sum s u‖ := hweighted
      _ = sectorialLogConstant K α * Real.log (2 + g11Height ρ) * ‖Finset.sum s u‖ := by
            unfold sectorialLogConstant
            ring
      _ = sectorialLogConstant K α * Real.log (2 + g11Height ρ) * localTaylor.principalCoeff := by
            rw [← hprincipal]
  have hm : 0 < ((localTaylor.multiplicity + 1 : ℝ)) := by
    positivity
  have hrem_le :
      localTaylor.remainderCoeff ≤
        (((1 : ℝ) / ((localTaylor.multiplicity + 1 : ℝ))) *
          sectorialLogConstant K α * Real.log (2 + g11Height ρ)) * localTaylor.principalCoeff := by
    calc
      localTaylor.remainderCoeff
        ≤ ‖Finset.sum s (fun i => (((tiltWeight δ (h i) : ℝ) : ℂ) * u i))‖ /
            ((localTaylor.multiplicity + 1 : ℝ)) := hremainder
      _ ≤ (sectorialLogConstant K α * Real.log (2 + g11Height ρ) * localTaylor.principalCoeff) /
            ((localTaylor.multiplicity + 1 : ℝ)) := by
            exact div_le_div_of_nonneg_right hweighted' (le_of_lt hm)
      _ = (((1 : ℝ) / ((localTaylor.multiplicity + 1 : ℝ))) *
        sectorialLogConstant K α * Real.log (2 + g11Height ρ)) *
        localTaylor.principalCoeff := by
            ring
  exact (div_le_iff₀ localTaylor.principalCoeff_pos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrem_le

/--
Route data for the H1+H2 tilt-setorial path in the exact note-level form.

The ratio field matches the output of §3.7.4.5 in `fechamento_unificado.md`:
after dividing by `(m + 1)!`, the local ratio carries an explicit prefactor
`1 / (m + 1)` times the sectorial log constant `e K / cos α`.
-/
structure SectorialMomentG11Data (F zetaFun : ℂ → ℂ) where
  supportConstant : ℝ
  aperture : ℝ
  supportConstant_pos : 0 < supportConstant
  aperture_nonneg : 0 ≤ aperture
  aperture_lt_pi_div_two : aperture < Real.pi / 2
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  moment_ratio_bound : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff / (localData ρ hρ).principalCoeff ≤
      ((1 : ℝ) / ((localData ρ hρ).multiplicity + 1 : ℝ)) *
        sectorialLogConstant supportConstant aperture *
        Real.log (2 + g11Height ρ)

/--
Bound-level version of the same H1+H2 route.

This structure records the concrete finite-family ingredients appearing in the
notes: demodulated contributions `uᵢ`, support heights `hᵢ`, an admissible tilt
parameter `δ`, sectorial coherence, and the identifications that connect these
finite sums to the Taylor coefficients entering `G11LocalTaylorData`.
-/
structure SectorialMomentG11BoundsData (F zetaFun : ℂ → ℂ) where
  supportConstant : ℝ
  aperture : ℝ
  supportConstant_pos : 0 < supportConstant
  aperture_nonneg : 0 ≤ aperture
  aperture_lt_pi_div_two : aperture < Real.pi / 2
  localData : ∀ ρ, IsCriticalZero zetaFun ρ → G11LocalTaylorData F ρ
  index : ∀ ρ, IsCriticalZero zetaFun ρ → Type*
  support : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), Finset (index ρ hρ)
  contribution : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), index ρ hρ → ℂ
  height : ∀ ρ (hρ : IsCriticalZero zetaFun ρ), index ρ hρ → ℝ
  tiltDelta : ∀ ρ, IsCriticalZero zetaFun ρ → ℝ
  height_mem_support : ∀ ρ (hρ : IsCriticalZero zetaFun ρ) (i : index ρ hρ),
    i ∈ support ρ hρ →
      0 ≤ height ρ hρ i ∧
        height ρ hρ i ≤ supportConstant * Real.log (2 + g11Height ρ)
  tiltDelta_mem : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    |tiltDelta ρ hρ| ≤ 1 / (supportConstant * Real.log (2 + g11Height ρ))
  sectorial : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    SectorialNormCoherence (support ρ hρ) (contribution ρ hρ) aperture
  principalCoeff_eq : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).principalCoeff = ‖Finset.sum (support ρ hρ) (contribution ρ hρ)‖
  remainderCoeff_le : ∀ ρ (hρ : IsCriticalZero zetaFun ρ),
    (localData ρ hρ).remainderCoeff ≤
      ‖Finset.sum (support ρ hρ)
          (fun i =>
            (((tiltWeight (tiltDelta ρ hρ) (height ρ hρ i) : ℝ) : ℂ) *
              contribution ρ hρ i))‖ /
        ((localData ρ hρ).multiplicity + 1 : ℝ)

theorem SectorialMomentG11BoundsData.moment_ratio_bound
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11BoundsData F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.localData ρ hρ).remainderCoeff / (data.localData ρ hρ).principalCoeff ≤
      ((1 : ℝ) / ((data.localData ρ hρ).multiplicity + 1 : ℝ)) *
        sectorialLogConstant data.supportConstant data.aperture *
        Real.log (2 + g11Height ρ) := by
  simpa using moment_ratio_bound_of_tiltWeight_family
    (localTaylor := data.localData ρ hρ)
    (ρ := ρ)
    (s := data.support ρ hρ)
    (u := data.contribution ρ hρ)
    (h := data.height ρ hρ)
    (δ := data.tiltDelta ρ hρ)
    (K := data.supportConstant)
    (α := data.aperture)
    data.supportConstant_pos
    data.aperture_nonneg
    data.aperture_lt_pi_div_two
    (data.height_mem_support ρ hρ)
    (data.tiltDelta_mem ρ hρ)
    (data.sectorial ρ hρ)
    (data.principalCoeff_eq ρ hρ)
    (data.remainderCoeff_le ρ hρ)

noncomputable def SectorialMomentG11BoundsData.toG11Data
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11BoundsData F zetaFun) :
    SectorialMomentG11Data F zetaFun where
  supportConstant := data.supportConstant
  aperture := data.aperture
  supportConstant_pos := data.supportConstant_pos
  aperture_nonneg := data.aperture_nonneg
  aperture_lt_pi_div_two := data.aperture_lt_pi_div_two
  localData := data.localData
  moment_ratio_bound := data.moment_ratio_bound

theorem SectorialMomentG11Data.logLinearRatioBound
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11Data F zetaFun)
    (ρ : ℂ) (hρ : IsCriticalZero zetaFun ρ) :
    (data.localData ρ hρ).remainderCoeff / (data.localData ρ hρ).principalCoeff ≤
      sectorialLogConstant data.supportConstant data.aperture *
        Real.log (2 + g11Height ρ) := by
  exact le_trans (data.moment_ratio_bound ρ hρ)
    (multiplicityScaled_sectorialLogBound_le
      data.supportConstant_pos data.aperture_nonneg data.aperture_lt_pi_div_two ρ)

noncomputable def SectorialMomentG11Data.toG11Certificate
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11Data F zetaFun) :
    G11Certificate F zetaFun :=
  G11Certificate.of_logLinearRatioBound
    (sectorialLogConstant data.supportConstant data.aperture)
    (sectorialLogConstant_pos
      data.supportConstant_pos data.aperture_nonneg data.aperture_lt_pi_div_two)
    data.localData
    data.logLinearRatioBound

theorem near_axis_nonzero_from_sectorialMomentG11
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11Data F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun data.toG11Certificate.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  near_axis_nonzero_from_G11 data.toG11Certificate hs

noncomputable def SectorialMomentG11BoundsData.toG11Certificate
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11BoundsData F zetaFun) :
    G11Certificate F zetaFun :=
  data.toG11Data.toG11Certificate

theorem near_axis_nonzero_from_sectorialMomentG11Bounds
    {F zetaFun : ℂ → ℂ} (data : SectorialMomentG11BoundsData F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun data.toG11Certificate.toNearAxisCertificate.radius) :
    F s ≠ 0 :=
  near_axis_nonzero_from_G11 data.toG11Certificate hs

end
end C2
