import LeanC2.Foundations.Basic

set_option linter.style.whitespace false

namespace C2

/-- A point lies on the critical line when its real part is `1/2`. -/
def onCriticalLine (s : ℂ) : Prop :=
  s.re = (1 : ℝ) / 2

/-- Critical-line zeros of an analytic target, typically `riemannZeta`. -/
def IsCriticalZero (f : ℂ → ℂ) (rho : ℂ) : Prop :=
  f rho = 0 ∧ onCriticalLine rho

lemma IsCriticalZero.re_eq_half {f : ℂ → ℂ} {rho : ℂ} (h : IsCriticalZero f rho) :
    rho.re = (1 : ℝ) / 2 :=
  h.2

/-- Horizontal window at fixed height around a critical-line center `rho`. -/
def transversalWindow (rho : ℂ) (radius : ℝ) : Set ℂ :=
  {s : ℂ | s.im = rho.im ∧ 0 < |s.re - rho.re| ∧ |s.re - rho.re| < radius}

/-- Global near-axis region induced by a radius assignment around critical zeros. -/
def nearAxisRegion (zetaFun : ℂ → ℂ) (radius : ℂ → ℝ) : Set ℂ :=
  {s : ℂ | ∃ rho : ℂ, IsCriticalZero zetaFun rho ∧ s ∈ transversalWindow rho (radius rho)}

/--
Abstract near-axis certificate. Later theorems from transversality, Taylor, and G11
should instantiate this structure.
-/
structure NearAxisCertificate (F zetaFun : ℂ → ℂ) where
  radius : ℂ → ℝ
  radius_pos : ∀ rho, IsCriticalZero zetaFun rho -> 0 < radius rho
  radius_le_half : ∀ rho, IsCriticalZero zetaFun rho -> radius rho ≤ (1 : ℝ) / 2
  nonvanishing : ∀ {rho s},
    IsCriticalZero zetaFun rho ->
    s ∈ transversalWindow rho (radius rho) ->
    F s ≠ 0

theorem NearAxisCertificate.offCriticalStrip_of_mem_transversalWindow
    {F zetaFun : ℂ → ℂ} (cert : NearAxisCertificate F zetaFun) {rho s : ℂ}
    (hrho : IsCriticalZero zetaFun rho)
    (hs : s ∈ transversalWindow rho (cert.radius rho)) :
    offCriticalStrip s := by
  rcases hs with ⟨_sameHeight, hdist_pos, hdist_lt⟩
  have hline : rho.re = (1 : ℝ) / 2 := hrho.re_eq_half
  have hltHalf : |s.re - (1 : ℝ) / 2| < (1 : ℝ) / 2 := by
    have hradius : cert.radius rho ≤ (1 : ℝ) / 2 := cert.radius_le_half rho hrho
    have : |s.re - rho.re| < (1 : ℝ) / 2 := lt_of_lt_of_le hdist_lt hradius
    simpa [hline] using this
  have habs := abs_lt.mp hltHalf
  have hne : s.re ≠ (1 : ℝ) / 2 := by
    intro hsEq
    have : |s.re - rho.re| = 0 := by simp [hsEq, hline]
    linarith
  refine ⟨?_, ?_, hne⟩
  · linarith
  · linarith

theorem NearAxisCertificate.nonvanishing_of_mem
    {F zetaFun : ℂ → ℂ} (cert : NearAxisCertificate F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun cert.radius) :
    F s ≠ 0 := by
  rcases hs with ⟨rho, hrho, hsWindow⟩
  exact cert.nonvanishing hrho hsWindow

theorem NearAxisCertificate.offCriticalStrip_of_mem
    {F zetaFun : ℂ → ℂ} (cert : NearAxisCertificate F zetaFun) {s : ℂ}
    (hs : s ∈ nearAxisRegion zetaFun cert.radius) :
    offCriticalStrip s := by
  rcases hs with ⟨rho, hrho, hsWindow⟩
  exact cert.offCriticalStrip_of_mem_transversalWindow hrho hsWindow

end C2