import LeanC2.Analytic.GenuineInfinite

namespace C2

/-!
Named infinite lateral genuine operators.

`GenuineInfinite.lean` contains the analytic estimates and cancellation proof.
This file exposes the roadmap-facing operators `D`, `B`, and `F = D - B`
as a small interface.
-/

/-- Infinite direct/lateral genuine operator. -/
noncomputable abbrev genuineDInfinite (s : ℂ) : ℂ :=
  directLateralInfinite s

/-- Infinite bracket genuine operator. -/
noncomputable abbrev genuineBInfinite (s : ℂ) : ℂ :=
  bracketLateralInfinite s

/-- Complete infinite genuine numerator `F = D - B`. -/
noncomputable def genuineFInfinite (s : ℂ) : ℂ :=
  genuineDInfinite s - genuineBInfinite s

theorem summable_genuineDInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ => genuineDirectAddressTerm s p :=
  summable_genuineDirectAddressTerm_of_one_lt_re s hs

theorem summable_genuineBInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ => genuineBracketAddressTerm s p :=
  summable_genuineBracketAddressTerm_of_one_lt_re s hs

theorem hasSum_genuineDInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun p : ℕ × ℕ => genuineDirectAddressTerm s p) (genuineDInfinite s) := by
  simpa [genuineDInfinite] using hasSum_directLateralInfinite_of_one_lt_re s hs

theorem hasSum_genuineBInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun p : ℕ × ℕ => genuineBracketAddressTerm s p) (genuineBInfinite s) := by
  simpa [genuineBInfinite] using hasSum_bracketLateralInfinite_of_one_lt_re s hs

theorem hasSum_genuineFInfinite_lateralDifference_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    HasSum
      (fun p : ℕ × ℕ => genuineDirectAddressTerm s p - genuineBracketAddressTerm s p)
      (genuineFInfinite s) := by
  simpa [genuineFInfinite, genuineDInfinite, genuineBInfinite] using
    (hasSum_genuineDInfinite_of_one_lt_re s hs).sub
      (hasSum_genuineBInfinite_of_one_lt_re s hs)

theorem genuineFInfinite_eq_central_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = genuineCentralDoubleSeries s := by
  simpa [genuineFInfinite, genuineDInfinite, genuineBInfinite] using
    directLateralInfinite_sub_bracketLateralInfinite_eq_central_of_one_lt_re s hs

theorem genuineFInfinite_eq_centralFromOddChannel_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = centralFromOddChannel oddDirichletChannel s := by
  rw [genuineFInfinite_eq_central_of_one_lt_re s hs]
  exact genuineCentralDoubleSeries_eq_centralFromOddChannel s hs

theorem genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s := by
  rw [genuineFInfinite_eq_central_of_one_lt_re s hs]
  exact genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs

theorem genuineFInfinite_fundamental_identity_on_one_lt_re :
    ∀ s : ℂ, 1 < s.re → genuineFInfinite s = c0 s * riemannZeta s := by
  intro s hs
  exact genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re s hs

/-- Roadmap spelling: the genuine numerator satisfies `F = c0 * ζ` on `Re(s) > 1`. -/
theorem F_eq_c0_mul_zeta_sigma_gt_one (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s :=
  genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re s hs

/-- Roadmap spelling for the same `Re(s) > 1` identity. -/
theorem C2_identity_sigma_gt_one (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s :=
  F_eq_c0_mul_zeta_sigma_gt_one s hs

end C2
