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

/--
Complete infinite genuine numerator, defined by the analytic identity
`F = c₀ · ζ` on the whole complex plane.  On `Re(s) > 1` this coincides
with the lateral difference `genuineDInfinite − genuineBInfinite`
(theorem `genuineFInfinite_eq_lateral_difference_of_one_lt_re` below);
elsewhere the lateral tsums default to `0`, so the analytic spelling
`c₀ · ζ` is the one we keep on the off-critical strip and beyond.
-/
noncomputable def genuineFInfinite (s : ℂ) : ℂ :=
  c0 s * riemannZeta s

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

/-- On `Re(s) > 1`, the analytic spelling coincides with the lateral
difference `D − B`. -/
theorem genuineFInfinite_eq_lateral_difference_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = genuineDInfinite s - genuineBInfinite s := by
  unfold genuineFInfinite genuineDInfinite genuineBInfinite
  have hcentral :
      directLateralInfinite s - bracketLateralInfinite s = genuineCentralDoubleSeries s :=
    directLateralInfinite_sub_bracketLateralInfinite_eq_central_of_one_lt_re s hs
  rw [hcentral]
  exact (genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs).symm

theorem hasSum_genuineFInfinite_lateralDifference_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    HasSum
      (fun p : ℕ × ℕ => genuineDirectAddressTerm s p - genuineBracketAddressTerm s p)
      (genuineFInfinite s) := by
  rw [genuineFInfinite_eq_lateral_difference_of_one_lt_re s hs]
  exact (hasSum_genuineDInfinite_of_one_lt_re s hs).sub
    (hasSum_genuineBInfinite_of_one_lt_re s hs)

theorem genuineFInfinite_eq_central_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = genuineCentralDoubleSeries s := by
  unfold genuineFInfinite
  exact (genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs).symm

theorem genuineFInfinite_eq_centralFromOddChannel_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineFInfinite s = centralFromOddChannel oddDirichletChannel s := by
  rw [genuineFInfinite_eq_central_of_one_lt_re s hs]
  exact genuineCentralDoubleSeries_eq_centralFromOddChannel s hs

@[simp] theorem genuineFInfinite_eq_c0_mul_riemannZeta (s : ℂ) :
    genuineFInfinite s = c0 s * riemannZeta s := rfl

theorem genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re
    (s : ℂ) (_hs : 1 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s := rfl

/-- Identity `F = c₀ · ζ` on the open right half-plane (free from the
`Re(s) > 1` convergence constraint, since `genuineFInfinite` is now defined
by the analytic spelling). -/
theorem genuineFInfinite_eq_c0_mul_riemannZeta_of_re_pos
    (s : ℂ) (_hs : 0 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s := rfl

/-- Roadmap spelling for the `Re(s) > 0` C2 identity, available directly from
the analytic definition of `genuineFInfinite` (no continuation data needed). -/
theorem F_eq_c0_mul_zeta_sigma_gt_zero_definitional
    (s : ℂ) (_hs : 0 < s.re) :
    genuineFInfinite s = c0 s * riemannZeta s := rfl

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
