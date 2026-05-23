import LeanC2.Analytic.OddChannel
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace C2

/--
Address-indexed direct lateral term on the infinite C2 grid.

The first coordinate encodes the shifted depth `k = j + 2`; the second coordinate
encodes the odd core `m = 2 * n + 1`.
-/
noncomputable def genuineDirectAddressTerm (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  directPairTerm (complexDirichletCoeff s) (p.1 + 2) (2 * p.2 + 1)

/-- Address-indexed bracket term on the infinite C2 grid. -/
noncomputable def genuineBracketAddressTerm (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  bracketTerm (complexDirichletCoeff s) (p.1 + 2) (2 * p.2 + 1)

/-- Address-indexed central remainder term left by infinite lateral cancellation. -/
noncomputable def genuineCentralAddressTerm (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  centerRemainderTerm (complexDirichletCoeff s) (p.1 + 2) (2 * p.2 + 1)

lemma genuine_address_lateral_cancellation (s : ℂ) (p : ℕ × ℕ) :
    genuineDirectAddressTerm s p - genuineBracketAddressTerm s p =
      genuineCentralAddressTerm s p := by
  rcases p with ⟨j, n⟩
  unfold genuineDirectAddressTerm genuineBracketAddressTerm genuineCentralAddressTerm
  exact local_lateral_cancellation (R := ℂ) (f := complexDirichletCoeff s)
    (k := j + 2) (m := 2 * n + 1) (by omega) ⟨n, rfl⟩

lemma genuineCentralAddressTerm_eq_explicit (s : ℂ) (p : ℕ × ℕ) :
    genuineCentralAddressTerm s p =
      (2 : ℂ) * (verticalRatio s ^ (p.1 + 2) *
        complexDirichletCoeff s (2 * p.2 + 1)) := by
  rcases p with ⟨j, n⟩
  unfold genuineCentralAddressTerm
  rw [centerRemainderTerm_eq_geometric]
  have hsep :
      complexDirichletCoeff s (2 ^ (j + 2) * (2 * n + 1)) =
        complexDirichletCoeff s 2 ^ (j + 2) * complexDirichletCoeff s (2 * n + 1) := by
    rw [complexDirichletCoeff_mul s
      (pow_ne_zero (j + 2) (by norm_num : (2 : Nat) ≠ 0))
      (by omega : 2 * n + 1 ≠ 0)]
    rw [complexDirichletCoeff_two_pow]
  rw [centerGeometricTerm_eq_separated
    (f := complexDirichletCoeff s)
    (u := fun k => complexDirichletCoeff s 2 ^ k)
    (v := complexDirichletCoeff s)
    hsep]
  unfold separatedCenterGeometricTerm
  rw [centerDepthFactor_pow (R := ℂ) (r := complexDirichletCoeff s 2) (k := j + 2)]
  simp [verticalRatio]
  ring

/-- Infinite direct/lateral C2 series indexed by the address grid `(j, n)`. -/
noncomputable def genuineDirectDoubleSeries (s : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, genuineDirectAddressTerm s p

/-- Infinite bracket C2 series indexed by the address grid `(j, n)`. -/
noncomputable def genuineBracketDoubleSeries (s : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, genuineBracketAddressTerm s p

/-- Roadmap operator `D∞`: the infinite direct/lateral C2 series. -/
noncomputable abbrev directLateralInfinite (s : ℂ) : ℂ :=
  genuineDirectDoubleSeries s

/-- Roadmap operator `B∞`: the infinite bracket C2 series. -/
noncomputable abbrev bracketLateralInfinite (s : ℂ) : ℂ :=
  genuineBracketDoubleSeries s

/--
The post-cancellation genuine central double series:
`2 * ∑_{k≥2} ∑_{m odd} q(s)^k m^(-s)`.

The first natural index is shifted by `+2` to encode `k ≥ 2`; the second index
parametrizes odd positive integers as `2 * n + 1`.
-/
noncomputable def genuineCentralDoubleSeries (s : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,
    (2 : ℂ) * (verticalRatio s ^ (p.1 + 2) *
      complexDirichletCoeff s (2 * p.2 + 1))

/-- Explicit address term of the infinite central series. -/
noncomputable def genuineCentralExplicitAddressTerm (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  (2 : ℂ) * (verticalRatio s ^ (p.1 + 2) *
    complexDirichletCoeff s (2 * p.2 + 1))

/-- A single direct leg on the infinite address grid. -/
noncomputable def genuineLegAddressTerm (epsilon : BranchSign) (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  directLegTerm (complexDirichletCoeff s)
    (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))

theorem genuineDoubleSeries_lateral_cancellation_of_summable
    (s : ℂ)
    (hDirect : Summable fun p : ℕ × ℕ => genuineDirectAddressTerm s p)
    (hBracket : Summable fun p : ℕ × ℕ => genuineBracketAddressTerm s p) :
    genuineDirectDoubleSeries s - genuineBracketDoubleSeries s =
      genuineCentralDoubleSeries s := by
  unfold genuineDirectDoubleSeries genuineBracketDoubleSeries
  rw [← hDirect.tsum_sub hBracket]
  have hfun :
      (fun p : ℕ × ℕ => genuineDirectAddressTerm s p - genuineBracketAddressTerm s p) =
        (fun p : ℕ × ℕ =>
          (2 : ℂ) * (verticalRatio s ^ (p.1 + 2) *
            complexDirichletCoeff s (2 * p.2 + 1))) := by
    funext p
    rw [genuine_address_lateral_cancellation, genuineCentralAddressTerm_eq_explicit]
  simpa [genuineCentralDoubleSeries] using congrArg (fun f => ∑' p : ℕ × ℕ, f p) hfun

lemma summable_verticalDepthTail_norm_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    Summable fun j : ℕ => ‖verticalRatio s ^ (j + 2)‖ := by
  have hgeom : Summable fun j : ℕ => ‖verticalRatio s‖ ^ j :=
    summable_geometric_of_lt_one (norm_nonneg _) (verticalRatio_norm_lt_one_of_re_pos s hs)
  have htail : Summable fun j : ℕ => ‖verticalRatio s‖ ^ (j + 2) :=
    hgeom.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  simpa [norm_pow] using htail

lemma summable_oddDirichletCoeff_norm_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖complexDirichletCoeff s (2 * n + 1)‖ := by
  have hnorm := summable_riemannZetaSummand (s := s) hs
  have hodd : Summable fun n : ℕ =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (2 * n + 1)‖ :=
    hnorm.comp_injective (by
      intro a b h
      have h' : 2 * a + 1 = 2 * b + 1 := by simpa using h
      omega)
  exact hodd.congr fun n => by
    rw [complexDirichletCoeff_eq_cpow_neg s (by omega : 2 * n + 1 ≠ 0)]
    simp [riemannZetaSummandHom, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Odd index whose image gives a single genuine leg as `2*q+1`. -/
def genuineLegOddIndex (epsilon : BranchSign) (p : ℕ × ℕ) : ℕ :=
  match epsilon with
  | BranchSign.plus => 2 ^ (p.1 + 1) * (2 * p.2 + 1)
  | BranchSign.minus => 2 ^ (p.1 + 1) * (2 * p.2 + 1) - 1

lemma natDescendant_eq_two_mul_genuineLegOddIndex_add_one
    (epsilon : BranchSign) (p : ℕ × ℕ) :
    natDescendant (p.1 + 2) epsilon (2 * p.2 + 1) =
      2 * genuineLegOddIndex epsilon p + 1 := by
  rcases p with ⟨j, n⟩
  cases epsilon
  · dsimp [genuineLegOddIndex, natDescendant]
    have hpow : 2 ^ (j + 2) * (2 * n + 1) = 2 * (2 ^ (j + 1) * (2 * n + 1)) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    have hpos : 0 < 2 ^ (j + 1) * (2 * n + 1) := by positivity
    change 2 * (2 ^ (j + 1) * (2 * n + 1)) - 1 =
      2 * (2 ^ (j + 1) * (2 * n + 1) - 1) + 1
    omega
  · dsimp [genuineLegOddIndex, natDescendant]
    have hpow : 2 ^ (j + 2) * (2 * n + 1) = 2 * (2 ^ (j + 1) * (2 * n + 1)) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]

lemma genuineLegOddIndex_injective (epsilon : BranchSign) :
    Function.Injective (genuineLegOddIndex epsilon) := by
  intro a b hab
  rcases a with ⟨j, n⟩
  rcases b with ⟨j', n'⟩
  have hdesc :
      natDescendant (j + 2) epsilon (2 * n + 1) =
        natDescendant (j' + 2) epsilon (2 * n' + 1) := by
    rw [natDescendant_eq_two_mul_genuineLegOddIndex_add_one epsilon (j, n),
      natDescendant_eq_two_mul_genuineLegOddIndex_add_one epsilon (j', n'), hab]
  rcases natDescendant_address_unique
      (k := j + 2) (k' := j' + 2)
      (epsilon := epsilon) (epsilon' := epsilon)
      (m := 2 * n + 1) (m' := 2 * n' + 1)
      (by omega) (by omega) ⟨n, rfl⟩ ⟨n', rfl⟩ hdesc with
    ⟨hk, _heq, hm⟩
  have hj : j = j' := Nat.add_right_cancel hk
  have hn : n = n' := by omega
  simp [hj, hn]

lemma summable_genuineLegOddCoeff_norm_of_one_lt_re
    (epsilon : BranchSign) (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ =>
      ‖complexDirichletCoeff s (2 * genuineLegOddIndex epsilon p + 1)‖ := by
  exact (summable_oddDirichletCoeff_norm_of_one_lt_re s hs).comp_injective
    (genuineLegOddIndex_injective epsilon)

lemma summable_genuineLegDescendantCoeff_norm_of_one_lt_re
    (epsilon : BranchSign) (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ =>
      ‖complexDirichletCoeff s
        (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ := by
  refine (summable_genuineLegOddCoeff_norm_of_one_lt_re epsilon s hs).congr ?_
  intro p
  rw [natDescendant_eq_two_mul_genuineLegOddIndex_add_one]

lemma dyadicWeight_le_one (k : Nat) : dyadicWeight k ≤ 1 := by
  unfold dyadicWeight
  have hk : (1 : ℚ) ≤ 2 ^ k := by
    exact one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  have hpos : 0 < (2 : ℚ) ^ k := by positivity
  exact (inv_le_one₀ hpos).2 hk

lemma dyadicWeight_complex_norm_le_one (k : Nat) :
    ‖((dyadicWeight k : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_ratCast]
  have hnonnegQ : 0 ≤ dyadicWeight k := by
    unfold dyadicWeight
    positivity
  have hnonneg : 0 ≤ ((dyadicWeight k : ℚ) : ℝ) := by
    exact_mod_cast hnonnegQ
  rw [abs_of_nonneg hnonneg]
  exact_mod_cast dyadicWeight_le_one k

lemma genuineLegAddressTerm_eq_weighted
    (epsilon : BranchSign) (s : ℂ) (p : ℕ × ℕ) :
    genuineLegAddressTerm epsilon s p =
      algebraMap ℚ ℂ (dyadicWeight (p.1 + 2)) *
        complexDirichletCoeff s
          (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1)) := by
  rcases p with ⟨j, n⟩
  unfold genuineLegAddressTerm
  rw [directLegTerm_eq_weighted_address (f := complexDirichletCoeff s)]
  exact ⟨by omega, ⟨n, rfl⟩, rfl⟩

lemma norm_genuineLegAddressTerm_le_descendantCoeff
    (epsilon : BranchSign) (s : ℂ) (p : ℕ × ℕ) :
    ‖genuineLegAddressTerm epsilon s p‖ ≤
      ‖complexDirichletCoeff s
        (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ := by
  rw [genuineLegAddressTerm_eq_weighted]
  calc
    ‖algebraMap ℚ ℂ (dyadicWeight (p.1 + 2)) *
        complexDirichletCoeff s (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ =
      ‖algebraMap ℚ ℂ (dyadicWeight (p.1 + 2))‖ *
        ‖complexDirichletCoeff s (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ := by
          rw [norm_mul]
    _ ≤ 1 * ‖complexDirichletCoeff s
          (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using dyadicWeight_complex_norm_le_one (p.1 + 2))
            (norm_nonneg _)
    _ = ‖complexDirichletCoeff s
          (natDescendant (p.1 + 2) epsilon (2 * p.2 + 1))‖ := by ring

lemma summable_genuineLegAddressTerm_of_one_lt_re
    (epsilon : BranchSign) (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ => genuineLegAddressTerm epsilon s p := by
  have hnorm : Summable fun p : ℕ × ℕ => ‖genuineLegAddressTerm epsilon s p‖ := by
    exact Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun p => norm_genuineLegAddressTerm_le_descendantCoeff epsilon s p)
      (summable_genuineLegDescendantCoeff_norm_of_one_lt_re epsilon s hs)
  exact hnorm.of_norm

lemma genuineDirectAddressTerm_eq_leg_sum (s : ℂ) (p : ℕ × ℕ) :
    genuineDirectAddressTerm s p =
      genuineLegAddressTerm BranchSign.minus s p +
        genuineLegAddressTerm BranchSign.plus s p := by
  rcases p with ⟨j, n⟩
  rfl

theorem summable_genuineDirectAddressTerm_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ => genuineDirectAddressTerm s p := by
  have hminus : Summable fun p : ℕ × ℕ => genuineLegAddressTerm BranchSign.minus s p :=
    summable_genuineLegAddressTerm_of_one_lt_re BranchSign.minus s hs
  have hplus : Summable fun p : ℕ × ℕ => genuineLegAddressTerm BranchSign.plus s p :=
    summable_genuineLegAddressTerm_of_one_lt_re BranchSign.plus s hs
  have hsum : Summable fun p : ℕ × ℕ =>
      genuineLegAddressTerm BranchSign.minus s p +
        genuineLegAddressTerm BranchSign.plus s p :=
    hminus.add hplus
  exact hsum.congr (genuineDirectAddressTerm_eq_leg_sum s)

/-- Convergence of the roadmap direct operator `D∞` in the absolute-convergence half-plane. -/
theorem hasSum_directLateralInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun p : ℕ × ℕ => genuineDirectAddressTerm s p) (directLateralInfinite s) := by
  simpa [directLateralInfinite, genuineDirectDoubleSeries] using
    (summable_genuineDirectAddressTerm_of_one_lt_re s hs).hasSum

lemma genuineBracketAddressTerm_eq_direct_sub_central
    (s : ℂ) (p : ℕ × ℕ) :
    genuineBracketAddressTerm s p =
      genuineDirectAddressTerm s p - genuineCentralAddressTerm s p := by
  calc
    genuineBracketAddressTerm s p =
        genuineDirectAddressTerm s p -
          (genuineDirectAddressTerm s p - genuineBracketAddressTerm s p) := by ring
    _ = genuineDirectAddressTerm s p - genuineCentralAddressTerm s p := by
        rw [genuine_address_lateral_cancellation]

lemma genuineBracketAddressTerm_eq_direct_sub_explicit
    (s : ℂ) (p : ℕ × ℕ) :
    genuineBracketAddressTerm s p =
      genuineDirectAddressTerm s p - genuineCentralExplicitAddressTerm s p := by
  rw [genuineBracketAddressTerm_eq_direct_sub_central, genuineCentralAddressTerm_eq_explicit,
    genuineCentralExplicitAddressTerm]

set_option maxHeartbeats 0 in
-- The explicit `Nat × Nat` summability target for the bracket-side difference still
-- exhausts bounded heartbeats after reindexing both legs, so keep the cap local here.
lemma summable_genuineBracketExplicitDiff_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ =>
      genuineDirectAddressTerm s p -
        ((2 : ℂ) * (verticalRatio s ^ (p.1 + 2) * complexDirichletCoeff s (2 * p.2 + 1))) := by
  have hDirect : Summable fun p : ℕ × ℕ => genuineDirectAddressTerm s p :=
    summable_genuineDirectAddressTerm_of_one_lt_re s hs
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hv : Summable fun j : ℕ => ‖verticalRatio s ^ (j + 2)‖ :=
    summable_verticalDepthTail_norm_of_re_pos s hs0
  have ho : Summable fun n : ℕ => ‖complexDirichletCoeff s (2 * n + 1)‖ :=
    summable_oddDirichletCoeff_norm_of_one_lt_re s hs
  have hCentralBase : Summable fun p : ℕ × ℕ =>
      verticalRatio s ^ (p.1 + 2) * complexDirichletCoeff s (2 * p.2 + 1) :=
    summable_mul_of_summable_norm hv ho
  exact hDirect.sub (hCentralBase.mul_left (2 : ℂ))

theorem summable_genuineBracketAddressTerm_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : ℕ × ℕ => genuineBracketAddressTerm s p := by
  exact (summable_genuineBracketExplicitDiff_of_one_lt_re s hs).congr fun p => by
    rw [genuineBracketAddressTerm_eq_direct_sub_explicit, genuineCentralExplicitAddressTerm]

/-- Convergence of the roadmap bracket operator `B∞` in the absolute-convergence half-plane. -/
theorem hasSum_bracketLateralInfinite_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun p : ℕ × ℕ => genuineBracketAddressTerm s p) (bracketLateralInfinite s) := by
  simpa [bracketLateralInfinite, genuineBracketDoubleSeries] using
    (summable_genuineBracketAddressTerm_of_one_lt_re s hs).hasSum

theorem genuineDoubleSeries_lateral_cancellation_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineDirectDoubleSeries s - genuineBracketDoubleSeries s =
      genuineCentralDoubleSeries s := by
  exact genuineDoubleSeries_lateral_cancellation_of_summable s
    (summable_genuineDirectAddressTerm_of_one_lt_re s hs)
    (summable_genuineBracketAddressTerm_of_one_lt_re s hs)

/-- In `Re(s) > 1`, the infinite lateral difference `D∞ - B∞` collapses to the central sum. -/
theorem directLateralInfinite_sub_bracketLateralInfinite_eq_central_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    directLateralInfinite s - bracketLateralInfinite s =
      genuineCentralDoubleSeries s := by
  simpa [directLateralInfinite, bracketLateralInfinite] using
    genuineDoubleSeries_lateral_cancellation_of_one_lt_re s hs

theorem genuineCentralDoubleSeries_eq_centralFromOddChannel
    (s : ℂ) (hs : 1 < s.re) :
    genuineCentralDoubleSeries s = centralFromOddChannel oddDirichletChannel s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hv : Summable fun j : ℕ => ‖verticalRatio s ^ (j + 2)‖ :=
    summable_verticalDepthTail_norm_of_re_pos s hs0
  have ho : Summable fun n : ℕ => ‖complexDirichletCoeff s (2 * n + 1)‖ :=
    summable_oddDirichletCoeff_norm_of_one_lt_re s hs
  have hprod :=
    tsum_mul_tsum_of_summable_norm
      (f := fun j : ℕ => verticalRatio s ^ (j + 2))
      (g := fun n : ℕ => complexDirichletCoeff s (2 * n + 1))
      hv ho
  unfold genuineCentralDoubleSeries
    centralFromOddChannel verticalDepthTailFromTwo
    oddDirichletChannel
  rw [tsum_mul_left]
  rw [← hprod]
  ring

theorem genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineCentralDoubleSeries s = c0 s * riemannZeta s := by
  rw [genuineCentralDoubleSeries_eq_centralFromOddChannel s hs]
  exact centralFromOddDirichletChannel_identity_of_one_lt_re s hs

theorem genuineDoubleSeries_lateral_cancellation_c0_zeta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    genuineDirectDoubleSeries s - genuineBracketDoubleSeries s =
      c0 s * riemannZeta s := by
  rw [genuineDoubleSeries_lateral_cancellation_of_one_lt_re s hs]
  exact genuineCentralDoubleSeries_eq_c0_mul_riemannZeta_of_one_lt_re s hs

end C2
