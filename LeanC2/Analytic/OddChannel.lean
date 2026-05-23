import LeanC2.Route.FundamentalAlgebra
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace C2

/-- The absolutely convergent Dirichlet channel over the positive integers. -/
noncomputable def positiveDirichletChannel (s : ℂ) : ℂ :=
  ∑' n : ℕ, complexDirichletCoeff s (n + 1)

/-- The odd subchannel `1, 3, 5, ...` of the Dirichlet coefficients. -/
noncomputable def oddDirichletChannel (s : ℂ) : ℂ :=
  ∑' n : ℕ, complexDirichletCoeff s (2 * n + 1)

/-- The positive even subchannel `2, 4, 6, ...` of the Dirichlet coefficients. -/
noncomputable def evenDirichletChannel (s : ℂ) : ℂ :=
  ∑' n : ℕ, complexDirichletCoeff s (2 * (n + 1))

lemma complexDirichletCoeff_eq_cpow_neg (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    complexDirichletCoeff s n = (n : ℂ) ^ (-s) := by
  unfold complexDirichletCoeff
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnC]
  congr 1
  rw [Complex.natCast_log]
  ring_nf

lemma summable_positiveDirichletCoeff_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Summable fun n : ℕ => complexDirichletCoeff s (n + 1) := by
  have hnorm := summable_riemannZetaSummand (s := s) hs
  have hall : Summable fun n : ℕ =>
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) n :=
    hnorm.of_norm
  have htail : Summable fun n : ℕ =>
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (n + 1) :=
    hall.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  exact htail.congr fun n => by
    rw [complexDirichletCoeff_eq_cpow_neg s (by omega : n + 1 ≠ 0)]
    simp [riemannZetaSummandHom, Nat.cast_add, Nat.cast_one]

theorem positiveDirichletChannel_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    positiveDirichletChannel s = riemannZeta s := by
  unfold positiveDirichletChannel
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  rw [complexDirichletCoeff_eq_cpow_neg s (by omega : n + 1 ≠ 0)]
  rw [Complex.cpow_neg]
  simp [one_div, Nat.cast_add, Nat.cast_one]

theorem evenDirichletChannel_eq_coeff_two_mul_positive (s : ℂ) :
    evenDirichletChannel s =
      complexDirichletCoeff s 2 * positiveDirichletChannel s := by
  unfold evenDirichletChannel positiveDirichletChannel
  calc
    (∑' n : ℕ, complexDirichletCoeff s (2 * (n + 1)))
        = ∑' n : ℕ, complexDirichletCoeff s 2 *
            complexDirichletCoeff s (n + 1) := by
          apply tsum_congr
          intro n
          exact complexDirichletCoeff_mul s (by norm_num) (by omega : n + 1 ≠ 0)
    _ = complexDirichletCoeff s 2 *
        ∑' n : ℕ, complexDirichletCoeff s (n + 1) := by
          rw [tsum_mul_left]

theorem positiveDirichletChannel_eq_odd_add_even (s : ℂ) (hs : 1 < s.re) :
    positiveDirichletChannel s = oddDirichletChannel s + evenDirichletChannel s := by
  let f : ℕ → ℂ := fun n => complexDirichletCoeff s (n + 1)
  have hf : Summable f := summable_positiveDirichletCoeff_of_one_lt_re s hs
  have heven : Summable fun k : ℕ => f (2 * k) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a = 2 * b := by simpa using h
      omega)
  have hodd : Summable fun k : ℕ => f (2 * k + 1) :=
    hf.comp_injective (by
      intro a b h
      have h' : 2 * a + 1 = 2 * b + 1 := by simpa using h
      omega)
  have hsplit :=
    (HasSum.even_add_odd heven.hasSum hodd.hasSum).tsum_eq
  unfold positiveDirichletChannel oddDirichletChannel evenDirichletChannel
  rw [hsplit]
  congr 1

theorem oddDirichletChannel_eulerRelation_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    oddDirichletChannel s =
      (1 - complexDirichletCoeff s 2) * riemannZeta s := by
  have hsplit := positiveDirichletChannel_eq_odd_add_even s hs
  have hpos := positiveDirichletChannel_eq_riemannZeta s hs
  have heven := evenDirichletChannel_eq_coeff_two_mul_positive s
  rw [heven, hpos] at hsplit
  have hstep :
      oddDirichletChannel s + complexDirichletCoeff s 2 * riemannZeta s =
        riemannZeta s :=
    hsplit.symm
  calc
    oddDirichletChannel s =
        (oddDirichletChannel s + complexDirichletCoeff s 2 * riemannZeta s) -
          complexDirichletCoeff s 2 * riemannZeta s := by
          ring
    _ = riemannZeta s - complexDirichletCoeff s 2 * riemannZeta s := by rw [hstep]
    _ = (1 - complexDirichletCoeff s 2) * riemannZeta s := by ring

theorem centralFromOddDirichletChannel_identity_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    centralFromOddChannel oddDirichletChannel s = c0 s * riemannZeta s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  unfold centralFromOddChannel
  rw [oddDirichletChannel_eulerRelation_of_one_lt_re s hs]
  have hc0 := c0_eq_c0FromVerticalFactor_of_re_pos s hs0
  unfold c0FromVerticalFactor at hc0
  calc
    (2 : ℂ) * verticalDepthTailFromTwo s *
        ((1 - complexDirichletCoeff s 2) * riemannZeta s)
        = ((2 : ℂ) * verticalDepthTailFromTwo s *
            (1 - complexDirichletCoeff s 2)) * riemannZeta s := by ring
    _ = c0 s * riemannZeta s := by rw [← hc0]

end C2
