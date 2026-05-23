import LeanC2.Foundations.Basic

set_option linter.style.whitespace false

namespace C2

/--
Abstract dominance lemma for the bulk step: a main term `K` that strictly dominates the
error term `E` in norm forces `F = K + E` to be nonzero.
-/
theorem no_zero_of_dominance {F K E : ℂ} {L R : ℝ}
    (hFE : F = K + E)
    (hK : L ≤ ‖K‖)
    (hE : ‖E‖ ≤ R)
    (hLR : R < L) :
    F ≠ 0 := by
  intro hFzero
  have hKrewrite : K = F - E := by
    rw [hFE]
    ring
  have hKleE : ‖K‖ ≤ ‖E‖ := by
    calc
      ‖K‖ = ‖F - E‖ := by rw [hKrewrite]
      _ ≤ ‖F‖ + ‖E‖ := norm_sub_le _ _
      _ = ‖E‖ := by simp [hFzero]
  have hLleR : L ≤ R := le_trans hK (le_trans hKleE hE)
  linarith

/--
Resolvent-shaped dominance: if `Kdelta` splits as a resolvent main term plus an auxiliary
error `Gdelta`, and the resolvent lower bound dominates `Gdelta` and `Edelta`, then `F ≠ 0`.
-/
theorem no_zero_of_resolvent_dominance
    {F Kdelta K2 q Gdelta Edelta : ℂ}
    (hdec : F = Kdelta + Edelta)
    (hres : Kdelta = K2 / (1 - q) + Gdelta)
    (hresLower : ‖K2‖ / (1 + ‖q‖) ≤ ‖K2 / (1 - q)‖)
    (hdom : ‖K2‖ / (1 + ‖q‖) > ‖Gdelta‖ + ‖Edelta‖) :
    F ≠ 0 := by
  have hKG : ‖K2 / (1 - q)‖ - ‖Gdelta‖ ≤ ‖Kdelta‖ := by
    have hres' : K2 / (1 - q) = Kdelta - Gdelta := by
      rw [hres]
      ring
    have htri : ‖K2 / (1 - q)‖ ≤ ‖Kdelta‖ + ‖Gdelta‖ := by
      rw [hres']
      simpa [sub_eq_add_neg, norm_neg] using norm_add_le Kdelta (-Gdelta)
    linarith
  have hGE : ‖Gdelta‖ + ‖Edelta‖ < ‖K2 / (1 - q)‖ :=
    lt_of_lt_of_le hdom hresLower
  have hE_lt_K : ‖Edelta‖ < ‖Kdelta‖ := by
    linarith
  exact no_zero_of_dominance
    (F := F) (K := Kdelta) (E := Edelta) (L := ‖Kdelta‖) (R := ‖Edelta‖)
    hdec le_rfl le_rfl hE_lt_K

/-- Function-level wrapper of `no_zero_of_resolvent_dominance` at a point `s`. -/
theorem no_zero_of_resolvent_dominance_at
    (s : ℂ) {F Kdelta K2 q Gdelta Edelta : ℂ → ℂ}
    (hdec : F s = Kdelta s + Edelta s)
    (hres : Kdelta s = K2 s / (1 - q s) + Gdelta s)
    (hresLower : ‖K2 s‖ / (1 + ‖q s‖) ≤ ‖K2 s / (1 - q s)‖)
    (hdom : ‖K2 s‖ / (1 + ‖q s‖) > ‖Gdelta s‖ + ‖Edelta s‖) :
    F s ≠ 0 := by
  exact no_zero_of_resolvent_dominance
    (F := F s) (Kdelta := Kdelta s) (K2 := K2 s) (q := q s)
    (Gdelta := Gdelta s) (Edelta := Edelta s)
    hdec hres hresLower hdom

end C2