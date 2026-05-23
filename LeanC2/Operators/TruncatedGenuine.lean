import LeanC2.Operators.VerticalResolvent

namespace C2

/-- Rectangular finite direct/lateral C2 operator for the complex Dirichlet coefficient. -/
noncomputable def rectangularDirect (s : ℂ) (K M : Nat) : ℂ :=
  (complexDirichletKernel s K M).directLateralSum

/-- Rectangular finite bracket C2 operator for the complex Dirichlet coefficient. -/
noncomputable def rectangularBracket (s : ℂ) (K M : Nat) : ℂ :=
  (complexDirichletKernel s K M).bracketSum

/-- Rectangular finite genuine numerator `F = D - B`. -/
noncomputable def rectangularGenuine (s : ℂ) (K M : Nat) : ℂ :=
  rectangularDirect s K M - rectangularBracket s K M

/-- Rectangular finite central term left by the lateral cancellation. -/
noncomputable def rectangularCentral (s : ℂ) (K M : Nat) : ℂ :=
  (complexDirichletKernel s K M).factoredCenter

/-- Finite vertical depth factor `∑_{k=2}^K q(s)^k`. -/
noncomputable def rectangularDepthFactor (s : ℂ) (K : Nat) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K, verticalRatio s ^ k

/-- Finite odd-core channel on the rectangle. -/
noncomputable def rectangularOddCoreSum (s : ℂ) (M : Nat) : ℂ :=
  ∑ m ∈ oddCoresUpTo M, complexDirichletCoeff s m

/-- Note-style exponential cutoff weight `e^{-n/X}` on a natural address. -/
noncomputable def exponentialCutoffWeight (X : ℝ) (n : Nat) : ℂ :=
  Complex.exp (-((n : ℂ) / (X : ℂ)))

/-- Residual cutoff profile `g_X(n) = e^{-n/X} - 1`. -/
noncomputable def exponentialCutoffResidualWeight (X : ℝ) (n : Nat) : ℂ :=
  exponentialCutoffWeight X n - 1

/-- Taylor polynomial of order `J - 1` for the residual cutoff profile. -/
noncomputable def exponentialCutoffTaylorPolynomial
    (X : ℝ) (J : Nat) (n : Nat) : ℂ :=
  Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
    (((-1 : ℂ) ^ j) /
        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
      ((n : ℂ) ^ j)

/-- Concrete Taylor remainder of `g_X(n) = e^{-n/X} - 1`. -/
noncomputable def exponentialCutoffTaylorRemainderCoeff
    (X : ℝ) (J : Nat) (n : Nat) : ℂ :=
  exponentialCutoffResidualWeight X n - exponentialCutoffTaylorPolynomial X J n

/-- Immediate complex-exponential upper for the concrete Taylor remainder
coefficient. -/
noncomputable def exponentialCutoffTaylorRemainderCoeffExpUpper
    (X : ℝ) (J : Nat) (n : Nat) : ℝ :=
  ‖-((n : ℂ) / (X : ℂ))‖ ^ J * Real.exp ‖-((n : ℂ) / (X : ℂ))‖

theorem exponentialCutoffResidualWeight_eq_taylorPolynomial_add_remainder
    (X : ℝ) (J n : Nat) :
    exponentialCutoffResidualWeight X n =
      exponentialCutoffTaylorPolynomial X J n +
        exponentialCutoffTaylorRemainderCoeff X J n := by
  unfold exponentialCutoffTaylorRemainderCoeff exponentialCutoffTaylorPolynomial
    exponentialCutoffResidualWeight
  ring

theorem exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper_succ
    (X : ℝ) (J n : Nat) :
    ‖exponentialCutoffTaylorRemainderCoeff X (J + 1) n‖ ≤
      exponentialCutoffTaylorRemainderCoeffExpUpper X (J + 1) n := by
  let z : ℂ := -((n : ℂ) / (X : ℂ))
  have hzterm : ∀ m : ℕ,
      (((-1 : ℂ) ^ m) /
          (((m.factorial : ℕ) : ℂ) * ((X : ℂ) ^ m))) *
        ((n : ℂ) ^ m) = z ^ m / m.factorial := by
    intro m
    calc
      (((-1 : ℂ) ^ m) /
            (((m.factorial : ℕ) : ℂ) * ((X : ℂ) ^ m))) *
          ((n : ℂ) ^ m)
          = (((m.factorial : ℕ) : ℂ)⁻¹) *
              (((-1 : ℂ) ^ m) * (((X : ℂ) ^ m)⁻¹ * (n : ℂ) ^ m)) := by
                simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (((m.factorial : ℕ) : ℂ)⁻¹) * (z ^ m) := by
            congr 1
            calc
              ((-1 : ℂ) ^ m) * (((X : ℂ) ^ m)⁻¹ * (n : ℂ) ^ m)
                  = ((-1 : ℂ) ^ m) * ((((X : ℂ)⁻¹) ^ m) * (n : ℂ) ^ m) := by
                      rw [inv_pow]
              _ = (((-1 : ℂ) * ((X : ℂ)⁻¹ * (n : ℂ))) ^ m) := by
                    rw [mul_pow, mul_pow]
              _ = z ^ m := by
                  simp [z, div_eq_mul_inv, mul_comm]
      _ = z ^ m / m.factorial := by
        simp [div_eq_mul_inv, mul_comm]
  have hsum :
      ∑ m ∈ Finset.range (J + 1), z ^ m / m.factorial =
        1 + exponentialCutoffTaylorPolynomial X (J + 1) n := by
    rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero J), Nat.add_sub_cancel_right]
    have hsplit :=
      (Finset.sum_Ioc_add_eq_sum_Icc
        (f := fun m : ℕ => z ^ m / m.factorial) (a := 0) (b := J) J.zero_le)
    simpa [exponentialCutoffTaylorPolynomial, hzterm, Finset.Icc_succ_left_eq_Ioc,
      add_comm, add_assoc, z] using hsplit.symm
  have hrewrite :
      exponentialCutoffTaylorRemainderCoeff X (J + 1) n =
        Complex.exp z - ∑ m ∈ Finset.range (J + 1), z ^ m / m.factorial := by
    unfold exponentialCutoffTaylorRemainderCoeff exponentialCutoffResidualWeight
      exponentialCutoffWeight
    rw [hsum]
    simp [z, sub_eq_add_neg, add_assoc, add_comm]
  rw [hrewrite]
  simpa [exponentialCutoffTaylorRemainderCoeffExpUpper, z] using
    (Complex.norm_exp_sub_sum_le_norm_mul_exp z (J + 1))

theorem exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper
    (X : ℝ) {J n : Nat} (hJ : 1 ≤ J) :
    ‖exponentialCutoffTaylorRemainderCoeff X J n‖ ≤
      exponentialCutoffTaylorRemainderCoeffExpUpper X J n := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ)
  simpa [Nat.succ_eq_add_one] using
    (exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper_succ X K n)

theorem exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper_24
    (X : ℝ) (n : Nat) :
    ‖exponentialCutoffTaylorRemainderCoeff X 24 n‖ ≤
      exponentialCutoffTaylorRemainderCoeffExpUpper X 24 n := by
  exact exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper X (n := n) (by decide)

/-- Dirichlet coefficient weighted by the exponential cutoff `e^{-n/X}`. -/
noncomputable def exponentialCutoffCoeff (s : ℂ) (X : ℝ) (n : Nat) : ℂ :=
  complexDirichletCoeff s n * exponentialCutoffWeight X n

/-- Residual coefficient `n^{-s}(e^{-n/X} - 1)` for the oscillatory witness. -/
noncomputable def exponentialCutoffResidualCoeff (s : ℂ) (X : ℝ) (n : Nat) : ℂ :=
  complexDirichletCoeff s n * exponentialCutoffResidualWeight X n

theorem exponentialCutoffResidualCoeff_eq_sub
    (s : ℂ) (X : ℝ) (n : Nat) :
    exponentialCutoffResidualCoeff s X n =
      exponentialCutoffCoeff s X n - complexDirichletCoeff s n := by
  unfold exponentialCutoffResidualCoeff exponentialCutoffCoeff
    exponentialCutoffResidualWeight exponentialCutoffWeight
  ring

/-- Rectangular finite direct/lateral sum with note-style exponential cutoff. -/
noncomputable def rectangularExponentialDirect
    (s : ℂ) (K M : Nat) (X : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M, directPairTerm (exponentialCutoffCoeff s X) k m

/-- Rectangular finite bracket sum with note-style exponential cutoff. -/
noncomputable def rectangularExponentialBracket
    (s : ℂ) (K M : Nat) (X : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M, bracketTerm (exponentialCutoffCoeff s X) k m

/-- Rectangular finite genuine operator with note-style exponential cutoff. -/
noncomputable def rectangularExponentialGenuine
    (s : ℂ) (K M : Nat) (X : ℝ) : ℂ :=
  rectangularExponentialDirect s K M X - rectangularExponentialBracket s K M X

/--
Rectangular finite residual operator driven by the residual profile
`g_X(n) = e^{-n/X} - 1`.
-/
noncomputable def rectangularExponentialResidual
    (s : ℂ) (K M : Nat) (X : ℝ) : ℂ :=
  (∑ k ∈ Finset.Icc 2 K,
      ∑ m ∈ oddCoresUpTo M,
        directPairTerm (exponentialCutoffResidualCoeff s X) k m) -
    (∑ k ∈ Finset.Icc 2 K,
      ∑ m ∈ oddCoresUpTo M,
        bracketTerm (exponentialCutoffResidualCoeff s X) k m)

theorem rectangularExponentialGenuine_eq_residual_add_rectangularGenuine
    (s : ℂ) (K M : Nat) (X : ℝ) :
    rectangularExponentialGenuine s K M X =
      rectangularExponentialResidual s K M X + rectangularGenuine s K M := by
  unfold rectangularExponentialGenuine rectangularExponentialDirect
    rectangularExponentialBracket rectangularExponentialResidual
    rectangularGenuine rectangularDirect rectangularBracket
  have hdirect :
      (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            directPairTerm (exponentialCutoffCoeff s X) k m) =
        (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            directPairTerm (exponentialCutoffResidualCoeff s X) k m) +
        (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            directPairTerm (complexDirichletCoeff s) k m) := by
    calc
      (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            directPairTerm (exponentialCutoffCoeff s X) k m) =
        ∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            (directPairTerm (exponentialCutoffResidualCoeff s X) k m +
              directPairTerm (complexDirichletCoeff s) k m) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          refine Finset.sum_congr rfl ?_
          intro m _hm
          unfold directPairTerm directLegTerm exponentialCutoffCoeff
            exponentialCutoffResidualCoeff exponentialCutoffResidualWeight
            exponentialCutoffWeight
          ring
      _ =
        (∑ k ∈ Finset.Icc 2 K,
            ∑ m ∈ oddCoresUpTo M,
              directPairTerm (exponentialCutoffResidualCoeff s X) k m) +
          (∑ k ∈ Finset.Icc 2 K,
            ∑ m ∈ oddCoresUpTo M,
              directPairTerm (complexDirichletCoeff s) k m) := by
          simp_rw [Finset.sum_add_distrib]
  have hbracket :
      (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            bracketTerm (exponentialCutoffCoeff s X) k m) =
        (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            bracketTerm (exponentialCutoffResidualCoeff s X) k m) +
        (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            bracketTerm (complexDirichletCoeff s) k m) := by
    calc
      (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            bracketTerm (exponentialCutoffCoeff s X) k m) =
        ∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            (bracketTerm (exponentialCutoffResidualCoeff s X) k m +
              bracketTerm (complexDirichletCoeff s) k m) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          refine Finset.sum_congr rfl ?_
          intro m _hm
          unfold bracketTerm exponentialCutoffCoeff
            exponentialCutoffResidualCoeff exponentialCutoffResidualWeight
            exponentialCutoffWeight
          ring
      _ =
        (∑ k ∈ Finset.Icc 2 K,
            ∑ m ∈ oddCoresUpTo M,
              bracketTerm (exponentialCutoffResidualCoeff s X) k m) +
          (∑ k ∈ Finset.Icc 2 K,
            ∑ m ∈ oddCoresUpTo M,
              bracketTerm (complexDirichletCoeff s) k m) := by
          simp_rw [Finset.sum_add_distrib]
  rw [hdirect, hbracket]
  unfold FormalDirichletKernel.directLateralSum FormalDirichletKernel.bracketSum
  simp [complexDirichletKernel]
  ring

theorem rectangularExponentialGenuine_eq_geometric
    (s : ℂ) (K M : Nat) (X : ℝ) :
    rectangularExponentialGenuine s K M X =
      ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          centerGeometricTerm (exponentialCutoffCoeff s X) k m := by
  unfold rectangularExponentialGenuine rectangularExponentialDirect
    rectangularExponentialBracket
  exact rectangular_lateral_cancellation_geometric
    (exponentialCutoffCoeff s X) K M

theorem rectangularExponentialResidual_eq_geometric
    (s : ℂ) (K M : Nat) (X : ℝ) :
    rectangularExponentialResidual s K M X =
      ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          centerGeometricTerm (exponentialCutoffResidualCoeff s X) k m := by
  unfold rectangularExponentialResidual
  exact rectangular_lateral_cancellation_geometric
    (exponentialCutoffResidualCoeff s X) K M

/--
Finite Taylor main term for the exponential residual, before packaging the
coefficients into oscillatory moments.
-/
noncomputable def rectangularExponentialTaylorMain
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M,
      centerGeometricTerm
        (fun n =>
          complexDirichletCoeff s n *
            Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
              (((-1 : ℂ) ^ j) /
                  (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
                ((n : ℂ) ^ j))
        k m

/-- Finite oscillatory moment attached to the `j`-th Taylor coefficient. -/
noncomputable def rectangularExponentialOscillatoryMoment
    (s : ℂ) (K M j : Nat) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M,
      centerGeometricTerm
        (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
        k m

/-- Pointwise oscillatory main term for the finite exponential residual. -/
noncomputable def rectangularExponentialPointwiseOscillatoryMain
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℂ :=
  Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
    (((-1 : ℂ) ^ j) /
        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
      rectangularExponentialOscillatoryMoment s K M j

theorem rectangularExponentialTaylorMain_eq_pointwiseOscillatoryMain
    (s : ℂ) (K M J : Nat) (X : ℝ) :
    rectangularExponentialTaylorMain s K M J X =
      rectangularExponentialPointwiseOscillatoryMain s K M J X := by
  let coeff : Nat → ℂ := fun j =>
    (((-1 : ℂ) ^ j) /
        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j)))
  have hterm :
      ∀ k : Nat, ∀ m : Nat,
        centerGeometricTerm
            (fun n =>
              complexDirichletCoeff s n *
                Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
                  coeff j * ((n : ℂ) ^ j))
            k m =
          ∑ j ∈ Finset.Icc 1 (J - 1),
            coeff j *
              centerGeometricTerm
                (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                k m := by
    intro k m
    let prfix : ℂ :=
      (2 : ℂ) * algebraMap ℚ ℂ (dyadicWeight k) *
        complexDirichletCoeff s (2 ^ k * m)
    calc
      centerGeometricTerm
          (fun n =>
            complexDirichletCoeff s n *
              Finset.sum (Finset.Icc 1 (J - 1)) fun j =>
                coeff j * ((n : ℂ) ^ j))
          k m =
        prfix *
          (∑ j ∈ Finset.Icc 1 (J - 1), coeff j * ((2 ^ k * m : ℂ) ^ j)) := by
          simp [centerGeometricTerm, prfix, mul_assoc]
      _ = ∑ j ∈ Finset.Icc 1 (J - 1),
            prfix * (coeff j * ((2 ^ k * m : ℂ) ^ j)) := by
          rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.Icc 1 (J - 1),
            coeff j *
              centerGeometricTerm
                (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                k m := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          simp [centerGeometricTerm, prfix, mul_assoc, mul_left_comm, mul_comm]
  unfold rectangularExponentialTaylorMain
    rectangularExponentialPointwiseOscillatoryMain
  calc
    ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          centerGeometricTerm
            (fun n =>
              complexDirichletCoeff s n *
                ∑ j ∈ Finset.Icc 1 (J - 1), coeff j * ((n : ℂ) ^ j))
            k m =
      ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          ∑ j ∈ Finset.Icc 1 (J - 1),
            coeff j *
              centerGeometricTerm
                (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                k m := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        refine Finset.sum_congr rfl ?_
        intro m _hm
        exact hterm k m
    _ = ∑ k ∈ Finset.Icc 2 K,
          ∑ j ∈ Finset.Icc 1 (J - 1),
            ∑ m ∈ oddCoresUpTo M,
              coeff j *
                centerGeometricTerm
                  (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                  k m := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 (J - 1),
          ∑ k ∈ Finset.Icc 2 K,
            ∑ m ∈ oddCoresUpTo M,
              coeff j *
                centerGeometricTerm
                  (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                  k m := by
        rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 (J - 1),
          coeff j * rectangularExponentialOscillatoryMoment s K M j := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        unfold rectangularExponentialOscillatoryMoment
        calc
          ∑ k ∈ Finset.Icc 2 K,
              ∑ m ∈ oddCoresUpTo M,
                coeff j *
                  centerGeometricTerm
                    (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                    k m =
            ∑ k ∈ Finset.Icc 2 K,
              coeff j *
                ∑ m ∈ oddCoresUpTo M,
                  centerGeometricTerm
                    (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                    k m := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              rw [← Finset.mul_sum]
          _ = coeff j *
              ∑ k ∈ Finset.Icc 2 K,
                ∑ m ∈ oddCoresUpTo M,
                  centerGeometricTerm
                    (fun n => complexDirichletCoeff s n * ((n : ℂ) ^ j))
                    k m := by
              rw [← Finset.mul_sum]
          _ = coeff j * rectangularExponentialOscillatoryMoment s K M j := by
              rfl
    _ = rectangularExponentialPointwiseOscillatoryMain s K M J X := by
      simp [rectangularExponentialPointwiseOscillatoryMain, coeff]

/--
Finite remainder contribution left after replacing `e^{-n/X} - 1` by a Taylor
polynomial plus a pointwise residual profile.
-/
noncomputable def rectangularExponentialTaylorRemainder
    (s : ℂ) (K M : Nat) (remainderCoeff : Nat → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M,
      centerGeometricTerm
        (fun n => complexDirichletCoeff s n * remainderCoeff n)
        k m

/-- Exact norm upper for the finite Taylor remainder, obtained by termwise norms. -/
noncomputable def rectangularExponentialTaylorRemainderExactUpper
    (s : ℂ) (K M : Nat) (remainderCoeff : Nat → ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M,
      ‖centerGeometricTerm
          (fun n => complexDirichletCoeff s n * remainderCoeff n)
          k m‖

theorem rectangularExponentialTaylorRemainder_norm_le_exactUpper
    (s : ℂ) (K M : Nat) (remainderCoeff : Nat → ℂ) :
    ‖rectangularExponentialTaylorRemainder s K M remainderCoeff‖ ≤
      rectangularExponentialTaylorRemainderExactUpper s K M remainderCoeff := by
  unfold rectangularExponentialTaylorRemainder
    rectangularExponentialTaylorRemainderExactUpper
  calc
    ‖∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          centerGeometricTerm
            (fun n => complexDirichletCoeff s n * remainderCoeff n)
            k m‖ ≤
      ∑ k ∈ Finset.Icc 2 K,
        ‖∑ m ∈ oddCoresUpTo M,
            centerGeometricTerm
              (fun n => complexDirichletCoeff s n * remainderCoeff n)
              k m‖ := by
        simpa using
          (norm_sum_le (Finset.Icc 2 K) fun k =>
            ∑ m ∈ oddCoresUpTo M,
              centerGeometricTerm
                (fun n => complexDirichletCoeff s n * remainderCoeff n)
                k m)
    _ ≤ ∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            ‖centerGeometricTerm
                (fun n => complexDirichletCoeff s n * remainderCoeff n)
                k m‖ := by
          refine Finset.sum_le_sum ?_
          intro k _hk
          simpa using
            (norm_sum_le (oddCoresUpTo M) fun m =>
              centerGeometricTerm
                (fun n => complexDirichletCoeff s n * remainderCoeff n)
                k m)
    _ = rectangularExponentialTaylorRemainderExactUpper s K M remainderCoeff := by
        rfl

/-- Pointwise coefficient upper transported through the finite Taylor remainder. -/
noncomputable def rectangularExponentialTaylorRemainderPointwiseUpper
    (s : ℂ) (K M : Nat) (coeffUpper : Nat → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ∑ m ∈ oddCoresUpTo M,
      ‖(2 : ℂ) * algebraMap ℚ ℂ (dyadicWeight k)‖ *
        (‖complexDirichletCoeff s (2 ^ k * m)‖ * coeffUpper (2 ^ k * m))

theorem rectangularExponentialTaylorRemainderExactUpper_le_pointwiseUpper
    (s : ℂ) (K M : Nat) (remainderCoeff : Nat → ℂ) (coeffUpper : Nat → ℝ)
    (hcoeff : ∀ n : Nat, ‖remainderCoeff n‖ ≤ coeffUpper n) :
    rectangularExponentialTaylorRemainderExactUpper s K M remainderCoeff ≤
      rectangularExponentialTaylorRemainderPointwiseUpper s K M coeffUpper := by
  unfold rectangularExponentialTaylorRemainderExactUpper
    rectangularExponentialTaylorRemainderPointwiseUpper
  refine Finset.sum_le_sum ?_
  intro k _hk
  refine Finset.sum_le_sum ?_
  intro m _hm
  have hcoeff' := hcoeff (2 ^ k * m)
  unfold centerGeometricTerm
  change ‖(2 : ℂ) * algebraMap ℚ ℂ (dyadicWeight k) *
      (complexDirichletCoeff s (2 ^ k * m) * remainderCoeff (2 ^ k * m))‖ ≤
    ‖(2 : ℂ) * algebraMap ℚ ℂ (dyadicWeight k)‖ *
      (‖complexDirichletCoeff s (2 ^ k * m)‖ * coeffUpper (2 ^ k * m))
  rw [norm_mul]
  have hinner :
      ‖complexDirichletCoeff s (2 ^ k * m) * remainderCoeff (2 ^ k * m)‖ ≤
        ‖complexDirichletCoeff s (2 ^ k * m)‖ *
          coeffUpper (2 ^ k * m) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hcoeff' (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)

theorem rectangularExponentialTaylorRemainder_norm_le_pointwiseUpper
    (s : ℂ) (K M : Nat) (remainderCoeff : Nat → ℂ) (coeffUpper : Nat → ℝ)
    (hcoeff : ∀ n : Nat, ‖remainderCoeff n‖ ≤ coeffUpper n) :
    ‖rectangularExponentialTaylorRemainder s K M remainderCoeff‖ ≤
      rectangularExponentialTaylorRemainderPointwiseUpper s K M coeffUpper := by
  exact le_trans
    (rectangularExponentialTaylorRemainder_norm_le_exactUpper s K M remainderCoeff)
    (rectangularExponentialTaylorRemainderExactUpper_le_pointwiseUpper
      s K M remainderCoeff coeffUpper hcoeff)

/-- Explicit upper for the finite Taylor remainder using the complex-exp remainder bound. -/
noncomputable def rectangularExponentialTaylorRemainderExpUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℝ :=
  rectangularExponentialTaylorRemainderPointwiseUpper s K M
    (exponentialCutoffTaylorRemainderCoeffExpUpper X J)

theorem rectangularExponentialTaylorRemainder_norm_le_expUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) (hJ : 1 ≤ J) :
    ‖rectangularExponentialTaylorRemainder s K M
        (exponentialCutoffTaylorRemainderCoeff X J)‖ ≤
      rectangularExponentialTaylorRemainderExpUpper s K M J X := by
  exact rectangularExponentialTaylorRemainder_norm_le_pointwiseUpper
    s K M (exponentialCutoffTaylorRemainderCoeff X J)
    (exponentialCutoffTaylorRemainderCoeffExpUpper X J)
    (fun n => exponentialCutoffTaylorRemainderCoeff_norm_le_expUpper X (J := J) (n := n) hJ)

theorem rectangularExponentialTaylorRemainder_norm_le_expUpper_24
    (s : ℂ) (K M : Nat) (X : ℝ) :
    ‖rectangularExponentialTaylorRemainder s K M
        (exponentialCutoffTaylorRemainderCoeff X 24)‖ ≤
      rectangularExponentialTaylorRemainderExpUpper s K M 24 X := by
  exact rectangularExponentialTaylorRemainder_norm_le_expUpper s K M 24 X (by decide)

/-- Exact pointwise oscillatory witness for the finite exponential residual. -/
noncomputable def rectangularExponentialPointwiseOscillatoryExactUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℝ :=
  ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
    rectangularExponentialTaylorRemainderExactUpper s K M
      (exponentialCutoffTaylorRemainderCoeff X J)

/-- Explicit pointwise oscillatory witness for the finite exponential residual,
using the exponential remainder upper. -/
noncomputable def rectangularExponentialPointwiseOscillatoryExpUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℝ :=
  ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
    rectangularExponentialTaylorRemainderExpUpper s K M J X

/-- Default pointwise oscillatory witness for the finite exponential residual. -/
noncomputable abbrev rectangularExponentialPointwiseOscillatoryUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) : ℝ :=
  rectangularExponentialPointwiseOscillatoryExpUpper s K M J X

theorem rectangularExponentialResidual_eq_taylorMain_add_remainder_of_weightExpansion
    (s : ℂ) (K M J : Nat) (X : ℝ) (remainderCoeff : Nat → ℂ)
    (hweight : ∀ n : Nat,
      exponentialCutoffResidualWeight X n =
        Finset.sum (Finset.Icc 1 (J - 1)) (fun j =>
          (((-1 : ℂ) ^ j) /
              (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
            ((n : ℂ) ^ j)) +
          remainderCoeff n) :
    rectangularExponentialResidual s K M X =
      rectangularExponentialTaylorMain s K M J X +
        rectangularExponentialTaylorRemainder s K M remainderCoeff := by
  rw [rectangularExponentialResidual_eq_geometric]
  have hterm :
      ∀ k : Nat, ∀ m : Nat,
        centerGeometricTerm (exponentialCutoffResidualCoeff s X) k m =
          centerGeometricTerm
              (fun n =>
                complexDirichletCoeff s n *
                  Finset.sum (Finset.Icc 1 (J - 1)) (fun j =>
                    (((-1 : ℂ) ^ j) /
                        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
                      ((n : ℂ) ^ j)))
              k m +
            centerGeometricTerm
              (fun n => complexDirichletCoeff s n * remainderCoeff n)
              k m := by
    intro k m
    unfold centerGeometricTerm exponentialCutoffResidualCoeff
    rw [hweight (2 ^ k * m)]
    ring
  calc
    ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          centerGeometricTerm (exponentialCutoffResidualCoeff s X) k m =
      ∑ k ∈ Finset.Icc 2 K,
        ∑ m ∈ oddCoresUpTo M,
          (centerGeometricTerm
              (fun n =>
                complexDirichletCoeff s n *
                  Finset.sum (Finset.Icc 1 (J - 1)) (fun j =>
                    (((-1 : ℂ) ^ j) /
                        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
                      ((n : ℂ) ^ j)))
              k m +
            centerGeometricTerm
              (fun n => complexDirichletCoeff s n * remainderCoeff n)
              k m) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        refine Finset.sum_congr rfl ?_
        intro m _hm
        exact hterm k m
    _ =
      (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            centerGeometricTerm
              (fun n =>
                complexDirichletCoeff s n *
                  Finset.sum (Finset.Icc 1 (J - 1)) (fun j =>
                    (((-1 : ℂ) ^ j) /
                        (((j.factorial : ℕ) : ℂ) * ((X : ℂ) ^ j))) *
                      ((n : ℂ) ^ j)))
              k m) +
        (∑ k ∈ Finset.Icc 2 K,
          ∑ m ∈ oddCoresUpTo M,
            centerGeometricTerm
              (fun n => complexDirichletCoeff s n * remainderCoeff n)
              k m) := by
        simp_rw [Finset.sum_add_distrib]
    _ =
      rectangularExponentialTaylorMain s K M J X +
        rectangularExponentialTaylorRemainder s K M remainderCoeff := by
        rfl

theorem rectangularExponentialResidual_eq_taylorMain_add_taylorRemainder
    (s : ℂ) (K M J : Nat) (X : ℝ) :
    rectangularExponentialResidual s K M X =
      rectangularExponentialTaylorMain s K M J X +
        rectangularExponentialTaylorRemainder s K M
          (exponentialCutoffTaylorRemainderCoeff X J) := by
  refine rectangularExponentialResidual_eq_taylorMain_add_remainder_of_weightExpansion
    s K M J X (exponentialCutoffTaylorRemainderCoeff X J) ?_
  intro n
  simpa [exponentialCutoffTaylorPolynomial] using
    exponentialCutoffResidualWeight_eq_taylorPolynomial_add_remainder X J n

theorem rectangularExponentialResidual_norm_le_pointwiseOscillatoryExactUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) :
    ‖rectangularExponentialResidual s K M X‖ ≤
      rectangularExponentialPointwiseOscillatoryExactUpper s K M J X := by
  rw [rectangularExponentialResidual_eq_taylorMain_add_taylorRemainder,
    rectangularExponentialTaylorMain_eq_pointwiseOscillatoryMain]
  calc
    ‖rectangularExponentialPointwiseOscillatoryMain s K M J X +
        rectangularExponentialTaylorRemainder s K M
          (exponentialCutoffTaylorRemainderCoeff X J)‖ ≤
      ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
        ‖rectangularExponentialTaylorRemainder s K M
          (exponentialCutoffTaylorRemainderCoeff X J)‖ := by
        exact norm_add_le _ _
    _ ≤ ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
          rectangularExponentialTaylorRemainderExactUpper s K M
            (exponentialCutoffTaylorRemainderCoeff X J) := by
          exact add_le_add le_rfl
            (rectangularExponentialTaylorRemainder_norm_le_exactUpper s K M
              (exponentialCutoffTaylorRemainderCoeff X J))
    _ = rectangularExponentialPointwiseOscillatoryExactUpper s K M J X := by
        rfl

theorem rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) (hJ : 1 ≤ J) :
    ‖rectangularExponentialResidual s K M X‖ ≤
      rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
  rw [rectangularExponentialResidual_eq_taylorMain_add_taylorRemainder,
    rectangularExponentialTaylorMain_eq_pointwiseOscillatoryMain]
  calc
    ‖rectangularExponentialPointwiseOscillatoryMain s K M J X +
        rectangularExponentialTaylorRemainder s K M
          (exponentialCutoffTaylorRemainderCoeff X J)‖ ≤
      ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
        ‖rectangularExponentialTaylorRemainder s K M
          (exponentialCutoffTaylorRemainderCoeff X J)‖ := by
        exact norm_add_le _ _
    _ ≤ ‖rectangularExponentialPointwiseOscillatoryMain s K M J X‖ +
          rectangularExponentialTaylorRemainderExpUpper s K M J X := by
          exact add_le_add le_rfl
            (rectangularExponentialTaylorRemainder_norm_le_expUpper s K M J X hJ)
    _ = rectangularExponentialPointwiseOscillatoryExpUpper s K M J X := by
        rfl

theorem rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper_24
    (s : ℂ) (K M : Nat) (X : ℝ) :
    ‖rectangularExponentialResidual s K M X‖ ≤
      rectangularExponentialPointwiseOscillatoryExpUpper s K M 24 X := by
  exact rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper
    s K M 24 X (by decide)

theorem rectangularExponentialResidual_norm_le_pointwiseOscillatoryUpper
    (s : ℂ) (K M J : Nat) (X : ℝ) (hJ : 1 ≤ J) :
    ‖rectangularExponentialResidual s K M X‖ ≤
      rectangularExponentialPointwiseOscillatoryUpper s K M J X := by
  exact rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper
    s K M J X hJ

theorem rectangularExponentialResidual_norm_le_pointwiseOscillatoryUpper_24
    (s : ℂ) (K M : Nat) (X : ℝ) :
    ‖rectangularExponentialResidual s K M X‖ ≤
      rectangularExponentialPointwiseOscillatoryUpper s K M 24 X := by
  exact rectangularExponentialResidual_norm_le_pointwiseOscillatoryExpUpper_24
    s K M X

lemma rectangularDepthFactor_eq_kernel_depthFactor (s : ℂ) (K M : Nat) :
    rectangularDepthFactor s K = (complexDirichletKernel s K M).depthFactor := by
  rfl

lemma rectangularOddCoreSum_eq_kernel_coreSum (s : ℂ) (K M : Nat) :
    rectangularOddCoreSum s M = (complexDirichletKernel s K M).coreSum := by
  rfl

lemma rectangularCentral_eq_depth_core (s : ℂ) (K M : Nat) :
    rectangularCentral s K M =
      (2 : ℂ) * rectangularDepthFactor s K * rectangularOddCoreSum s M := by
  unfold rectangularCentral FormalDirichletKernel.factoredCenter
  rw [← rectangularDepthFactor_eq_kernel_depthFactor s K M,
    ← rectangularOddCoreSum_eq_kernel_coreSum s K M]

/-- Rectangular finite C2 identity `F = D - B = central`. -/
theorem rectangularGenuine_eq_central (s : ℂ) (K M : Nat) :
    rectangularGenuine s K M = rectangularCentral s K M := by
  unfold rectangularGenuine rectangularDirect rectangularBracket rectangularCentral
  exact complexDirichletKernel_lateral_sub_bracket_eq_factoredCenter s K M

/-- Rectangular finite C2 identity with vertical and odd-core factors exposed. -/
theorem rectangularGenuine_eq_depth_core (s : ℂ) (K M : Nat) :
    rectangularGenuine s K M =
      (2 : ℂ) * rectangularDepthFactor s K * rectangularOddCoreSum s M := by
  rw [rectangularGenuine_eq_central, rectangularCentral_eq_depth_core]

/-- Rectangular finite C2 identity using the closed depth factor. -/
theorem rectangularGenuine_eq_closed (s : ℂ) (K M : Nat)
    (hK : 2 ≤ K) (hr : verticalRatio s ≠ 1) :
    rectangularGenuine s K M =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        rectangularOddCoreSum s M := by
  unfold rectangularGenuine rectangularDirect rectangularBracket
  rw [complexDirichletKernel_lateral_sub_bracket_eq_closed s K M hK]
  · rw [rectangularOddCoreSum_eq_kernel_coreSum s K M]
  · exact hr

/-- Rectangular finite C2 identity using the closed depth factor in the right half-plane. -/
theorem rectangularGenuine_eq_closed_of_re_pos (s : ℂ) (K M : Nat)
    (hs : 0 < s.re) (hK : 2 ≤ K) :
    rectangularGenuine s K M =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        rectangularOddCoreSum s M := by
  exact rectangularGenuine_eq_closed s K M hK (verticalRatio_ne_one_of_re_pos s hs)

/-- Rectangular finite C2 identity using the closed depth factor on the off-critical strip. -/
theorem rectangularGenuine_eq_closed_of_offCriticalStrip (s : ℂ) (K M : Nat)
    (hs : offCriticalStrip s) (hK : 2 ≤ K) :
    rectangularGenuine s K M =
      (2 : ℂ) * (complexDirichletKernel s K M).closedDepthFactor *
        rectangularOddCoreSum s M := by
  exact rectangularGenuine_eq_closed_of_re_pos s K M hs.1 hK

end C2
