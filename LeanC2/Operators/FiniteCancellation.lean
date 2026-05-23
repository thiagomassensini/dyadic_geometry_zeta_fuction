import LeanC2.Foundations.Dyadic

namespace C2

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- C2 bracket center `c = 2^k * m`. -/
def c2Center (k m : Nat) : Nat :=
  2 ^ k * m

/-- A direct `D`-side leg term, using `keff` weight. -/
def directLegTerm (f : Nat -> R) (n : Nat) : R :=
  algebraMap ℚ R (directLegWeight n) * f n

/-- The two lateral terms of `D`, grouped by a bracket address. -/
def directPairTerm (f : Nat -> R) (k m : Nat) : R :=
  directLegTerm f (natDescendant k BranchSign.minus m) +
    directLegTerm f (natDescendant k BranchSign.plus m)

/-- The bracket term attached to a C2 center. -/
def bracketTerm (f : Nat -> R) (k m : Nat) : R :=
  algebraMap ℚ R (dyadicWeight k) *
    (f (natDescendant k BranchSign.minus m) +
      f (natDescendant k BranchSign.plus m) - 2 * f (c2Center k m))

/-- The central term left after lateral cancellation. -/
def centerRemainderTerm (f : Nat -> R) (k m : Nat) : R :=
  algebraMap ℚ R (dyadicWeight k) * (2 * f (c2Center k m))

lemma directLegTerm_eq_weighted_address (f : Nat -> R) {n k : Nat}
    {epsilon : BranchSign} {m : Nat} (h : IsC2LegAddress n k epsilon m) :
    directLegTerm f n = algebraMap ℚ R (dyadicWeight k) * f n := by
  unfold directLegTerm
  rw [halving_law_of_address h]

/-- Local lateral cancellation: `D` legs minus the bracket leaves only the center. -/
theorem local_lateral_cancellation (f : Nat -> R) {k m : Nat} (hk : 2 ≤ k) (hm : Odd m) :
    directPairTerm f k m - bracketTerm f k m = centerRemainderTerm f k m := by
  have hLeft : directLegWeight (natDescendant k BranchSign.minus m) = dyadicWeight k := by
    exact halving_law_of_address (n := natDescendant k BranchSign.minus m)
      (k := k) (epsilon := BranchSign.minus) (m := m) ⟨hk, hm, rfl⟩
  have hRight : directLegWeight (natDescendant k BranchSign.plus m) = dyadicWeight k := by
    exact halving_law_of_address (n := natDescendant k BranchSign.plus m)
      (k := k) (epsilon := BranchSign.plus) (m := m) ⟨hk, hm, rfl⟩
  unfold directPairTerm directLegTerm bracketTerm centerRemainderTerm
  rw [hLeft, hRight]
  ring

abbrev C2Address := Nat × Nat

def C2Address.depth (a : C2Address) : Nat :=
  a.1

def C2Address.core (a : C2Address) : Nat :=
  a.2

/-- A valid finite C2 bracket address. -/
def IsValidC2Address (a : C2Address) : Prop :=
  2 ≤ a.depth ∧ Odd a.core

/-- Direct finite sum over both legs of each address. -/
def directPairFiniteSum (f : Nat -> R) (A : Finset C2Address) : R :=
  A.sum fun a => directPairTerm f a.depth a.core

/-- Finite sum of C2 bracket terms. -/
def bracketFiniteSum (f : Nat -> R) (A : Finset C2Address) : R :=
  A.sum fun a => bracketTerm f a.depth a.core

/-- Finite sum of the center remainders left after cancellation. -/
def centerRemainderFiniteSum (f : Nat -> R) (A : Finset C2Address) : R :=
  A.sum fun a => centerRemainderTerm f a.depth a.core

/-- Finite lateral cancellation over any valid finite family of C2 addresses. -/
theorem finite_lateral_cancellation (f : Nat -> R) (A : Finset C2Address)
    (hA : ∀ a ∈ A, IsValidC2Address a) :
    directPairFiniteSum f A - bracketFiniteSum f A = centerRemainderFiniteSum f A := by
  unfold directPairFiniteSum bracketFiniteSum centerRemainderFiniteSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rcases hA a ha with ⟨hk, hm⟩
  exact local_lateral_cancellation f hk hm

/-- Odd cores up to the finite cutoff `M`. -/
def oddCoresUpTo (M : Nat) : Finset Nat :=
  (Finset.range (M + 1)).filter Odd

lemma mem_oddCoresUpTo {m M : Nat} :
    m ∈ oddCoresUpTo M ↔ m ≤ M ∧ Odd m := by
  simp [oddCoresUpTo]

/-- Rectangular finite C2 address cutoff: `2 ≤ k ≤ K`, `m ≤ M`, `m` odd. -/
def c2Rectangle (K M : Nat) : Finset C2Address :=
  (Finset.Icc 2 K) ×ˢ oddCoresUpTo M

lemma mem_c2Rectangle {a : C2Address} {K M : Nat} :
    a ∈ c2Rectangle K M ↔
      2 ≤ a.depth ∧ a.depth ≤ K ∧ a.core ≤ M ∧ Odd a.core := by
  rcases a with ⟨k, m⟩
  constructor
  · intro ha
    rw [c2Rectangle, Finset.mem_product] at ha
    rcases ha with ⟨hk, hm⟩
    rw [Finset.mem_Icc] at hk
    rw [mem_oddCoresUpTo] at hm
    exact ⟨hk.1, hk.2, hm.1, hm.2⟩
  · intro ha
    rw [c2Rectangle, Finset.mem_product]
    exact ⟨Finset.mem_Icc.mpr ⟨ha.1, ha.2.1⟩,
      mem_oddCoresUpTo.mpr ⟨ha.2.2.1, ha.2.2.2⟩⟩

theorem c2Rectangle_valid (K M : Nat) :
    ∀ a ∈ c2Rectangle K M, IsValidC2Address a := by
  intro a ha
  rw [mem_c2Rectangle] at ha
  exact ⟨ha.1, ha.2.2.2⟩

/-- Finite lateral cancellation on the rectangular cutoff. -/
theorem rectangular_lateral_cancellation (f : Nat -> R) (K M : Nat) :
    directPairFiniteSum f (c2Rectangle K M) - bracketFiniteSum f (c2Rectangle K M) =
      centerRemainderFiniteSum f (c2Rectangle K M) := by
  exact finite_lateral_cancellation f (c2Rectangle K M) (c2Rectangle_valid K M)

theorem directPairFiniteSum_c2Rectangle (f : Nat -> R) (K M : Nat) :
    directPairFiniteSum f (c2Rectangle K M) =
      ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm f k m := by
  unfold directPairFiniteSum c2Rectangle C2Address.depth C2Address.core
  rw [Finset.sum_product]

theorem bracketFiniteSum_c2Rectangle (f : Nat -> R) (K M : Nat) :
    bracketFiniteSum f (c2Rectangle K M) =
      ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm f k m := by
  unfold bracketFiniteSum c2Rectangle C2Address.depth C2Address.core
  rw [Finset.sum_product]

theorem centerRemainderFiniteSum_c2Rectangle (f : Nat -> R) (K M : Nat) :
    centerRemainderFiniteSum f (c2Rectangle K M) =
      ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerRemainderTerm f k m := by
  unfold centerRemainderFiniteSum c2Rectangle C2Address.depth C2Address.core
  rw [Finset.sum_product]

/-- Rectangular lateral cancellation, written as the explicit double sum from the notes. -/
theorem rectangular_lateral_cancellation_double (f : Nat -> R) (K M : Nat) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm f k m) -
      (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm f k m) =
        ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerRemainderTerm f k m := by
  have h := rectangular_lateral_cancellation (R := R) f K M
  rw [directPairFiniteSum_c2Rectangle, bracketFiniteSum_c2Rectangle,
    centerRemainderFiniteSum_c2Rectangle] at h
  exact h

/-- Central remainder in the explicit geometric form from the notes. -/
def centerGeometricTerm (f : Nat -> R) (k m : Nat) : R :=
  (2 : R) * algebraMap ℚ R (dyadicWeight k) * f (2 ^ k * m)

theorem centerRemainderTerm_eq_geometric (f : Nat -> R) (k m : Nat) :
    centerRemainderTerm f k m = centerGeometricTerm f k m := by
  unfold centerRemainderTerm centerGeometricTerm c2Center
  ring

theorem centerRemainderDoubleSum_eq_geometric (f : Nat -> R) (K M : Nat) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerRemainderTerm f k m) =
      ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerGeometricTerm f k m := by
  refine Finset.sum_congr rfl ?_
  intro k _hk
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact centerRemainderTerm_eq_geometric f k m

/-- Rectangular cancellation with the center side expanded as `2 * 2^{-k} * f(2^k*m)`. -/
theorem rectangular_lateral_cancellation_geometric (f : Nat -> R) (K M : Nat) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm f k m) -
      (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm f k m) =
        ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerGeometricTerm f k m := by
  rw [rectangular_lateral_cancellation_double]
  exact centerRemainderDoubleSum_eq_geometric f K M

/-- The `k`-side coefficient in the separated center sum. -/
def centerDepthFactor (u : Nat -> R) (k : Nat) : R :=
  algebraMap ℚ R (dyadicWeight k) * u k

/-- Center term after substituting a separated form `f(2^k*m)=u k * v m`. -/
def separatedCenterGeometricTerm (u v : Nat -> R) (k m : Nat) : R :=
  (2 : R) * centerDepthFactor u k * v m

/-- Product form of a finite separated center sum. -/
def separatedCenterProduct (u v : Nat -> R) (K M : Nat) : R :=
  (2 : R) * (∑ k ∈ Finset.Icc 2 K, centerDepthFactor u k) *
    (∑ m ∈ oddCoresUpTo M, v m)

theorem centerGeometricTerm_eq_separated (f u v : Nat -> R) {k m : Nat}
    (hsep : f (2 ^ k * m) = u k * v m) :
    centerGeometricTerm f k m = separatedCenterGeometricTerm u v k m := by
  unfold centerGeometricTerm separatedCenterGeometricTerm centerDepthFactor
  rw [hsep]
  ring

theorem centerGeometricDoubleSum_eq_separated (f u v : Nat -> R) (K M : Nat)
    (hsep : ∀ k ∈ Finset.Icc 2 K, ∀ m ∈ oddCoresUpTo M, f (2 ^ k * m) = u k * v m) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerGeometricTerm f k m) =
      ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, separatedCenterGeometricTerm u v k m := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  refine Finset.sum_congr rfl ?_
  intro m hm
  exact centerGeometricTerm_eq_separated f u v (hsep k hk m hm)

theorem separatedCenterDoubleSum_eq_product (u v : Nat -> R) (K M : Nat) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, separatedCenterGeometricTerm u v k m) =
      separatedCenterProduct u v K M := by
  unfold separatedCenterGeometricTerm separatedCenterProduct
  calc
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, (2 : R) * centerDepthFactor u k * v m)
        = ∑ k ∈ Finset.Icc 2 K, ((2 : R) * centerDepthFactor u k) *
            (∑ m ∈ oddCoresUpTo M, v m) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [Finset.mul_sum]
    _ = (∑ k ∈ Finset.Icc 2 K, (2 : R) * centerDepthFactor u k) *
          (∑ m ∈ oddCoresUpTo M, v m) := by
          rw [Finset.sum_mul]
    _ = (2 : R) * (∑ k ∈ Finset.Icc 2 K, centerDepthFactor u k) *
          (∑ m ∈ oddCoresUpTo M, v m) := by
          rw [← Finset.mul_sum]

/-- Finite geometric-factorization step for a separated center function. -/
theorem centerGeometricDoubleSum_factorized (f u v : Nat -> R) (K M : Nat)
    (hsep : ∀ k ∈ Finset.Icc 2 K, ∀ m ∈ oddCoresUpTo M, f (2 ^ k * m) = u k * v m) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerGeometricTerm f k m) =
      separatedCenterProduct u v K M := by
  rw [centerGeometricDoubleSum_eq_separated f u v K M hsep]
  exact separatedCenterDoubleSum_eq_product u v K M

/-- Formal C2 multiplicativity on a finite rectangle. -/
def IsC2MultiplicativeOnRectangle (f : Nat -> R) (K M : Nat) : Prop :=
  ∀ k ∈ Finset.Icc 2 K, ∀ m ∈ oddCoresUpTo M, f (2 ^ k * m) = f (2 ^ k) * f m

/-- The depth factor for a formally multiplicative Dirichlet-like term. -/
def dirichletDepthFactor (f : Nat -> R) (k : Nat) : R :=
  centerDepthFactor (fun j => f (2 ^ j)) k

/-- Product form of the finite C2 center sum for a multiplicative Dirichlet-like term. -/
def dirichletSeparatedCenterProduct (f : Nat -> R) (K M : Nat) : R :=
  separatedCenterProduct (fun k => f (2 ^ k)) f K M

theorem centerGeometricDoubleSum_factorized_multiplicative (f : Nat -> R) (K M : Nat)
    (hMul : IsC2MultiplicativeOnRectangle f K M) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, centerGeometricTerm f k m) =
      dirichletSeparatedCenterProduct f K M := by
  unfold dirichletSeparatedCenterProduct
  exact centerGeometricDoubleSum_factorized f (fun k => f (2 ^ k)) f K M hMul

/-- Rectangular cancellation plus formal multiplicativity gives the separated product form. -/
theorem rectangular_lateral_cancellation_factorized_multiplicative (f : Nat -> R) (K M : Nat)
    (hMul : IsC2MultiplicativeOnRectangle f K M) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm f k m) -
      (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm f k m) =
        dirichletSeparatedCenterProduct f K M := by
  rw [rectangular_lateral_cancellation_geometric]
  exact centerGeometricDoubleSum_factorized_multiplicative f K M hMul

lemma dyadicWeight_eq_inv_pow (k : Nat) :
    dyadicWeight k = ((2 : ℚ)⁻¹) ^ k := by
  unfold dyadicWeight
  rw [inv_pow]

/-- The single depth ratio obtained from `2^{-k} r^k`. -/
def depthGeometricRatio (r : R) : R :=
  algebraMap ℚ R ((2 : ℚ)⁻¹) * r

/-- If the depth part is `r^k`, then the C2 depth factor is `(r/2)^k`. -/
theorem centerDepthFactor_pow (r : R) (k : Nat) :
    centerDepthFactor (fun j => r ^ j) k = depthGeometricRatio r ^ k := by
  unfold centerDepthFactor depthGeometricRatio
  rw [dyadicWeight_eq_inv_pow, map_pow, mul_pow]

/-- A finite-depth sequence is geometric on the C2 depth cutoff. -/
def IsGeometricOnDepth (u : Nat -> R) (K : Nat) (r : R) : Prop :=
  ∀ k ∈ Finset.Icc 2 K, u k = r ^ k

theorem separatedCenterProduct_geometricDepth (u v : Nat -> R) (K M : Nat) (r : R)
    (hgeom : IsGeometricOnDepth u K r) :
    separatedCenterProduct u v K M =
      (2 : R) * (∑ k ∈ Finset.Icc 2 K, depthGeometricRatio r ^ k) *
        (∑ m ∈ oddCoresUpTo M, v m) := by
  unfold separatedCenterProduct
  congr 2
  refine Finset.sum_congr rfl ?_
  intro k hk
  unfold centerDepthFactor depthGeometricRatio
  rw [hgeom k hk, dyadicWeight_eq_inv_pow, map_pow, mul_pow]

/-- A Dirichlet-like finite sequence has geometric values on powers of two. -/
def HasGeometricDepthOnRectangle (f : Nat -> R) (K : Nat) (r : R) : Prop :=
  ∀ k ∈ Finset.Icc 2 K, f (2 ^ k) = r ^ k

theorem dirichletSeparatedCenterProduct_geometricDepth (f : Nat -> R) (K M : Nat) (r : R)
    (hdepth : HasGeometricDepthOnRectangle f K r) :
    dirichletSeparatedCenterProduct f K M =
      (2 : R) * (∑ k ∈ Finset.Icc 2 K, depthGeometricRatio r ^ k) *
        (∑ m ∈ oddCoresUpTo M, f m) := by
  unfold dirichletSeparatedCenterProduct
  exact separatedCenterProduct_geometricDepth (fun k => f (2 ^ k)) f K M r hdepth

/-- Rectangular cancellation with both multiplicativity and geometric depth made explicit. -/
theorem rectangular_lateral_cancellation_geometric_depth (f : Nat -> R) (K M : Nat) (r : R)
    (hMul : IsC2MultiplicativeOnRectangle f K M)
    (hdepth : HasGeometricDepthOnRectangle f K r) :
    (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, directPairTerm f k m) -
      (∑ k ∈ Finset.Icc 2 K, ∑ m ∈ oddCoresUpTo M, bracketTerm f k m) =
        (2 : R) * (∑ k ∈ Finset.Icc 2 K, depthGeometricRatio r ^ k) *
          (∑ m ∈ oddCoresUpTo M, f m) := by
  rw [rectangular_lateral_cancellation_factorized_multiplicative f K M hMul]
  exact dirichletSeparatedCenterProduct_geometricDepth f K M r hdepth

section FieldClosedForm

variable {F : Type*} [Field F] [Algebra ℚ F]

omit [Algebra ℚ F] in
/-- Closed form for the finite C2 depth geometric sum. -/
theorem depthGeometricSum_Icc_closed (q : F) {K : Nat} (hK : 2 ≤ K) (hq : q ≠ 1) :
    (∑ k ∈ Finset.Icc 2 K, q ^ k) = (q ^ (K + 1) - q ^ 2) / (q - 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  exact geom_sum_Ico hq (by omega : 2 ≤ K + 1)

/-- Closed form specialized to the C2 depth ratio `(r/2)`. -/
theorem depthGeometricRatioSum_Icc_closed (r : F) {K : Nat} (hK : 2 ≤ K)
    (hr : depthGeometricRatio r ≠ 1) :
    (∑ k ∈ Finset.Icc 2 K, depthGeometricRatio r ^ k) =
      (depthGeometricRatio r ^ (K + 1) - depthGeometricRatio r ^ 2) /
        (depthGeometricRatio r - 1) := by
  exact depthGeometricSum_Icc_closed (depthGeometricRatio r) hK hr

end FieldClosedForm

end C2
