import Mathlib
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import LeanC2.Foundations.Basic

namespace C2

/-- The two C2 branch directions. -/
inductive BranchSign where
  | minus
  | plus
deriving DecidableEq, Repr, Fintype

namespace BranchSign

/-- The signed offset attached to a branch. -/
def toInt : BranchSign -> Int
  | minus => -1
  | plus => 1

@[simp] theorem toInt_minus : toInt BranchSign.minus = -1 := rfl
@[simp] theorem toInt_plus : toInt BranchSign.plus = 1 := rfl

end BranchSign

/-- Two-adic valuation on naturals, using Mathlib's `padicValNat`. -/
def v2 (n : Nat) : Nat :=
  padicValNat 2 n

/-- Effective C2 depth for an odd leg. -/
def keff (n : Nat) : Nat :=
  max (v2 (n - 1)) (v2 (n + 1))

/-- Integer descendant produced from an odd core `m` at depth `k`. -/
def descendant (k : Nat) (epsilon : BranchSign) (m : Int) : Int :=
  (2 : Int) ^ k * m + epsilon.toInt

/-- Natural-number descendant used for finite/cutoff bookkeeping. -/
def natDescendant (k : Nat) (epsilon : BranchSign) (m : Nat) : Nat :=
  match epsilon with
  | BranchSign.minus => 2 ^ k * m - 1
  | BranchSign.plus => 2 ^ k * m + 1

lemma natDescendant_cast {k m : Nat} {epsilon : BranchSign} (hm : Odd m) :
    ((natDescendant k epsilon m : Nat) : Int) = descendant k epsilon (m : Int) := by
  cases epsilon
  · have hmpos : 0 < m := by
      rcases hm with ⟨a, rfl⟩
      omega
    have hle : 1 ≤ 2 ^ k * m := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by norm_num) _) hmpos)
    change ((2 ^ k * m - 1 : Nat) : Int) = (2 : Int) ^ k * (m : Int) + -1
    rw [Nat.cast_sub hle]
    rw [Nat.cast_mul, Nat.cast_pow]
    ring
  · change ((2 ^ k * m + 1 : Nat) : Int) = (2 : Int) ^ k * (m : Int) + 1
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring

lemma odd_nat_pos {m : Nat} (hm : Odd m) : 0 < m := by
  rcases hm with ⟨a, rfl⟩
  omega

lemma odd_natCast_int {m : Nat} (hm : Odd m) : Odd (m : Int) := by
  rcases hm with ⟨a, rfl⟩
  exact ⟨a, by norm_num⟩

lemma odd_divMaxPow_two {a : Nat} (ha : a ≠ 0) : Odd (a.divMaxPow 2) := by
  have hnotdvd : ¬ 2 ∣ a.divMaxPow 2 := Nat.not_dvd_divMaxPow (by norm_num : 1 < 2) ha
  have hnotEven : ¬ Even (a.divMaxPow 2) := by
    rwa [even_iff_two_dvd]
  exact Nat.not_even_iff_odd.mp hnotEven

lemma two_le_v2_of_four_dvd {a : Nat} (ha0 : a ≠ 0) (h4 : 2 ^ 2 ∣ a) :
    2 ≤ v2 a := by
  rw [v2]
  exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num : (2 : Nat) ≠ 1) ha0).mp h4

lemma v2_two_pow_mul_of_odd (k : Nat) {m : Nat} (hm : Odd m) :
    v2 (2 ^ k * m) = k := by
  have hm0 : m ≠ 0 := by
    exact ne_of_gt (odd_nat_pos hm)
  rw [v2, padicValNat.mul]
  · rw [padicValNat.prime_pow]
    have hvm : padicValNat 2 m = 0 := by
      exact padicValNat.eq_zero_of_not_dvd hm.not_two_dvd_nat
    omega
  · exact pow_ne_zero k (by norm_num : (2 : Nat) ≠ 0)
  · exact hm0

lemma even_two_pow_mul_nat (j m : Nat) : Even (2 ^ (j + 1) * m) := by
  refine ⟨2 ^ j * m, ?_⟩
  rw [pow_succ']
  ring

lemma odd_two_pow_mul_sub_one (j : Nat) {m : Nat} (hm : Odd m) :
    Odd (2 ^ (j + 1) * m - 1) := by
  have hmpos : 0 < m := odd_nat_pos hm
  have hEven : Even (2 ^ (j + 1) * m) := even_two_pow_mul_nat j m
  have hle : 1 ≤ 2 ^ (j + 1) * m := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by norm_num) _) hmpos)
  rw [Nat.odd_sub hle]
  constructor
  · intro hOddA
    exact False.elim ((Nat.not_odd_iff_even.mpr hEven) hOddA)
  · intro hEvenOne
    exact False.elim (Nat.not_even_one hEvenOne)

lemma odd_two_pow_mul_add_one (j m : Nat) :
    Odd (2 ^ (j + 1) * m + 1) := by
  exact (even_two_pow_mul_nat j m).add_one

lemma v2_left_leg_pred_shift (j : Nat) {m : Nat} (hm : Odd m) :
    v2 (((2 ^ (j + 2) * m - 1) - 1)) = 1 := by
  have hmpos : 0 < m := odd_nat_pos hm
  have hEq : (2 ^ (j + 2) * m - 1) - 1 = 2 * (2 ^ (j + 1) * m - 1) := by
    have hpow : 2 ^ (j + 2) * m = 2 * (2 ^ (j + 1) * m) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    have hle : 1 ≤ 2 ^ (j + 1) * m := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by norm_num) _) hmpos)
    omega
  let q := 2 ^ (j + 1) * m - 1
  have hqne : q ≠ 0 := by
    have hodd : Odd q := by
      simpa [q] using odd_two_pow_mul_sub_one j hm
    rcases hodd with ⟨a, ha⟩
    omega
  rw [hEq, v2]
  change padicValNat 2 (2 * q) = 1
  rw [padicValNat.mul (by norm_num : (2 : Nat) ≠ 0) hqne]
  rw [padicValNat.self (by norm_num : 1 < 2)]
  have hq : padicValNat 2 q = 0 := by
    exact padicValNat.eq_zero_of_not_dvd
      (by simpa [q] using (odd_two_pow_mul_sub_one j hm).not_two_dvd_nat)
  omega

lemma v2_left_leg_succ_shift (j : Nat) {m : Nat} (hm : Odd m) :
    v2 (((2 ^ (j + 2) * m - 1) + 1)) = j + 2 := by
  have hmpos : 0 < m := odd_nat_pos hm
  have hEq : (2 ^ (j + 2) * m - 1) + 1 = 2 ^ (j + 2) * m := by
    have hle : 1 ≤ 2 ^ (j + 2) * m := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by norm_num) _) hmpos)
    omega
  rw [hEq]
  exact v2_two_pow_mul_of_odd (j + 2) hm

lemma v2_right_leg_pred_shift (j : Nat) {m : Nat} (hm : Odd m) :
    v2 (((2 ^ (j + 2) * m + 1) - 1)) = j + 2 := by
  have hEq : (2 ^ (j + 2) * m + 1) - 1 = 2 ^ (j + 2) * m := by
    omega
  rw [hEq]
  exact v2_two_pow_mul_of_odd (j + 2) hm

lemma v2_right_leg_succ_shift (j m : Nat) :
    v2 (((2 ^ (j + 2) * m + 1) + 1)) = 1 := by
  have hEq : (2 ^ (j + 2) * m + 1) + 1 = 2 * (2 ^ (j + 1) * m + 1) := by
    have hpow : 2 ^ (j + 2) * m = 2 * (2 ^ (j + 1) * m) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    ring
  let q := 2 ^ (j + 1) * m + 1
  have hqne : q ≠ 0 := by
    have hodd : Odd q := by
      simpa [q] using odd_two_pow_mul_add_one j m
    rcases hodd with ⟨a, ha⟩
    omega
  rw [hEq, v2]
  change padicValNat 2 (2 * q) = 1
  rw [padicValNat.mul (by norm_num : (2 : Nat) ≠ 0) hqne]
  rw [padicValNat.self (by norm_num : 1 < 2)]
  have hq : padicValNat 2 q = 0 := by
    exact padicValNat.eq_zero_of_not_dvd
      (by simpa [q] using (odd_two_pow_mul_add_one j m).not_two_dvd_nat)
  omega

/-- K.5, left leg, written with the shifted depth `j + 2`. -/
theorem keff_left_leg_shift (j : Nat) {m : Nat} (hm : Odd m) :
    keff (2 ^ (j + 2) * m - 1) = j + 2 := by
  unfold keff
  rw [v2_left_leg_pred_shift j hm, v2_left_leg_succ_shift j hm]
  exact max_eq_right (by omega)

/-- K.5, right leg, written with the shifted depth `j + 2`. -/
theorem keff_right_leg_shift (j : Nat) {m : Nat} (hm : Odd m) :
    keff (2 ^ (j + 2) * m + 1) = j + 2 := by
  unfold keff
  rw [v2_right_leg_pred_shift j hm, v2_right_leg_succ_shift j m]
  exact max_eq_left (by omega)

/-- K.5, left leg: a bracket centered at `2^k * m` gives effective depth `k`. -/
theorem keff_left_leg (k m : Nat) (hk : 2 ≤ k) (hm : Odd m) :
    keff (2 ^ k * m - 1) = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using keff_left_leg_shift j hm

/-- K.5, right leg: a bracket centered at `2^k * m` gives effective depth `k`. -/
theorem keff_right_leg (k m : Nat) (hk : 2 ≤ k) (hm : Odd m) :
    keff (2 ^ k * m + 1) = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using keff_right_leg_shift j hm

/-- Existence half of K.5: every odd `n ≥ 3` is a leg at level `keff n`. -/
theorem bracket_bijection_odd_ge_three_exists (n : Nat) (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ k epsilon m, 2 ≤ k ∧ Odd m ∧ keff n = k ∧ n = natDescendant k epsilon m := by
  rcases hn with ⟨a, rfl⟩
  by_cases ha : Even a
  · rcases ha with ⟨b, rfl⟩
    let k := v2 ((2 * (b + b) + 1) - 1)
    let m := ((2 * (b + b) + 1) - 1).divMaxPow 2
    refine ⟨k, BranchSign.plus, m, ?_, ?_, ?_, ?_⟩
    · have hnonzero : (2 * (b + b) + 1) - 1 ≠ 0 := by omega
      have h4 : 2 ^ 2 ∣ (2 * (b + b) + 1) - 1 := by
        refine ⟨b, ?_⟩
        omega
      exact two_le_v2_of_four_dvd hnonzero h4
    · have hnonzero : (2 * (b + b) + 1) - 1 ≠ 0 := by omega
      exact odd_divMaxPow_two hnonzero
    · have hsucc : v2 ((2 * (b + b) + 1) + 1) = 1 := by
        have hOdd : Odd (b + b + 1) := by
          exact (show Even (b + b) from ⟨b, rfl⟩).add_one
        have hEq : (2 * (b + b) + 1) + 1 = 2 ^ 1 * (b + b + 1) := by
          ring
        rw [hEq]
        exact v2_two_pow_mul_of_odd 1 hOdd
      unfold keff k
      rw [hsucc]
      exact max_eq_left (by
        have hnonzero : (2 * (b + b) + 1) - 1 ≠ 0 := by omega
        have h4 : 2 ^ 2 ∣ (2 * (b + b) + 1) - 1 := by
          refine ⟨b, ?_⟩
          omega
        have hk : 2 ≤ v2 ((2 * (b + b) + 1) - 1) :=
          two_le_v2_of_four_dvd hnonzero h4
        omega)
    · have hfac : 2 ^ k * m = (2 * (b + b) + 1) - 1 := by
        simpa [k, m, v2] using
          Nat.pow_padicValNat_mul_divMaxPow 2 ((2 * (b + b) + 1) - 1)
      change 2 * (b + b) + 1 = 2 ^ k * m + 1
      omega
  · have haOdd : Odd a := Nat.not_even_iff_odd.mp ha
    rcases haOdd with ⟨b, rfl⟩
    let k := v2 ((2 * (2 * b + 1) + 1) + 1)
    let m := ((2 * (2 * b + 1) + 1) + 1).divMaxPow 2
    refine ⟨k, BranchSign.minus, m, ?_, ?_, ?_, ?_⟩
    · have hnonzero : (2 * (2 * b + 1) + 1) + 1 ≠ 0 := by omega
      have h4 : 2 ^ 2 ∣ (2 * (2 * b + 1) + 1) + 1 := by
        refine ⟨b + 1, ?_⟩
        omega
      exact two_le_v2_of_four_dvd hnonzero h4
    · have hnonzero : (2 * (2 * b + 1) + 1) + 1 ≠ 0 := by omega
      exact odd_divMaxPow_two hnonzero
    · have hpred : v2 ((2 * (2 * b + 1) + 1) - 1) = 1 := by
        have hOdd : Odd (2 * b + 1) := ⟨b, rfl⟩
        have hEq : (2 * (2 * b + 1) + 1) - 1 = 2 ^ 1 * (2 * b + 1) := by
          omega
        rw [hEq]
        exact v2_two_pow_mul_of_odd 1 hOdd
      unfold keff k
      rw [hpred]
      exact max_eq_right (by
        have hnonzero : (2 * (2 * b + 1) + 1) + 1 ≠ 0 := by omega
        have h4 : 2 ^ 2 ∣ (2 * (2 * b + 1) + 1) + 1 := by
          refine ⟨b + 1, ?_⟩
          omega
        have hk : 2 ≤ v2 ((2 * (2 * b + 1) + 1) + 1) :=
          two_le_v2_of_four_dvd hnonzero h4
        omega)
    · have hfac : 2 ^ k * m = (2 * (2 * b + 1) + 1) + 1 := by
        simp [k, m, v2]
      change 2 * (2 * b + 1) + 1 = 2 ^ k * m - 1
      omega

lemma pow_two_ne_zero (k : Nat) : (2 : Int) ^ k ≠ 0 := by
  exact pow_ne_zero k (by norm_num)

lemma four_mul_form (d : Nat) : (2 : Int) ^ (d + 2) = 4 * (2 : Int) ^ d := by
  calc
    (2 : Int) ^ (d + 2) = (2 : Int) ^ d * (2 : Int) ^ 2 := by
      rw [pow_add]
    _ = (2 : Int) ^ d * 4 := by norm_num
    _ = 4 * (2 : Int) ^ d := by ring

lemma even_two_pow_mul (d : Nat) (m : Int) : Even ((2 : Int) ^ (d + 1) * m) := by
  refine ⟨(2 : Int) ^ d * m, ?_⟩
  rw [pow_succ']
  ring

lemma odd_not_even {m : Int} (hm : Odd m) : ¬ Even m := by
  rintro ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  omega

lemma same_depth_same_sign_injective {k : Nat} {m m' : Int} {epsilon : BranchSign}
    (h : descendant k epsilon m = descendant k epsilon m') :
    m = m' := by
  have hMul : (2 : Int) ^ k * m = (2 : Int) ^ k * m' := by
    cases epsilon <;> simpa [descendant] using h
  exact mul_left_cancel₀ (pow_two_ne_zero k) hMul

lemma same_depth_opposite_sign_ne {k : Nat} (hk : 2 <= k) {m m' : Int} :
    descendant k BranchSign.minus m ≠ descendant k BranchSign.plus m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hDesc :
      (2 : Int) ^ (2 + d) * m + -1 = (2 : Int) ^ (2 + d) * m' + 1 := by
    simpa [descendant] using h
  have hEq' : (2 : Int) ^ (d + 2) * (m - m') = 2 := by
    have h' := congrArg (fun z => z + 1 - ((2 : Int) ^ (2 + d) * m')) hDesc
    calc
      (2 : Int) ^ (d + 2) * (m - m') =
          (2 : Int) ^ (d + 2) * m - (2 : Int) ^ (d + 2) * m' := by
        ring
      _ = 2 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  have hDivPow : (4 : Int) ∣ (2 : Int) ^ (d + 2) := by
    refine ⟨(2 : Int) ^ d, ?_⟩
    simpa [mul_comm] using four_mul_form d
  have hDivL : (4 : Int) ∣ (2 : Int) ^ (d + 2) * (m - m') :=
    dvd_mul_of_dvd_left hDivPow (m - m')
  have hDivR : (4 : Int) ∣ 2 := by
    rw [← hEq']
    exact hDivL
  norm_num at hDivR

lemma same_depth_address_unique {k : Nat} (hk : 2 <= k)
    {m m' : Int} {epsilon epsilon' : BranchSign}
    (h : descendant k epsilon m = descendant k epsilon' m') :
    epsilon = epsilon' ∧ m = m' := by
  cases epsilon <;> cases epsilon'
  · exact ⟨rfl, same_depth_same_sign_injective h⟩
  · exact (same_depth_opposite_sign_ne hk h).elim
  · exact (same_depth_opposite_sign_ne hk h.symm).elim
  · exact ⟨rfl, same_depth_same_sign_injective h⟩

lemma different_depth_same_sign_ne {k k' : Nat} (hkk' : k < k')
    {m m' : Int} (hm : Odd m) {epsilon : BranchSign} :
    descendant k epsilon m ≠ descendant k' epsilon m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  have hNoOffset : (2 : Int) ^ k * m = (2 : Int) ^ (k + (d + 1)) * m' := by
    cases epsilon <;> simpa [descendant] using h
  have hCore : m = (2 : Int) ^ (d + 1) * m' := by
    have hMul' : (2 : Int) ^ k * m = (2 : Int) ^ k * ((2 : Int) ^ (d + 1) * m') := by
      calc
        (2 : Int) ^ k * m = (2 : Int) ^ (k + (d + 1)) * m' := hNoOffset
        _ = (2 : Int) ^ k * ((2 : Int) ^ (d + 1) * m') := by
          rw [pow_add]
          ring
    exact mul_left_cancel₀ (pow_two_ne_zero k) hMul'
  have hmEven : Even m := by
    rw [hCore]
    exact even_two_pow_mul d m'
  exact odd_not_even hm hmEven

lemma different_depth_opposite_sign_ne {k k' : Nat} (hk : 2 <= k) (hkk' : k < k')
    {m m' : Int} {epsilon epsilon' : BranchSign} (hSign : epsilon ≠ epsilon') :
    descendant k epsilon m ≠ descendant k' epsilon' m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases epsilon <;> cases epsilon'
  · contradiction
  · have hEq : (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') = 2 := by
      have hDesc :
          (2 : Int) ^ (2 + e) * m + -1 =
            (2 : Int) ^ (2 + e + d + 1) * m' + 1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z + 1 - ((2 : Int) ^ (2 + e + d + 1) * m')) hDesc
      calc
        (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') =
            (2 : Int) ^ (e + 2) * m - (2 : Int) ^ (e + 2 + (d + 1)) * m' := by
          rw [mul_sub, pow_add]
          ring
        _ = 2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : Int) ∣ (2 : Int) ^ (e + 2) := by
      refine ⟨(2 : Int) ^ e, ?_⟩
      simpa [mul_comm] using four_mul_form e
    have hDivL : (4 : Int) ∣ (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : Int) ^ (d + 1) * m')
    have hDivR : (4 : Int) ∣ 2 := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · have hEq : (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') = -2 := by
      have hDesc :
          (2 : Int) ^ (2 + e) * m + 1 =
            (2 : Int) ^ (2 + e + d + 1) * m' + -1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z - 1 - ((2 : Int) ^ (2 + e + d + 1) * m')) hDesc
      calc
        (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') =
            (2 : Int) ^ (e + 2) * m - (2 : Int) ^ (e + 2 + (d + 1)) * m' := by
          rw [mul_sub, pow_add]
          ring
        _ = -2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : Int) ∣ (2 : Int) ^ (e + 2) := by
      refine ⟨(2 : Int) ^ e, ?_⟩
      simpa [mul_comm] using four_mul_form e
    have hDivL : (4 : Int) ∣ (2 : Int) ^ (e + 2) * (m - (2 : Int) ^ (d + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : Int) ^ (d + 1) * m')
    have hDivR : (4 : Int) ∣ (-2 : Int) := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · contradiction

/--
Address uniqueness for the C2 branches.  This is the combinatorial spine behind the
`keff`/bracket bijection; the later `keff` theorem will identify this address with the valuation
definition.
-/
theorem descendant_address_unique {k k' : Nat} (hk : 2 <= k) (hk' : 2 <= k')
    {m m' : Int} (hm : Odd m) (hm' : Odd m') {epsilon epsilon' : BranchSign}
    (h : descendant k epsilon m = descendant k' epsilon' m') :
    k = k' ∧ epsilon = epsilon' ∧ m = m' := by
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · exfalso
    by_cases hSign : epsilon = epsilon'
    · exact different_depth_same_sign_ne hlt hm (hSign ▸ h)
    · exact different_depth_opposite_sign_ne hk hlt hSign h
  · rcases same_depth_address_unique hk h with ⟨hEps, hmEq⟩
    exact ⟨rfl, hEps, hmEq⟩
  · exfalso
    by_cases hSign : epsilon = epsilon'
    · exact different_depth_same_sign_ne hgt hm' (hSign ▸ h.symm)
    · have hSign' : epsilon' ≠ epsilon := by simpa [eq_comm] using hSign
      exact different_depth_opposite_sign_ne hk' hgt hSign' h.symm

/-- Natural-address uniqueness for C2 brackets. -/
theorem natDescendant_address_unique {k k' : Nat} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {m m' : Nat} (hm : Odd m) (hm' : Odd m') {epsilon epsilon' : BranchSign}
    (h : natDescendant k epsilon m = natDescendant k' epsilon' m') :
    k = k' ∧ epsilon = epsilon' ∧ m = m' := by
  have hInt : descendant k epsilon (m : Int) = descendant k' epsilon' (m' : Int) := by
    rw [← natDescendant_cast hm, ← natDescendant_cast hm']
    exact_mod_cast h
  rcases descendant_address_unique hk hk' (odd_natCast_int hm) (odd_natCast_int hm') hInt with
    ⟨hkEq, heps, hmInt⟩
  refine ⟨hkEq, heps, ?_⟩
  exact_mod_cast hmInt

/--
K.5 as a bijection statement: every odd `n ≥ 3` has one and only one C2 bracket address.
The returned level is exactly `keff n`.
-/
theorem bracket_bijection_odd_ge_three (n : Nat) (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ k epsilon m,
      2 ≤ k ∧ Odd m ∧ keff n = k ∧ n = natDescendant k epsilon m ∧
        ∀ k' epsilon' m',
          2 ≤ k' →
          Odd m' →
          keff n = k' →
          n = natDescendant k' epsilon' m' →
          k' = k ∧ epsilon' = epsilon ∧ m' = m := by
  rcases bracket_bijection_odd_ge_three_exists n hn h3 with
    ⟨k, epsilon, m, hk, hm, hkEff, hnAddr⟩
  refine ⟨k, epsilon, m, hk, hm, hkEff, hnAddr, ?_⟩
  intro k' epsilon' m' hk' hm' _hkEff' hnAddr'
  have hAddr : natDescendant k epsilon m = natDescendant k' epsilon' m' := by
    rw [← hnAddr, ← hnAddr']
  rcases natDescendant_address_unique hk hk' hm hm' hAddr with ⟨hkEq, heps, hmEq⟩
  exact ⟨hkEq.symm, heps.symm, hmEq.symm⟩

/-- Dyadic C2 weight `2^{-k}`, represented rationally as `(2^k)⁻¹`. -/
def dyadicWeight (k : Nat) : ℚ :=
  ((2 : ℚ) ^ k)⁻¹

/-- Direct leg weight used by the `D` side. -/
def directLegWeight (n : Nat) : ℚ :=
  dyadicWeight (keff n)

/-- A valid bracket address whose leg is `n`. -/
def IsC2LegAddress (n k : Nat) (epsilon : BranchSign) (m : Nat) : Prop :=
  2 ≤ k ∧ Odd m ∧ n = natDescendant k epsilon m

lemma isC2LegAddress.keff_eq {n k : Nat} {epsilon : BranchSign} {m : Nat}
    (h : IsC2LegAddress n k epsilon m) :
    keff n = k := by
  rcases h with ⟨hk, hm, hnAddr⟩
  cases epsilon
  · rw [hnAddr]
    exact keff_left_leg k m hk hm
  · rw [hnAddr]
    exact keff_right_leg k m hk hm

/-- Local Halving Law: an addressed bracket leg carries exactly the direct `keff` weight. -/
theorem halving_law_of_address {n k : Nat} {epsilon : BranchSign} {m : Nat}
    (h : IsC2LegAddress n k epsilon m) :
    directLegWeight n = dyadicWeight k := by
  unfold directLegWeight
  rw [isC2LegAddress.keff_eq h]

/-- Halving Law: every odd `n ≥ 3` has one unique bracket address and matching weight. -/
theorem halving_law_odd_ge_three (n : Nat) (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ k epsilon m,
      IsC2LegAddress n k epsilon m ∧
        directLegWeight n = dyadicWeight k ∧
          ∀ k' epsilon' m',
            IsC2LegAddress n k' epsilon' m' →
              k' = k ∧ epsilon' = epsilon ∧ m' = m := by
  rcases bracket_bijection_odd_ge_three_exists n hn h3 with
    ⟨k, epsilon, m, hk, hm, hkEff, hnAddr⟩
  have hAddr : IsC2LegAddress n k epsilon m := ⟨hk, hm, hnAddr⟩
  refine ⟨k, epsilon, m, hAddr, ?_, ?_⟩
  · unfold directLegWeight
    rw [hkEff]
  · intro k' epsilon' m' hAddr'
    rcases hAddr' with ⟨hk', hm', hnAddr'⟩
    have hEq : natDescendant k epsilon m = natDescendant k' epsilon' m' := by
      rw [← hnAddr, ← hnAddr']
    rcases natDescendant_address_unique hk hk' hm hm' hEq with ⟨hkEq, heps, hmEq⟩
    exact ⟨hkEq.symm, heps.symm, hmEq.symm⟩

end C2
