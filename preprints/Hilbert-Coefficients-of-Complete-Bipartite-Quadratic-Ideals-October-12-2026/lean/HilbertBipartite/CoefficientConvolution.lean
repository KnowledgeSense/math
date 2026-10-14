import HilbertBipartite.Signs

open Finset Polynomial

namespace HilbertBipartite

@[simp] theorem weightedCoeff_zero_degree (P : Polynomial ℚ) (i : ℕ) :
    weightedCoeff P i 0 = P.coeff 0 := by
  simp [weightedCoeff]

@[simp] theorem weightedCoeff_one (i r : ℕ) :
    weightedCoeff 1 i r = 2^r * ((r+i).choose i : ℚ) := by
  classical
  simp [weightedCoeff, Polynomial.coeff_one, Finset.sum_ite_eq']

@[simp] theorem weightedCoeff_X_mul_zero (P : Polynomial ℚ) (i : ℕ) :
    weightedCoeff (X*P) i 0 = 0 := by simp

theorem weightedCoeff_X_mul_succ (P : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff (X*P) i (r+1) = weightedCoeff P i r := by
  unfold weightedCoeff
  rw [Finset.sum_range_succ']
  simp only [coeff_X_mul_zero, zero_mul, add_zero, coeff_X_mul, Nat.add_sub_add_right]

theorem weightedCoeff_pascal (P : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff P (i+1) (r+1) - 2 * weightedCoeff P (i+1) r =
      weightedCoeff P i (r+1) := by
  unfold weightedCoeff
  conv_lhs => lhs; rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ]
  rw [Finset.mul_sum]
  have h : ∀ j ∈ range (r+1),
      P.coeff j * 2^(r+1-j) * ((r+1-j+(i+1)).choose (i+1) : ℚ) -
      2 * (P.coeff j * 2^(r-j) * ((r-j+(i+1)).choose (i+1) : ℚ)) =
      P.coeff j * 2^(r+1-j) * ((r+1-j+i).choose i : ℚ) := by
    intro j hj
    have hjr : j ≤ r := by simpa using (Nat.le_of_lt_succ (mem_range.mp hj))
    have he : r+1-j = r-j+1 := by omega
    rw [he]
    rw [show r-j+1+(i+1) = (r-j+(i+1))+1 by omega, Nat.choose_succ_succ]
    push_cast
    simp only [Nat.succ_eq_add_one]
    rw [pow_succ]
    ring
  have hh := Finset.sum_congr rfl h
  rw [Finset.sum_sub_distrib] at hh
  simp only [Nat.sub_self, zero_add, pow_zero, mul_one, Nat.choose_self, Nat.cast_one] at *
  linarith

theorem weightedCoeff_cancel (P : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff ((1-C 2*X)*P) (i+1) r = weightedCoeff P i r := by
  rw [sub_mul, one_mul, weightedCoeff_sub]
  rw [mul_assoc, weightedCoeff_C_mul]
  cases r with
  | zero => simp
  | succ r =>
    rw [weightedCoeff_X_mul_succ]
    exact weightedCoeff_pascal P i r

theorem weightedCoeff_cancel_pow (c i r : ℕ) (hc : c ≤ i) :
    weightedCoeff ((1-C 2*X)^c) i r =
      2^r * ((r+i-c).choose r : ℚ) := by
  induction c generalizing i with
  | zero =>
    simp only [pow_zero, weightedCoeff_one, Nat.sub_zero]
    rw [Nat.choose_symm_add]
  | succ c ih =>
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [pow_succ', weightedCoeff_cancel, ih i (by omega)]
    congr 3
    omega

end HilbertBipartite
