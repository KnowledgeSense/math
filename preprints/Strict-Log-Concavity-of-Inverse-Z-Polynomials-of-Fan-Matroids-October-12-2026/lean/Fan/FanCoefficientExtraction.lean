import Fan.FanLagrangeSubstitution

namespace Fan
open PowerSeries Finset
variable {R : Type*} [CommRing R]

theorem fanLagrangePolynomial_pow (t : R) (n : ℕ) :
    fanLagrangePolynomial t ^ n =
      ∑ r ∈ range (n+1), C ((n.choose r : R) * t ^ r) * X ^ (2*r) := by
  rw [fanLagrangePolynomial, add_comm, add_pow]
  apply sum_congr rfl
  intro r _
  simp only [one_pow, mul_one, mul_pow, ← pow_mul, map_mul, map_pow, map_natCast]
  ring

theorem fanLagrangePolynomial_product_coeff (t : R) (f : PowerSeries R) (n N : ℕ) :
    coeff N (f * fanLagrangePolynomial t ^ n) =
      ∑ r ∈ range (n+1), if 2*r ≤ N then
        (n.choose r : R) * t^r * coeff (N-2*r) f else 0 := by
  rw [fanLagrangePolynomial_pow, mul_sum, map_sum]
  apply sum_congr rfl
  intro r _
  rw [show f * (C ((n.choose r : R)*t^r)*X^(2*r)) =
    C ((n.choose r : R)*t^r)*(X^(2*r)*f) by ring, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem fanLagrangePolynomial_derivative (t : R) :
    derivative (fanLagrangePolynomial t) = 2 * C t * X := by
  simp only [fanLagrangePolynomial, map_add, derivative_one, Derivation.leibniz,
    derivative_C, derivative_pow, derivative_X, smul_eq_mul]
  ring

theorem coeff_X_derivative (f : PowerSeries R) (N : ℕ) :
    coeff N (X * derivative f) = (N : R) * coeff N f := by
  cases N with
  | zero => simp
  | succ N => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

variable [NoZeroDivisors R] [CharZero R]

theorem fanLagrange_coeff_derivative (t : R) (f : PowerSeries R) (n : ℕ) :
    (n+1 : R) * coeff (n+1) (f.subst (fanLagrangeSeries t)) =
    coeff (n+1) ((X * derivative f) * fanLagrangePolynomial t ^ (n+1)) := by
  rw [fanLagrange_coeff_factored]
  let v := fanLagrangePolynomial t
  have hd := congrArg (coeff (n+1))
    (show X * derivative (f * v^(n+1)) =
      (X * derivative f)*v^(n+1) +
        (n+1 : R) • (2 * f * v^n * C t * X^2) by
      rw [Derivation.leibniz, derivative_pow]
      simp only [smul_eq_mul, Nat.add_sub_cancel, fanLagrangePolynomial_derivative, v]
      simp only [Algebra.smul_def, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
      ring)
  rw [coeff_X_derivative, map_add, map_smul] at hd
  simp only [smul_eq_mul] at hd
  have he : f*v^n*(1-C t*X^2) = f*v^(n+1) - 2*f*v^n*C t*X^2 := by
    rw [pow_succ]
    dsimp [v, fanLagrangePolynomial]
    ring
  change (n+1 : R) * coeff (n+1) (f*v^n*(1-C t*X^2)) = _
  rw [he, map_sub]
  push_cast at hd
  linear_combination hd

theorem fanLagrange_coeff_sum (t : R) (f : PowerSeries R) (N : ℕ) (hN : 0 < N) :
    (N : R) * coeff N (f.subst (fanLagrangeSeries t)) =
      ∑ r ∈ range (N+1), if 2*r < N then
        (N.choose r : R) * t^r * ((N-2*r : ℕ) : R) * coeff (N-2*r) f else 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [show (↑(n+1) : R) = n+1 by push_cast; rfl,
    fanLagrange_coeff_derivative, fanLagrangePolynomial_product_coeff]
  apply sum_congr rfl
  intro r _
  by_cases hr : 2*r < n+1
  · rw [ite_eq_left (by omega), ite_eq_left hr, coeff_X_derivative]
    ring
  · rw [ite_eq_right hr]
    by_cases he : 2*r ≤ n+1
    · rw [ite_eq_left he, show n+1-2*r = 0 by omega, coeff_X_derivative]
      simp
    · rw [ite_eq_right he]

end Fan
