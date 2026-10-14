import SphericalTreeFailures.PathReversal
import Mathlib.Algebra.Polynomial.Derivative

namespace SphericalTreeFailures
open Polynomial

noncomputable def eulerPolynomial (p : ℕ[X]) : ℕ[X] := X * derivative p

theorem eulerPolynomial_coeff (p : ℕ[X]) (j : ℕ) :
    (eulerPolynomial p).coeff j = p.coeff j * j := by
  cases j with
  | zero => simp [eulerPolynomial]
  | succ j => simp [eulerPolynomial, coeff_X_mul, coeff_derivative]

theorem eulerPolynomial_natDegree_le (p : ℕ[X]) :
    (eulerPolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [eulerPolynomial_coeff, coeff_eq_zero_of_natDegree_lt hj, zero_mul]

/-- Euler differentiation splits the degree into size and reversed deficit. -/
theorem euler_reflection_identity (p : ℕ[X]) {N : ℕ} (hp : p.natDegree ≤ N) :
    C N * p = eulerPolynomial p + reflect N (eulerPolynomial (reflect N p)) := by
  ext j
  rw [coeff_C_mul, coeff_add, eulerPolynomial_coeff, coeff_reflect, eulerPolynomial_coeff,
    coeff_reflect, revAt_invol]
  by_cases hj : j ≤ N
  · rw [revAt_le hj]
    rw [← Nat.mul_add, Nat.add_sub_of_le hj, Nat.mul_comm]
  · have hz : p.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hz]

noncomputable def polynomialMean (p : ℕ[X]) (activity : ℝ) : ℝ :=
  (eulerPolynomial p).eval₂ (Nat.castRingHom ℝ) activity /
    p.eval₂ (Nat.castRingHom ℝ) activity

theorem polynomialMean_reflection (p : ℕ[X]) {N : ℕ} (hp : p.natDegree ≤ N)
    {activity : ℝ} (ha : 0 < activity)
    (hpos : 0 < p.eval₂ (Nat.castRingHom ℝ) activity) :
    polynomialMean p activity = (N : ℝ) - polynomialMean (reflect N p) (1 / activity) := by
  let _ := invertibleOfNonzero (ne_of_gt ha)
  have hR := eval₂_reflect_mul_pow (Nat.castRingHom ℝ) activity N p hp
  rw [invOf_eq_inv] at hR
  have hd : (reflect N p).natDegree ≤ N := by
    exact natDegree_reflect_le.trans (max_le le_rfl hp)
  have hdq := (eulerPolynomial_natDegree_le (reflect N p)).trans hd
  have hdqq : (reflect N (eulerPolynomial (reflect N p))).natDegree ≤ N :=
    natDegree_reflect_le.trans (max_le le_rfl hdq)
  have hq := eval₂_reflect_mul_pow (Nat.castRingHom ℝ) activity N
    (reflect N (eulerPolynomial (reflect N p))) hdqq
  rw [invOf_eq_inv, reflect_reflect] at hq
  have he := congrArg (fun q : ℕ[X] => q.eval₂ (Nat.castRingHom ℝ) activity)
    (euler_reflection_identity p hp)
  simp only [eval₂_mul, eval₂_C, eval₂_add] at he
  rw [← hq] at he
  have hRn : (reflect N p).eval₂ (Nat.castRingHom ℝ) activity⁻¹ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hR
    exact (ne_of_gt hpos) hR.symm
  unfold polynomialMean
  simp only [one_div]
  rw [← hR]
  change (eulerPolynomial p).eval₂ (Nat.castRingHom ℝ) activity /
      ((reflect N p).eval₂ (Nat.castRingHom ℝ) activity⁻¹ * activity ^ N) =
    (N : ℝ) - (eulerPolynomial (reflect N p)).eval₂ (Nat.castRingHom ℝ) activity⁻¹ /
      (reflect N p).eval₂ (Nat.castRingHom ℝ) activity⁻¹
  change (N : ℝ) * p.eval₂ (Nat.castRingHom ℝ) activity = _ at he
  rw [← hR] at he
  have halg (A B S P c : ℝ) (hS : S ≠ 0) (hP : P ≠ 0)
      (h : c * (S * P) = A + B * P) : A / (S * P) = c - B / S := by
    field_simp
    nlinarith
  exact halg _ _ _ _ _ hRn (pow_ne_zero _ (ne_of_gt ha)) he

end SphericalTreeFailures
