import SphericalTreeFailures.StrictCharacteristic
import SphericalTreeFailures.CharacteristicRecursion

namespace SphericalTreeFailures
open Polynomial

theorem square_coeff_one (p : ℕ[X]) : (p ^ 2).coeff 1 = 2 * p.coeff 0 * p.coeff 1 := by
  rw [pow_two, coeff_mul]
  have h : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  rw [h]
  simp
  ring

theorem conditionalPolynomials_low_coefficients (m k : ℕ) :
    (conditionalPolynomials m k).1.coeff 0 = 1 ∧
    (conditionalPolynomials m k).2.coeff 0 = 0 ∧
    (conditionalPolynomials m k).2.coeff 1 = 1 ∧
    0 < (conditionalPolynomials m k).1.coeff 1 := by
  induction m with
  | zero =>
    simp [conditionalPolynomials, coeff_X_mul, pathPolynomial_coeff]
  | succ m ih =>
    simp only [conditionalPolynomials]
    have h0 : ((conditionalPolynomials m k).1 + (conditionalPolynomials m k).2).coeff 0 = 1 := by
      simp [ih.1, ih.2.1]
    have h1 : 0 < ((conditionalPolynomials m k).1 + (conditionalPolynomials m k).2).coeff 1 := by
      simp only [coeff_add, ih.2.2.1]
      omega
    constructor
    · simp [pow_two, h0]
    constructor
    · simp
    constructor
    · simp [coeff_X_mul, pow_two, ih.1]
    · rw [square_coeff_one, h0]
      omega

theorem present_coeff_two_pos (m : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    0 < (conditionalPolynomials m k).2.coeff 2 := by
  cases m with
  | zero =>
    simp [conditionalPolynomials, coeff_X_mul, pathPolynomial_coeff]
    omega
  | succ m =>
    change 0 < (X * (conditionalPolynomials m k).1 ^ 2).coeff (1 + 1)
    rw [coeff_X_mul, square_coeff_one, (conditionalPolynomials_low_coefficients m k).1]
    have h := (conditionalPolynomials_low_coefficients m k).2.2.2
    omega

theorem conditionalCharacteristic_lattice {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ)
    {t : ℝ} (ht0 : 0 < |t|) (ht : |t| ≤ Real.pi) :
    ‖absentCharacteristic m k (tunedActivity r) t‖ < 1 ∧
    ‖presentCharacteristic m k (tunedActivity r) t‖ < 1 := by
  have ha := tunedActivity_pos hr
  have hp := excludedPartition_pos m (2 * k + 1) ha
  have hb : includedPartition 0 (2 * k + 1) (tunedActivity r) =
      r * excludedPartition 0 (2 * k + 1) (tunedActivity r) := by
    rw [includedPartition_zero_succ, excludedPartition_zero]
    exact htune
  have hi := tuned_partition_ratio (2 * k + 1) (tunedActivity r) r rfl hb m
  obtain ⟨hc0, _, hc1, hc01⟩ := conditionalPolynomials_low_coefficients m k
  constructor
  · exact polynomialCharacteristic_norm_lt_one _ ha
      (by rw [conditionalPolynomials_excluded]; exact hp) t
      (by rw [hc0]; decide) hc01 (unit_exponential_ne_one ht0 ht)
  · exact polynomialCharacteristic_norm_lt_one _ ha
      (by rw [conditionalPolynomials_included, hi]; exact mul_pos hr hp) t
      (by rw [hc1]; decide) (present_coeff_two_pos m hk) (unit_exponential_ne_one ht0 ht)

end SphericalTreeFailures
