import SphericalTreeFailures.ConditionalPolynomials
import SphericalTreeFailures.PolynomialCharacteristic

namespace SphericalTreeFailures

noncomputable def absentCharacteristic (m k : ℕ) (activity t : ℝ) : ℂ :=
  polynomialCharacteristic (conditionalPolynomials m k).1 activity t
noncomputable def presentCharacteristic (m k : ℕ) (activity t : ℝ) : ℂ :=
  polynomialCharacteristic (conditionalPolynomials m k).2 activity t
noncomputable def totalCharacteristic (m k : ℕ) (activity t : ℝ) : ℂ :=
  polynomialCharacteristic ((conditionalPolynomials m k).1 + (conditionalPolynomials m k).2) activity t

theorem absentCharacteristic_succ (m k : ℕ) (activity t : ℝ) :
    absentCharacteristic (m + 1) k activity t = totalCharacteristic m k activity t ^ 2 := by
  simp only [absentCharacteristic, conditionalPolynomials, polynomialCharacteristic_pow,
    totalCharacteristic]

theorem presentCharacteristic_succ (m k : ℕ) {activity : ℝ} (ha : 0 < activity) (t : ℝ) :
    presentCharacteristic (m + 1) k activity t =
      Complex.exp ((t : ℂ) * Complex.I) * absentCharacteristic m k activity t ^ 2 := by
  simp only [presentCharacteristic, conditionalPolynomials, polynomialCharacteristic_mul,
    polynomialCharacteristic_X ha, polynomialCharacteristic_pow, absentCharacteristic]

theorem tuned_characteristic_mixture (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    totalCharacteristic m k (tunedActivity r) t =
      ((1 - broadcastParameter r : ℝ) : ℂ) * absentCharacteristic m k (tunedActivity r) t +
      (broadcastParameter r : ℂ) * presentCharacteristic m k (tunedActivity r) t := by
  have hb : includedPartition 0 (2 * k + 1) (tunedActivity r) =
      r * excludedPartition 0 (2 * k + 1) (tunedActivity r) := by
    rw [includedPartition_zero_succ, excludedPartition_zero]
    exact htune
  have hi := tuned_partition_ratio (2 * k + 1) (tunedActivity r) r rfl hb m
  have hp := excludedPartition_pos m (2 * k + 1) (tunedActivity_pos hr)
  have h := polynomialCharacteristic_add_ratio (conditionalPolynomials m k).1
    (conditionalPolynomials m k).2 hr
    (by rw [conditionalPolynomials_excluded]; exact hp)
    (by rw [conditionalPolynomials_included, conditionalPolynomials_excluded]; exact hi) t
  have he : (1 / (1 + r) : ℝ) = 1 - broadcastParameter r := by
    unfold broadcastParameter
    have hd : 1 + r ≠ 0 := by positivity
    field_simp
    ring
  simpa only [he, totalCharacteristic, absentCharacteristic, presentCharacteristic,
    broadcastParameter] using h

theorem totalCharacteristic_graph (m k : ℕ) (activity t : ℝ) :
    totalCharacteristic m k activity t =
      polynomialCharacteristic (independencePolynomial (sphericalTree m (2 * k + 1)).graph Finset.univ)
        activity t := by
  unfold totalCharacteristic
  rw [conditionalPolynomials_total]

end SphericalTreeFailures
