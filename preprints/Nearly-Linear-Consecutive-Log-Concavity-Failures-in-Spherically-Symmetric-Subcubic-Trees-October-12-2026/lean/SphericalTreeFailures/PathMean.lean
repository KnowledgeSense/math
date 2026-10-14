import SphericalTreeFailures.EulerReflection
import SphericalTreeFailures.TailMoments
import SphericalTreeFailures.TunedRootProbability

namespace SphericalTreeFailures
open Finset Polynomial

noncomputable def pathMean (n : ℕ) (activity : ℝ) : ℝ := polynomialMean (pathPolynomial n) activity

theorem eulerPolynomial_eval_sum (p : ℕ[X]) {N : ℕ} (hp : p.natDegree < N) (y : ℝ) :
    (eulerPolynomial p).eval₂ (Nat.castRingHom ℝ) y =
      ∑ j ∈ range N, (j : ℝ) * (p.coeff j : ℝ) * y ^ j := by
  rw [eval₂_eq_sum_range' _ ((eulerPolynomial_natDegree_le p).trans_lt hp)]
  apply sum_congr rfl
  intro j hj
  rw [eulerPolynomial_coeff]
  change ((p.coeff j * j : ℕ) : ℝ) * y ^ j = _
  push_cast
  ring

theorem oddReverse_polynomialMean (k : ℕ) (y : ℝ) :
    polynomialMean (reflect (k + 1) (pathPolynomial (2 * k + 1))) y = oddDeficit k y := by
  have hd : (reflect (k + 1) (pathPolynomial (2 * k + 1))).natDegree < k + 2 :=
    (natDegree_reflect_le.trans (max_le le_rfl (oddPath_natDegree_le k))).trans_lt (by omega)
  unfold polynomialMean
  rw [eulerPolynomial_eval_sum _ hd, oddReverseSum_eval]
  simp only [oddPath_reflect_coeff, oddDeficit, oddReverseCoefficient]

theorem evenReverse_polynomialMean (k : ℕ) (y : ℝ) :
    polynomialMean (reflect k (pathPolynomial (2 * k))) y = evenDeficit k y := by
  have hd : (reflect k (pathPolynomial (2 * k))).natDegree < k + 1 :=
    (natDegree_reflect_le.trans (max_le le_rfl (evenPath_natDegree_le k))).trans_lt (by omega)
  unfold polynomialMean
  rw [eulerPolynomial_eval_sum _ hd, evenReverseSum_eval]
  simp only [evenPath_reflect_coeff]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hs : ∑ j ∈ range (k + 1), (j : ℝ) *
      (Nat.choose (k + 1 + j) (2 * j + 1) : ℝ) * y ^ j =
      (k + 1) * ∑ j ∈ range (k + 1), (j : ℝ) * evenReverseCoefficient k j * y ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    unfold evenReverseCoefficient
    field_simp
  rw [hs, mul_div_mul_left _ _ hk]
  rfl

theorem pathMean_odd (k : ℕ) {activity : ℝ} (ha : 0 < activity) :
    pathMean (2 * k + 1) activity = (k + 1 : ℝ) - oddDeficit k (1 / activity) := by
  unfold pathMean
  rw [polynomialMean_reflection _ (oddPath_natDegree_le k) ha]
  · rw [oddReverse_polynomialMean]
    push_cast
    rfl
  · exact pathPartition_pos _ ha

theorem pathMean_even (k : ℕ) {activity : ℝ} (ha : 0 < activity) :
    pathMean (2 * k) activity = (k : ℝ) - evenDeficit k (1 / activity) := by
  unfold pathMean
  rw [polynomialMean_reflection _ (evenPath_natDegree_le k) ha]
  · rw [evenReverse_polynomialMean]
  · exact pathPartition_pos _ ha

end SphericalTreeFailures
