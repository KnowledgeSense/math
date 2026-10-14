import SphericalTreeFailures.PathReversal
import SphericalTreeFailures.FiniteExponentialBounds

namespace SphericalTreeFailures
open Finset Polynomial

noncomputable def oddReverseSum (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (k + 2), oddReverseCoefficient k j * y ^ j
noncomputable def evenReverseSum (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), evenReverseCoefficient k j * y ^ j

noncomputable def pathPartition (n : ℕ) (activity : ℝ) : ℝ :=
  (pathPolynomial n).eval₂ (Nat.castRingHom ℝ) activity

theorem oddReverseSum_lower (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ oddReverseSum k y := by
  have h := single_le_sum (f := fun j => oddReverseCoefficient k j * y ^ j)
    (s := range (k + 2)) (a := 0)
    (fun j hj => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hy j)) (by simp)
  simpa [oddReverseSum] using h

theorem evenReverseSum_lower (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ evenReverseSum k y := by
  have h := single_le_sum (f := fun j => evenReverseCoefficient k j * y ^ j)
    (s := range (k + 1)) (a := 0)
    (fun j hj => mul_nonneg (by unfold evenReverseCoefficient; positivity) (pow_nonneg hy j)) (by simp)
  simpa [evenReverseSum] using h

theorem oddReverseSum_upper (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    oddReverseSum k y ≤ Real.exp ((reverseScale k : ℝ) * y) :=
  finite_exponential_bound (Nat.cast_nonneg _) hy (oddReverseCoefficient_exponential_bound k) _

theorem evenReverseSum_upper (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    evenReverseSum k y ≤ Real.exp ((reverseScale k : ℝ) * y) :=
  finite_exponential_bound (Nat.cast_nonneg _) hy (evenReverseCoefficient_exponential_bound k) _

theorem oddReverseSum_eval (k : ℕ) (y : ℝ) :
    (reflect (k + 1) (pathPolynomial (2 * k + 1))).eval₂ (Nat.castRingHom ℝ) y =
      oddReverseSum k y := by
  have hd := natDegree_reflect_le (N := k + 1) (p := pathPolynomial (2 * k + 1))
  rw [max_eq_left (oddPath_natDegree_le k)] at hd
  rw [eval₂_eq_sum_range' _ (by omega : (reflect (k + 1) (pathPolynomial (2 * k + 1))).natDegree < k + 2)]
  simp only [oddReverseSum, oddPath_reflect_coeff, oddReverseCoefficient]
  rfl

theorem evenReverseSum_eval (k : ℕ) (y : ℝ) :
    (reflect k (pathPolynomial (2 * k))).eval₂ (Nat.castRingHom ℝ) y =
      (k + 1) * evenReverseSum k y := by
  have hd := natDegree_reflect_le (N := k) (p := pathPolynomial (2 * k))
  rw [max_eq_left (evenPath_natDegree_le k)] at hd
  rw [eval₂_eq_sum_range' _ (by omega : (reflect k (pathPolynomial (2 * k))).natDegree < k + 1)]
  simp only [evenReverseSum, evenPath_reflect_coeff, evenReverseCoefficient, mul_sum]
  apply sum_congr rfl
  intro j hj
  change (Nat.choose (k + 1 + j) (2 * j + 1) : ℝ) * y ^ j =
    (k + 1) * ((Nat.choose (k + 1 + j) (2 * j + 1) : ℝ) / (k + 1) * y ^ j)
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem odd_path_reversal (k : ℕ) {activity : ℝ} (ha : 0 < activity) :
    pathPartition (2 * k + 1) activity = activity ^ (k + 1) * oddReverseSum k (1 / activity) := by
  let _ := invertibleOfNonzero (ne_of_gt ha)
  have h := eval₂_reflect_mul_pow (Nat.castRingHom ℝ) activity (k + 1)
    (pathPolynomial (2 * k + 1)) (oddPath_natDegree_le k)
  rw [invOf_eq_inv, oddReverseSum_eval] at h
  simpa [pathPartition, one_div, mul_comm] using h.symm

theorem even_path_reversal (k : ℕ) {activity : ℝ} (ha : 0 < activity) :
    pathPartition (2 * k) activity =
      (k + 1) * activity ^ k * evenReverseSum k (1 / activity) := by
  let _ := invertibleOfNonzero (ne_of_gt ha)
  have h := eval₂_reflect_mul_pow (Nat.castRingHom ℝ) activity k
    (pathPolynomial (2 * k)) (evenPath_natDegree_le k)
  rw [invOf_eq_inv, evenReverseSum_eval] at h
  unfold pathPartition
  rw [← h]
  simp only [one_div]
  ring

end SphericalTreeFailures
