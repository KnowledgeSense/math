import SphericalTreeFailures.TuningEstimates
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace SphericalTreeFailures

noncomputable def tuningFunction (k : ℕ) (r : ℝ) : ℝ :=
  tunedActivity r * pathPartition (2 * k) (tunedActivity r) -
    r * pathPartition (2 * k + 1) (tunedActivity r)

theorem tuningFunction_continuous (k : ℕ) : Continuous (tuningFunction k) := by
  have hc : Continuous tunedActivity :=
    continuous_id.mul ((continuous_const.add continuous_id).pow 2)
  have hp (n : ℕ) : Continuous (pathPartition n) :=
    (pathPolynomial n).continuous_eval₂ (Nat.castRingHom ℝ)
  exact (hc.mul ((hp (2 * k)).comp hc)).sub
    (continuous_id.mul ((hp (2 * k + 1)).comp hc))

theorem tuningFunction_factor (k : ℕ) {r : ℝ} (hr : 0 < r) :
    tuningFunction k r = tunedActivity r ^ (k + 1) *
      ((k + 1) * evenReverseSum k (1 / tunedActivity r) -
        r * oddReverseSum k (1 / tunedActivity r)) := by
  unfold tuningFunction
  rw [even_path_reversal k (tunedActivity_pos hr), odd_path_reversal k (tunedActivity_pos hr)]
  rw [pow_succ]
  ring

theorem tuningFunction_left_pos {k : ℕ} (hk : 16384 ≤ k) :
    0 < tuningFunction k ((k : ℝ) / 2) := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < (k : ℝ) / 2 := by linarith
  obtain ⟨_, ho, he, _⟩ := tuning_reverseSum_bounds hk (le_refl ((k : ℝ) / 2))
  rw [tuningFunction_factor k hr]
  apply mul_pos (pow_pos (tunedActivity_pos hr) _)
  have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ (k : ℝ) + 1 by positivity)
  have h2 := mul_le_mul_of_nonneg_left ho (le_of_lt hr)
  nlinarith

theorem tuningFunction_right_neg {k : ℕ} (hk : 16384 ≤ k) :
    tuningFunction k (2 * (k : ℝ)) < 0 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < 2 * (k : ℝ) := by linarith
  obtain ⟨ho, _, _, he⟩ := tuning_reverseSum_bounds hk (by linarith : (k : ℝ) / 2 ≤ 2 * k)
  rw [tuningFunction_factor k hr]
  apply mul_neg_of_pos_of_neg (pow_pos (tunedActivity_pos hr) _)
  have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ (k : ℝ) + 1 by positivity)
  have h2 := mul_le_mul_of_nonneg_left ho (le_of_lt hr)
  nlinarith

/-- The release's exact path tuning equation has a solution in the prescribed interval. -/
theorem exists_tuning_parameter {k : ℕ} (hk : 16384 ≤ k) :
    ∃ r : ℝ, (k : ℝ) / 2 < r ∧ r < 2 * k ∧
      tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
        r * pathPartition (2 * k + 1) (tunedActivity r) := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨r, hr, he⟩ := intermediate_value_Ioo'
    (by linarith : (k : ℝ) / 2 ≤ 2 * k)
    (tuningFunction_continuous k).continuousOn
    ⟨tuningFunction_right_neg hk, tuningFunction_left_pos hk⟩
  refine ⟨r, hr.1, hr.2, ?_⟩
  exact sub_eq_zero.mp he

end SphericalTreeFailures
