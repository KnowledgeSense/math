import SphericalTreeFailures.TailNoise

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem memLp_tail_coordinate (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (v : BinaryNode) (q : ℝ≥0∞) :
    MemLp (fun τ : TailInputSpace k => tailSampleNoise k activity i (τ v)) q
      (tailInputMeasure k activity ha) := by
  apply MemLp.of_bound ((measurable_of_finite (tailSampleNoise k activity i)).comp
    (measurable_pi_apply v)).aestronglyMeasurable (2 * (k : ℝ) + 1)
  exact ae_of_all _ fun τ => tailSampleNoise_abs_le k activity ha i (τ v)

theorem integral_tail_coordinate (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (v : BinaryNode) :
    ∫ τ, tailSampleNoise k activity i (τ v) ∂tailInputMeasure k activity ha = 0 := by
  have h := (tail_input_law k activity ha v).integral_comp
    (measurable_of_finite (tailSampleNoise k activity i)).aestronglyMeasurable
  exact h.trans (tailSampleNoise_integral k activity ha i)

theorem integral_tail_coordinate_mul (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i j : Bool) (u v : BinaryNode) (huv : u ≠ v) :
    ∫ τ, tailSampleNoise k activity i (τ u) * tailSampleNoise k activity j (τ v)
      ∂tailInputMeasure k activity ha = 0 := by
  have hi := (tail_inputs_independent k activity ha).indepFun huv
  have hij := hi.comp (measurable_of_finite (tailSampleNoise k activity i))
    (measurable_of_finite (tailSampleNoise k activity j))
  have h := hij.integral_fun_mul_eq_mul_integral
    (memLp_tail_coordinate k activity ha i u 2).aestronglyMeasurable
    (memLp_tail_coordinate k activity ha j v 2).aestronglyMeasurable
  simpa only [Function.comp_apply, integral_tail_coordinate, zero_mul] using h

theorem integral_tail_coordinate_sq_le (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (v : BinaryNode) :
    ∫ τ, tailSampleNoise k activity i (τ v) ^ 2 ∂tailInputMeasure k activity ha ≤
      (2 * (k : ℝ) + 1) ^ 2 := by
  have h := (tail_input_law k activity ha v).integral_comp
    (measurable_of_finite (fun s => tailSampleNoise k activity i s ^ 2)).aestronglyMeasurable
  exact h.trans_le (tailSampleNoise_sq_integral_le k activity ha i)

theorem tail_sum_variance_bound (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (s : Finset BinaryNode) (states : BinaryNode → Bool) :
    ∫ τ, (∑ v ∈ s, tailSampleNoise k activity (states v) (τ v)) ^ 2
      ∂tailInputMeasure k activity ha ≤ (s.card : ℝ) * (2 * (k : ℝ) + 1) ^ 2 := by
  let f := fun v (τ : TailInputSpace k) => tailSampleNoise k activity (states v) (τ v)
  have hm (u v : BinaryNode) : Integrable (fun τ => f u τ * f v τ)
      (tailInputMeasure k activity ha) :=
    (memLp_tail_coordinate k activity ha (states u) u 2).integrable_mul
      (memLp_tail_coordinate k activity ha (states v) v 2)
  have he (τ : TailInputSpace k) : (∑ v ∈ s, f v τ) ^ 2 =
      ∑ u ∈ s, ∑ v ∈ s, f u τ * f v τ := by
    rw [pow_two, sum_mul]
    exact sum_congr rfl fun u _ => mul_sum ..
  change (∫ τ, (∑ v ∈ s, f v τ) ^ 2 ∂tailInputMeasure k activity ha) ≤ _
  simp_rw [he]
  rw [integral_finsetSum s (fun u _ => integrable_finsetSum s (fun v _ => hm u v))]
  simp_rw [integral_finsetSum s (fun v _ => hm _ v)]
  have hc (u : BinaryNode) (hu : u ∈ s) :
      (∑ v ∈ s, ∫ τ, f u τ * f v τ ∂tailInputMeasure k activity ha) =
        ∫ τ, f u τ ^ 2 ∂tailInputMeasure k activity ha := by
    rw [sum_eq_single u]
    · simp only [pow_two]
    · intro v _ huv
      exact integral_tail_coordinate_mul k activity ha (states u) (states v) u v huv.symm
    · exact fun h => False.elim (h hu)
  have heq := sum_congr rfl hc
  rw [heq]
  calc
    _ ≤ ∑ _u ∈ s, (2 * (k : ℝ) + 1) ^ 2 :=
      sum_le_sum fun u _ => integral_tail_coordinate_sq_le k activity ha (states u) u
    _ = _ := by simp

end SphericalTreeFailures
