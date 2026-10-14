import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

set_option maxHeartbeats 1200000 in
theorem gaussian_polynomial_integrable (μ : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ k) (gaussianReal μ v) := by
  have hX : MemLp id (k : ℝ≥0∞) (gaussianReal μ v) :=
    IsGaussian.memLp_id (gaussianReal μ v) (k : ℝ≥0∞) (by simp)
  have hI : Integrable (fun x : ℝ => ‖x‖ ^ k) (gaussianReal μ v) :=
    hX.integrable_norm_pow' (p := k)
  have hB : Integrable (fun x : ℝ => (2 : ℝ) ^ (k - 1) * (1 + ‖x‖ ^ k))
      (gaussianReal μ v) := ((integrable_const 1).add hI).const_mul _
  apply hB.mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [one_pow] using add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k

theorem gaussian_temperate_integrable {f : ℝ → ℝ} (hf : f.HasTemperateGrowth)
    (μ : ℝ) (v : ℝ≥0) : Integrable f (gaussianReal μ v) := by
  obtain ⟨k, C, _, hC⟩ := hf.norm_iteratedFDeriv_le_uniform 0
  apply ((gaussian_polynomial_integrable μ v k).const_mul C).mono'
    hf.1.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [norm_iteratedFDeriv_zero] using hC 0 le_rfl x

theorem gaussian_derivative_integrable {f : ℝ → ℝ} (hf : f.HasTemperateGrowth)
    (μ : ℝ) (v : ℝ≥0) : Integrable (deriv f) (gaussianReal μ v) := by
  obtain ⟨k, C, _, hC⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  apply ((gaussian_polynomial_integrable μ v k).const_mul C).mono'
    (hf.1.continuous_deriv (by simp)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using hC 1 le_rfl x

theorem quadraticPower_temperate {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (b : ℝ) :
    (fun x : ℝ => (c + d * x ^ 2) ^ b).HasTemperateGrowth := by
  let k : ℝ := Real.sqrt (d / c)
  have hs : (fun x : ℝ => k * x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const k).mul Function.HasTemperateGrowth.id'
  have h := (Function.HasTemperateGrowth.const (c ^ b)).mul
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow (H := ℝ) b).comp hs)
  have he : (fun x : ℝ => c ^ b * (1 + ‖k * x‖ ^ 2) ^ b) =
      fun x : ℝ => (c + d * x ^ 2) ^ b := by
    funext x
    rw [← Real.mul_rpow hc.le (by positivity : 0 ≤ 1 + ‖k * x‖ ^ 2)]
    apply congrArg (fun z : ℝ => z ^ b)
    dsimp [k]
    simp only [mul_pow, sq_abs,
      Real.sq_sqrt (div_nonneg hd hc.le)]
    field_simp
  change (fun x : ℝ => c ^ b * (1 + ‖k * x‖ ^ 2) ^ b).HasTemperateGrowth at h
  rw [he] at h
  exact h

theorem quadraticPower_gaussian_integrable {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (b μ : ℝ)
    (v : ℝ≥0) : Integrable (fun x : ℝ => (c + d * x ^ 2) ^ b) (gaussianReal μ v) :=
  gaussian_temperate_integrable (quadraticPower_temperate hc hd b) μ v

end ResearchMain.WishartBlocks
