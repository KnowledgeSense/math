import MainTheorems.WishartBlocks.GaussianGrowth
import MainTheorems.WishartBlocks.GaussianOdd
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

noncomputable def gaussianSmoothing (f : ℝ → ℝ) (v : ℝ≥0) (s : ℝ) : ℝ :=
  ∫ x, f (x + s) ∂(gaussianReal 0 v)

theorem gaussianSmoothing_hasDerivAt {f : ℝ → ℝ} (hf : f.HasTemperateGrowth)
    (v : ℝ≥0) (s₀ : ℝ) :
    HasDerivAt (gaussianSmoothing f v)
      (∫ x, deriv f (x + s₀) ∂(gaussianReal 0 v)) s₀ := by
  obtain ⟨k, C, hC, hbound⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  have hb : ∀ x, ‖deriv f x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using
      hbound 1 le_rfl x
  let B : ℝ → ℝ := fun x => (C * (2 + ‖s₀‖) ^ k) * (1 + ‖x‖) ^ k
  have hB : Integrable B (gaussianReal 0 v) :=
    (gaussian_polynomial_integrable 0 v k).const_mul _
  have hi : Integrable (fun x => f (x + s₀)) (gaussianReal 0 v) :=
    gaussian_temperate_integrable (hf.comp
      (Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const s₀))) 0 v
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 v) (s := Metric.ball s₀ 1) (bound := B)
    (F := fun s x => f (x + s)) (F' := fun s x => deriv f (x + s))
    (Metric.ball_mem_nhds s₀ (by norm_num)) _ hi _ _ hB _).2
  · exact Filter.Eventually.of_forall fun s =>
      (hf.1.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  · exact ((hf.1.continuous_deriv (by simp)).comp
      (continuous_id.add continuous_const)).aestronglyMeasurable
  · exact ae_of_all _ fun x s hs => by
      have hs' : ‖s - s₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs
      have hsN : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have ht := norm_add_le (s - s₀) s₀
        rw [sub_add_cancel] at ht
        linarith
      have hxs : 1 + ‖x + s‖ ≤ (1 + ‖x‖) * (2 + ‖s₀‖) := by
        have ht := norm_add_le x s
        nlinarith [norm_nonneg x, norm_nonneg s₀, mul_nonneg (norm_nonneg x) (norm_nonneg s₀)]
      calc
        ‖deriv f (x + s)‖ ≤ C * (1 + ‖x + s‖) ^ k := hb _
        _ ≤ C * ((1 + ‖x‖) * (2 + ‖s₀‖)) ^ k := by gcongr
        _ = B x := by dsimp [B]; rw [mul_pow]; ring
  · exact ae_of_all _ fun x s _ => by
      simpa only [Function.comp_def, zero_add, mul_one] using
        ((hf.1.differentiable (by simp)) (x + s)).hasDerivAt.comp s
          ((hasDerivAt_const s x).add (hasDerivAt_id' s))

theorem gaussianSmoothing_monotone {f : ℝ → ℝ} (hf : f.HasTemperateGrowth)
    {v : ℝ≥0} (hv : v ≠ 0)
    (ho : ∀ x, deriv f (-x) = -deriv f x)
    (hp : ∀ x ≥ 0, 0 ≤ deriv f x) :
    MonotoneOn (gaussianSmoothing f v) (Set.Ici 0) := by
  have hd := gaussianSmoothing_hasDerivAt hf v
  have hdiff : Differentiable ℝ (gaussianSmoothing f v) := fun s => (hd s).differentiableAt
  have hc : Continuous (gaussianSmoothing f v) := Differentiable.continuous hdiff
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc.continuousOn
  · intro s _
    exact (hd s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici, Set.mem_Ioi] at hs
    rw [(hd s).deriv]
    have he : ∫ x, deriv f (x + s) ∂(gaussianReal 0 v) =
        ∫ x, deriv f x ∂(gaussianReal s v) := by
      have hm : (gaussianReal 0 v).map (fun x => x + s) = gaussianReal s v := by
        simpa only [zero_add] using gaussianReal_map_add_const s (μ := (0 : ℝ)) (v := v)
      rw [← hm, integral_map (by fun_prop)
        (hf.1.continuous_deriv (by simp)).aestronglyMeasurable]
    rw [he]
    exact gaussian_odd_integral_nonneg hv hs.le ho hp (gaussian_derivative_integrable hf s v)

theorem quadraticPower_derivative {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (b x : ℝ) :
    HasDerivAt (fun y : ℝ => (c + d * y ^ 2) ^ b)
      (2 * b * d * x * (c + d * x ^ 2) ^ (b - 1)) x := by
  have hp := (hasDerivAt_const x c).add (((hasDerivAt_id' x).pow 2).const_mul d)
  have hb : c + d * x ^ 2 ≠ 0 := (by positivity : 0 < c + d * x ^ 2).ne'
  convert hp.rpow_const (p := b) (Or.inl hb) using 1
  dsimp only [Pi.add_apply, Pi.pow_apply]
  ring

theorem quadraticPower_gaussian_monotone {c d b : ℝ} (hc : 0 < c) (hd : 0 ≤ d)
    (hb : 0 ≤ b) {v : ℝ≥0} (hv : v ≠ 0) :
    MonotoneOn (gaussianSmoothing (fun x => (c + d * x ^ 2) ^ b) v) (Set.Ici 0) := by
  apply gaussianSmoothing_monotone (quadraticPower_temperate hc hd b) hv
  · intro x
    rw [(quadraticPower_derivative hc hd b (-x)).deriv,
      (quadraticPower_derivative hc hd b x).deriv]
    simp only [neg_sq]
    ring
  · intro x hx
    rw [(quadraticPower_derivative hc hd b x).deriv]
    positivity

end ResearchMain.WishartBlocks
