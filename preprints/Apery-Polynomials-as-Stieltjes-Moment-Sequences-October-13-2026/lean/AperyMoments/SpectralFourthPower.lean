import AperyMoments.LatticeFourthPower
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem spectralFourthKernel_integrable (b : ℝ) :
    Integrable (fun p : ℝ × ℝ => latticeDensity (p.2-b*Real.cos p.1)^4)
      ((volume.restrict (Ioc 0 Real.pi)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => latticeDensity (p.2-b*Real.cos p.1)^4) :=
    (latticeDensity_measurable.comp (by fun_prop)).pow_const 4
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro θ
    exact (measurePreserving_sub_right volume (b*Real.cos θ)).integrable_comp_of_integrable
      latticeDensity_fourth_integrable
  · have he : (fun θ : ℝ => ∫ w : ℝ, ‖latticeDensity (w-b*Real.cos θ)^4‖) =
        (fun _ : ℝ => ∫ w : ℝ, latticeDensity w^4) := by
      funext θ
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ latticeDensity (_ : ℝ)^4)]
      exact integral_sub_right_eq_self (μ := volume) (fun w : ℝ => latticeDensity w^4) (b*Real.cos θ)
    rw [he]
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne)

theorem nonneg_le_one_add_fourth {x : ℝ} (hx : 0 ≤ x) : x ≤ 1+x^4 := by
  by_cases h : x ≤ 1
  · nlinarith [sq_nonneg (x^2)]
  · have h1 : 1 ≤ x := le_of_not_ge h
    have h2 : x ≤ x^2 := by nlinarith
    have h4 : x^2 ≤ x^4 := by nlinarith [sq_nonneg (x^2-1)]
    linarith

theorem spectralDensity_fourth_bound_ae (b : ℝ) :
    ∀ᵐ w : ℝ ∂volume, spectralDensity b w^4 ≤
      Real.pi⁻¹ * ∫ θ in Ioc (0 : ℝ) Real.pi, latticeDensity (w-b*Real.cos θ)^4 := by
  filter_upwards [(spectralFourthKernel_integrable b).prod_left_ae] with w hw
  have hf4 : IntegrableOn (fun θ : ℝ => latticeDensity (w-b*Real.cos θ)^4) (Ioc 0 Real.pi) := hw
  have hf : IntegrableOn (fun θ : ℝ => latticeDensity (w-b*Real.cos θ)) (Ioc 0 Real.pi) := by
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 Real.pi) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    apply (hi.add hf4).mono' (latticeDensity_measurable.comp (by fun_prop)).aestronglyMeasurable
    apply Eventually.of_forall
    intro θ
    dsimp only [Function.comp_def, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (latticeDensity_nonneg _)]
    exact nonneg_le_one_add_fourth (latticeDensity_nonneg _)
  have hzero : volume (Ioc (0 : ℝ) Real.pi) ≠ 0 := by simp [Real.volume_Ioc, Real.pi_pos]
  have htop : volume (Ioc (0 : ℝ) Real.pi) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hj := (convexOn_pow (𝕜 := ℝ) 4).map_set_average_le (by fun_prop) isClosed_Ici hzero htop
    (Eventually.of_forall (fun θ : ℝ => latticeDensity_nonneg (w-b*Real.cos θ))) hf hf4
  simp only [setAverage_eq, Real.volume_real_Ioc, sub_zero, max_eq_left Real.pi_pos.le, smul_eq_mul] at hj
  unfold spectralDensity
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  exact hj

theorem spectralDensity_fourth_integrable (b : ℝ) : Integrable (fun w : ℝ => spectralDensity b w^4) := by
  have hi := (spectralFourthKernel_integrable b).integral_prod_right.const_mul Real.pi⁻¹
  apply hi.mono' ((spectralDensity_measurable b).pow_const 4).aestronglyMeasurable
  filter_upwards [spectralDensity_fourth_bound_ae b] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ spectralDensity b w^4)]
  exact hw

end AperyMoments
