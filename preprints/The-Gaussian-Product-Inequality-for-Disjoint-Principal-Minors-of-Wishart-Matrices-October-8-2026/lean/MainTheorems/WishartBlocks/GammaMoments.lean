import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory

theorem gammaMeasure_ae_positive (a r : ℝ) : ∀ᵐ x ∂(gammaMeasure a r), 0 < x := by
  let : NullSingletonClass (gammaMeasure a r) := by
    unfold gammaMeasure
    infer_instance
  have hz : gammaMeasure a r (Set.Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  apply ae_iff.mpr
  rw [show {x : ℝ | ¬0 < x} = Set.Iic 0 by ext x; simp]
  exact
    (measure_congr (Iio_ae_eq_Iic (μ := gammaMeasure a r) (a := (0 : ℝ)))).symm.trans hz

theorem gamma_weighted_integral {a r β : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hβ : 0 ≤ β) :
    ∫ x : ℝ in Set.Ioi 0, x ^ β * gammaPDFReal a r x =
      (r ^ a / Real.Gamma a) * ((1 / r) ^ (a + β) * Real.Gamma (a + β)) := by
  have he : (fun x : ℝ => x ^ β * gammaPDFReal a r x) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun x => (r ^ a / Real.Gamma a) *
        (x ^ (a + β - 1) * Real.exp (-(r * x))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [gammaPDFReal, ite_eq_left hx.le]
    rw [show a + β - 1 = β + (a - 1) by ring, Real.rpow_add hx]
    ring
  rw [integral_congr_ae he, integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < a + β) hr]

theorem gamma_positive_power_integrable {a r β : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hβ : 0 ≤ β) :
    IntegrableOn (fun x : ℝ => x ^ β * gammaPDFReal a r x) (Set.Ioi 0) := by
  by_contra h
  have hz := integral_undef h
  rw [gamma_weighted_integral ha hr hβ] at hz
  have hp : 0 < (r ^ a / Real.Gamma a) *
      ((1 / r) ^ (a + β) * Real.Gamma (a + β)) := by
    apply mul_pos
    · exact div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos ha)
    · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
        (Real.Gamma_pos_of_pos (by linarith))
  exact hp.ne' hz

theorem gamma_moment {a r β : ℝ} (ha : 0 < a) (hr : 0 < r) (hβ : 0 ≤ β) :
    ∫ x : ℝ, x ^ β ∂(gammaMeasure a r) =
      (r ^ a / Real.Gamma a) * ((1 / r) ^ (a + β) * Real.Gamma (a + β)) := by
  calc
    ∫ x : ℝ, x ^ β ∂(gammaMeasure a r)
        = ∫ x : ℝ in Set.Ioi 0, x ^ β ∂(gammaMeasure a r) := by
          symm
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          filter_upwards [gammaMeasure_ae_positive a r] with x hx
          intro h
          exact (h hx).elim
    _ = ∫ x : ℝ in Set.Ioi 0, x ^ β * gammaPDFReal a r x := by
      rw [gammaMeasure]
      unfold gammaPDF
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        ((measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable)
        (by simp) _ measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      simp [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), mul_comm]
    _ = _ := gamma_weighted_integral ha hr hβ

theorem gamma_moment_integrable {a r β : ℝ} (ha : 0 < a) (hr : 0 < r) (hβ : 0 ≤ β) :
    Integrable (fun x : ℝ => x ^ β) (gammaMeasure a r) := by
  by_contra h
  have hz := integral_undef h
  rw [gamma_moment ha hr hβ] at hz
  have hp : 0 < (r ^ a / Real.Gamma a) *
      ((1 / r) ^ (a + β) * Real.Gamma (a + β)) := by
    apply mul_pos
    · exact div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos ha)
    · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
        (Real.Gamma_pos_of_pos (by linarith))
  exact hp.ne' hz

end ResearchMain.WishartBlocks
