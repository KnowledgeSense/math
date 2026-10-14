import MainTheorems.WishartBlocks.GammaMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory

theorem gamma_laplace {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : 0 < r + t) :
    ∫ x : ℝ, Real.exp (-(t * x)) ∂(gammaMeasure a r) = (r / (r + t)) ^ a := by
  have he : (fun x : ℝ => Real.exp (-(t * x)) * gammaPDFReal a r x) =ᵐ[volume.restrict
      (Set.Ioi 0)] fun x => (r ^ a / Real.Gamma a) *
        (x ^ (a - 1) * Real.exp (-((r + t) * x))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [gammaPDFReal, ite_eq_left hx.le]
    rw [show -((r + t) * x) = -(t * x) + -(r * x) by ring, Real.exp_add]
    ring
  calc
    ∫ x : ℝ, Real.exp (-(t * x)) ∂(gammaMeasure a r)
        = ∫ x : ℝ in Set.Ioi 0, Real.exp (-(t * x)) ∂(gammaMeasure a r) := by
          symm
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          filter_upwards [gammaMeasure_ae_positive a r] with x hx
          intro h
          exact (h hx).elim
    _ = ∫ x : ℝ in Set.Ioi 0, Real.exp (-(t * x)) * gammaPDFReal a r x := by
      rw [gammaMeasure]
      unfold gammaPDF
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        ((measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable)
        (by simp) _ measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      simp [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), mul_comm]
    _ = (r ^ a / Real.Gamma a) * ((1 / (r + t)) ^ a * Real.Gamma a) := by
      rw [integral_congr_ae he, integral_const_mul,
        Real.integral_rpow_mul_exp_neg_mul_Ioi ha ht]
    _ = (r / (r + t)) ^ a := by
      rw [Real.div_rpow hr.le ht.le, Real.div_rpow zero_le_one ht.le, Real.one_rpow]
      have hg := (Real.Gamma_pos_of_pos ha).ne'
      have hp := (Real.rpow_pos_of_pos ht a).ne'
      field_simp

end ResearchMain.WishartBlocks
