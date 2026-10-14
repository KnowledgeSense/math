import AperyMoments.SpectralMeasure
import AperyMoments.EllipticBounds
import AperyMoments.ShiftedPowerIntegral

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def latticeWeakConstant : ℝ := 8 * (4 : ℝ) ^ (1/8 : ℝ) / (2*Real.pi^2)

theorem latticeWeakConstant_nonneg : 0 ≤ latticeWeakConstant := by unfold latticeWeakConstant; positivity

theorem latticeDensity_weak_bound {x : ℝ} (hx : x ≠ 0) :
    latticeDensity x ≤ latticeWeakConstant * |x| ^ (-(1/8 : ℝ)) := by
  by_cases hs : |x| < 4
  · have hp : 0 < |x|/4 := by positivity
    have hK := ellipticK_complement_eighth_bound hp
    have he : 1-(|x|/4)^2 = 1-x^2/16 := by rw [div_pow, sq_abs]; ring
    rw [he] at hK
    have hpow : (|x|/4) ^ (-(1/8 : ℝ)) = |x| ^ (-(1/8 : ℝ)) * (4 : ℝ) ^ (1/8 : ℝ) := by
      rw [show |x|/4 = |x| * (4 : ℝ)⁻¹ by ring, Real.mul_rpow (abs_nonneg _) (by norm_num),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hpow] at hK
    rw [latticeDensity, ite_eq_left hs, latticeExpression]
    apply (div_le_div_of_nonneg_right hK (by positivity : 0 ≤ 2*Real.pi^2)).trans_eq
    unfold latticeWeakConstant
    ring
  · rw [latticeDensity, ite_eq_right hs]
    exact mul_nonneg latticeWeakConstant_nonneg (Real.rpow_nonneg (abs_nonneg _) _)

theorem latticeDensity_fourth_bound {x : ℝ} (hx : x ≠ 0) :
    latticeDensity x ^ 4 ≤ latticeWeakConstant ^ 4 * ‖x‖ ^ (-(1/2 : ℝ)) := by
  have h := pow_le_pow_left₀ (latticeDensity_nonneg x) (latticeDensity_weak_bound hx) 4
  rw [mul_pow] at h
  have he : (|x| ^ (-(1/8 : ℝ))) ^ 4 = ‖x‖ ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x), Real.norm_eq_abs]
    norm_num
  rwa [he] at h

theorem latticeDensity_fourth_integrable : Integrable (fun x : ℝ => latticeDensity x ^ 4) := by
  have hp := (norm_rpow_locallyIntegrable (by norm_num : (1/2 : ℝ) < 1)).integrableOn_isCompact
    (k := Icc (-4 : ℝ) 4) isCompact_Icc
  have hi : IntegrableOn (fun x : ℝ => latticeDensity x ^ 4) (Icc (-4) 4) := by
    apply (hp.const_mul (latticeWeakConstant^4)).mono' (latticeDensity_measurable.pow_const 4).aestronglyMeasurable
    have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
    filter_upwards [ae_restrict_of_ae hn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ latticeDensity x ^ 4)]
    exact latticeDensity_fourth_bound hx
  have he : (fun x : ℝ => latticeDensity x ^ 4) = (Icc (-4 : ℝ) 4).indicator (fun x => latticeDensity x ^ 4) := by
    funext x
    by_cases hx : x ∈ Icc (-4 : ℝ) 4
    · simp [hx]
    · have ha : 4 ≤ |x| := by
        by_contra hn
        have hh := abs_lt.mp (lt_of_not_ge hn)
        exact hx ⟨hh.1.le,hh.2.le⟩
      simp [hx,latticeDensity_eq_zero_of_abs_ge ha]
  rw [he]
  exact hi.integrable_indicator measurableSet_Icc

end AperyMoments
