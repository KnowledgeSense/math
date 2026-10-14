import AperyMoments.LowerElliptic
import AperyMoments.ArcsineSubstitution
import AperyMoments.EllipticCutParts

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def lowerEllipticRealKernel (z t : ℝ) : ℝ :=
  (t ^ 2 + z) ^ (-(1 / 2 : ℝ)) * (1 + z * t ^ 2) ^ (-(1 / 2 : ℝ))

theorem lowerEllipticKernel_ofReal {z : ℝ} (hz : 0 < z) (t : ℝ) :
    lowerEllipticKernel (z : ℂ) t = (lowerEllipticRealKernel z t : ℂ) := by
  unfold lowerEllipticKernel lowerEllipticRealKernel
  have ha : ((t : ℂ)^2+(z:ℂ)) = ((t^2+z:ℝ):ℂ) := by push_cast; rfl
  have hb : (1+(z:ℂ)*(t:ℂ)^2) = ((1+z*t^2:ℝ):ℂ) := by push_cast; rfl
  rw [ha, hb, inverse_sqrt_cpow_of_nonneg (by positivity), inverse_sqrt_cpow_of_nonneg (by positivity)]
  push_cast
  rfl

theorem scaled_arctan_image {z : ℝ} (hz : 0 < z) :
    (fun t : ℝ => Real.arctan (Real.sqrt z * t)) '' Ioi 0 = Ioo 0 (Real.pi / 2) := by
  have hr := Real.sqrt_pos.mpr hz
  ext θ
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.arctan_pos.mpr (mul_pos hr ht), (Real.arctan_mem_Ioo _).2⟩
  · intro hθ
    refine ⟨Real.tan θ / Real.sqrt z, div_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) hr, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ hr.ne']
    exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2

theorem lowerEllipticRealKernel_arctan_identity {z : ℝ} (hz : 0 < z) (t : ℝ) :
    (Real.sqrt z / (1 + (Real.sqrt z * t) ^ 2)) *
      (1 - (1 - z ^ 2) * Real.cos (Real.arctan (Real.sqrt z * t)) ^ 2) ^ (-(1 / 2 : ℝ)) =
      lowerEllipticRealKernel z t := by
  have ha : 0 < t ^ 2 + z := by positivity
  have hb : 0 < 1 + z * t ^ 2 := by positivity
  have hr := Real.sqrt_pos.mpr hz
  have hsa := Real.sqrt_pos.mpr ha
  have hsb := Real.sqrt_pos.mpr hb
  have hd : 1 + (Real.sqrt z * t) ^ 2 = 1 + z * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hz.le]
  rw [Real.cos_arctan, hd, div_pow, one_pow, Real.sq_sqrt hb.le]
  have he : 1 - (1 - z ^ 2) * (1 / (1 + z * t ^ 2)) = z * (t ^ 2 + z) / (1 + z * t ^ 2) := by
    field_simp
    ring
  rw [he, inverse_sqrt_rpow (by positivity), Real.sqrt_div (by positivity), Real.sqrt_mul hz.le]
  unfold lowerEllipticRealKernel
  rw [inverse_sqrt_rpow ha.le, inverse_sqrt_rpow hb.le]
  field_simp [hr.ne', hsa.ne', hsb.ne']
  rw [Real.sq_sqrt hb.le]

/-- The actual convergent continuation integral agrees with the original elliptic
integral on the positive real axis. -/
theorem lowerEllipticIntegral_ofReal {z : ℝ} (hz : 0 < z) :
    lowerEllipticIntegral (z : ℂ) = (ellipticK (1 - z ^ 2) : ℂ) := by
  have hr := Real.sqrt_pos.mpr hz
  let g : ℝ → ℝ := fun θ => (1 - (1-z^2)*Real.cos θ^2)^(-(1/2:ℝ))
  have hder t : HasDerivAt (fun t : ℝ => Real.arctan (Real.sqrt z*t))
      (Real.sqrt z / (1+(Real.sqrt z*t)^2)) t := by
    convert (Real.hasDerivAt_arctan (Real.sqrt z*t)).comp t ((hasDerivAt_id t).const_mul (Real.sqrt z)) using 1
    · rfl
    · simp only [mul_one]
      ring
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) => (hder t).hasDerivWithinAt)
    (fun a _ b _ h => mul_left_cancel₀ hr.ne' (Real.arctan_injective h)) g
  rw [scaled_arctan_image hz] at hi
  have he : (∫ t in Ioi (0:ℝ), lowerEllipticRealKernel z t) = ellipticK (1-z^2) := by
    calc
      _ = ∫ θ in Ioo (0:ℝ) (Real.pi/2), g θ := by
        rw [hi]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        rw [abs_of_pos (by positivity : 0 < Real.sqrt z / (1+(Real.sqrt z*t)^2))]
        exact (lowerEllipticRealKernel_arctan_identity hz t).symm
      _ = ∫ θ in (0:ℝ)..Real.pi/2, g θ := by
        rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
      _ = ellipticK (1-z^2) := by
        have h := intervalIntegral.integral_comp_sub_left
          (fun θ : ℝ => (1-(1-z^2)*Real.sin θ^2)^(-(1/2:ℝ)))
          (a := 0) (b := Real.pi/2) (Real.pi/2)
        simpa only [g, ellipticK, sub_self, sub_zero, Real.sin_pi_div_two_sub] using h
  unfold lowerEllipticIntegral
  simp_rw [lowerEllipticKernel_ofReal hz]
  rw [integral_complex_ofReal, he]

end AperyMoments
