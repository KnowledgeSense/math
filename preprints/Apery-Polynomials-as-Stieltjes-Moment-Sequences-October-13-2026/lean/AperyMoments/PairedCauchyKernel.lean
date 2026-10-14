import AperyMoments.MomentHorizontalFormula

noncomputable section
namespace AperyMoments
open Complex

def pairedCauchyKernel (A z : ℂ) (x c : ℝ) : ℂ :=
  A/((x:ℂ)+c*I-z)-starRingEnd ℂ A/((x:ℂ)-c*I-z)

theorem pairedCauchyKernel_eq (A z : ℂ) (x c : ℝ)
    (hp : (x:ℂ)+c*I-z≠0) (hm : (x:ℂ)-c*I-z≠0) :
    pairedCauchyKernel A z x c=
      2*I*((A.im:ℂ)*((x:ℂ)-z)-(c:ℂ)*A.re)/
        (((x:ℂ)+c*I-z)*((x:ℂ)-c*I-z)) := by
  have hA : A=(A.re:ℂ)+(A.im:ℂ)*I := (Complex.re_add_im A).symm
  unfold pairedCauchyKernel
  field_simp [hp,hm]
  rw [hA]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  simp only [mul_zero,mul_one,add_zero,zero_add,sub_zero]
  ring

theorem pairedCauchyKernel_split (A z : ℂ) (x c : ℝ)
    (hp : (x:ℂ)+c*I-z≠0) (hm : (x:ℂ)-c*I-z≠0) :
    pairedCauchyKernel A z x c=
      (2*I*(A.im:ℂ))/((x:ℂ)+c*I-z) -
      (2*I*(c:ℂ)*starRingEnd ℂ A)/
        (((x:ℂ)+c*I-z)*((x:ℂ)-c*I-z)) := by
  have hA : A=(A.re:ℂ)+(A.im:ℂ)*I := (Complex.re_add_im A).symm
  unfold pairedCauchyKernel
  field_simp [hp,hm]
  rw [hA]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  simp only [Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  simp only [mul_zero,mul_one,add_zero,zero_add]
  ring

theorem horizontal_denominator_lower {z : ℂ} {c : ℝ} (hz : 0<z.im)
    (hc : 0≤c) (hcz : c≤z.im/2) (x : ℝ) :
    z.im/2≤‖(x:ℂ)+c*I-z‖ ∧ z.im/2≤‖(x:ℂ)-c*I-z‖ := by
  constructor
  · have hi := Complex.abs_im_le_norm ((x:ℂ)+c*I-z)
    have he : ((x:ℂ)+c*I-z).im=c-z.im := by simp
    rw [he,abs_of_nonpos (by linarith)] at hi
    linarith
  · have hi := Complex.abs_im_le_norm ((x:ℂ)-c*I-z)
    have he : ((x:ℂ)-c*I-z).im= -c-z.im := by simp
    rw [he,abs_of_nonpos (by linarith)] at hi
    linarith

theorem pairedCauchyKernel_bound {z : ℂ} {c : ℝ} (hz : 0<z.im)
    (hc : 0≤c) (hcz : c≤z.im/2) (A : ℂ) (x : ℝ) :
    ‖pairedCauchyKernel A z x c‖≤4*|A.im|/z.im+8*c*‖A‖/z.im^2 := by
  obtain ⟨hp,hm⟩ := horizontal_denominator_lower hz hc hcz x
  have hp0 : 0<‖(x:ℂ)+c*I-z‖ := lt_of_lt_of_le (by positivity) hp
  have hm0 : 0<‖(x:ℂ)-c*I-z‖ := lt_of_lt_of_le (by positivity) hm
  rw [pairedCauchyKernel_split A z x c (norm_pos_iff.mp hp0) (norm_pos_iff.mp hm0)]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_div,norm_mul,norm_ofNat,Complex.norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hc,Complex.norm_conj]
  have h1 : 2*|A.im|/‖(x:ℂ)+c*I-z‖≤4*|A.im|/z.im := by
    apply (div_le_div_iff₀ hp0 hz).mpr
    nlinarith [abs_nonneg A.im]
  have h2 : 2*c*‖A‖/(‖(x:ℂ)+c*I-z‖*‖(x:ℂ)-c*I-z‖)≤8*c*‖A‖/z.im^2 := by
    apply (div_le_div_iff₀ (mul_pos hp0 hm0) (sq_pos_of_pos hz)).mpr
    have hh : z.im^2/4≤‖(x:ℂ)+c*I-z‖*‖(x:ℂ)-c*I-z‖ := by nlinarith
    have hn : 0≤c*‖A‖ := mul_nonneg hc (norm_nonneg A)
    nlinarith
  exact add_le_add h1 h2

end AperyMoments
