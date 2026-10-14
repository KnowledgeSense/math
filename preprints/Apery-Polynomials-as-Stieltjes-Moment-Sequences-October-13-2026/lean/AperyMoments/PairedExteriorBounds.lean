import AperyMoments.PairedCompactIntegral

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem pairedCauchyKernel_norm_bound {z : ℂ} {c : ℝ} (hz : 0<z.im)
    (hc : 0≤c) (hcz : c≤z.im/2) (A : ℂ) (x : ℝ) :
    ‖pairedCauchyKernel A z x c‖≤4*‖A‖/z.im := by
  obtain ⟨hp,hm⟩ := horizontal_denominator_lower hz hc hcz x
  have hp0 : 0<‖(x:ℂ)+c*I-z‖ := lt_of_lt_of_le (by positivity) hp
  have hm0 : 0<‖(x:ℂ)-c*I-z‖ := lt_of_lt_of_le (by positivity) hm
  unfold pairedCauchyKernel
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_div,Complex.norm_conj]
  have h1 : ‖A‖/‖(x:ℂ)+c*I-z‖≤2*‖A‖/z.im := by
    apply (div_le_div_iff₀ hp0 hz).mpr
    nlinarith [norm_nonneg A]
  have h2 : ‖A‖/‖(x:ℂ)-c*I-z‖≤2*‖A‖/z.im := by
    apply (div_le_div_iff₀ hm0 hz).mpr
    nlinarith [norm_nonneg A]
  calc
    _ ≤ 2*‖A‖/z.im+2*‖A‖/z.im := add_le_add h1 h2
    _ = _ := by ring

theorem momentTransform_negative_compact_bound {α δ R : ℝ}
    (hα : 0<α) (hα1 : α≤1) (hδ : 0<δ) :
    ∃ C:ℝ, 0≤C ∧ ∀ x y:ℝ, -R≤x → x≤ -δ → 0≤y → y≤1 →
      ‖momentTransform α ((x:ℂ)+y*I)‖≤C := by
  let K : Set (ℝ×ℝ) := Icc (-R) (-δ) ×ˢ Icc 0 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p:ℝ×ℝ=>momentTransform α ((p.1:ℂ)+p.2*I)) K := by
    intro p hp
    have hn : ((p.1:ℂ)+p.2*I).re<0 := by simp only [Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]; linarith [hp.1.2]
    have hf : ContinuousAt (fun p:ℝ×ℝ=>(p.1:ℂ)+p.2*I) p := by fun_prop
    exact (((momentTransform_analyticOnNhd hα hα1) _ (Or.inr (Or.inl hn))).continuousAt.comp (f := fun p:ℝ×ℝ=>(p.1:ℂ)+p.2*I) hf).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x y hxR hxδ hy0 hy1
  exact (hC (x,y) ⟨⟨hxR,hxδ⟩,⟨hy0,hy1⟩⟩).trans (le_max_left _ _)

theorem pairedMomentKernel_zero_bound {α : ℝ} {z : ℂ}
    (hα : 0<α) (hz : 0<z.im) :
    ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ x y:ℝ, |x|<δ → 0<y → y<δ → y≤z.im/2 → x≠0 →
      ‖pairedMomentKernel α y z x‖≤C/Real.sqrt |x| := by
  obtain ⟨ε,A,hε,hA,hbound⟩ := momentTransform_zero_bound hα
  refine ⟨ε/3,4*A/z.im,by positivity,by positivity,?_⟩
  intro x y hx hy hyδ hyz hxn
  have hn : ‖(x:ℂ)+y*I‖<ε := by
    have hh := norm_add_le (x:ℂ) ((y:ℂ)*I)
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy] at hh
    linarith
  have hs : 0<((x:ℂ)+y*I).im := by simpa using hy
  have hm := hbound _ hs hn
  have hre : |x|≤‖(x:ℂ)+y*I‖ := by simpa using Complex.abs_re_le_norm ((x:ℂ)+y*I)
  have hsqrt : 0<Real.sqrt |x| := Real.sqrt_pos.mpr (abs_pos.mpr hxn)
  have hm' : ‖momentTransform α ((x:ℂ)+y*I)‖≤A/Real.sqrt |x| :=
    hm.trans (div_le_div_of_nonneg_left hA hsqrt (Real.sqrt_le_sqrt hre))
  have hk := pairedCauchyKernel_norm_bound hz hy.le hyz
    (momentTransform α ((x:ℂ)+y*I)) x
  change ‖pairedCauchyKernel (momentTransform α ((x:ℂ)+y*I)) z x y‖≤_
  calc
    _ ≤ 4*‖momentTransform α ((x:ℂ)+y*I)‖/z.im := hk
    _ ≤ 4*(A/Real.sqrt |x|)/z.im := div_le_div_of_nonneg_right (by linarith) hz.le
    _ = _ := by ring

theorem pairedMomentKernel_tail_bound {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) {x y : ℝ} (hy : 0<y)
    (hx : 256≤|x|) (hxz : 2*|z.re|≤|x|) :
    ‖pairedMomentKernel α y z x‖≤8/|x|^2 := by
  have hx0 : 0 < |x| := by linarith
  have hsn : |x|≤‖(x:ℂ)+y*I‖ := by simpa using Complex.abs_re_le_norm ((x:ℂ)+y*I)
  have hM := momentTransform_infinity_bound hα hα1 (by simpa using hy) (hx.trans hsn)
  have hM' : ‖momentTransform α ((x:ℂ)+y*I)‖≤2/|x| :=
    hM.trans (div_le_div_of_nonneg_left (by norm_num) hx0 hsn)
  have hdiff : |x|/2≤|x-z.re| := by
    have hh := abs_add_le (x-z.re) z.re
    rw [sub_add_cancel] at hh
    linarith
  have hp : |x|/2≤‖(x:ℂ)+y*I-z‖ := by
    have hh := Complex.abs_re_le_norm ((x:ℂ)+y*I-z)
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hh
    exact hdiff.trans hh
  have hm : |x|/2≤‖(x:ℂ)-y*I-z‖ := by
    have hh := Complex.abs_re_le_norm ((x:ℂ)-y*I-z)
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero] at hh
    exact hdiff.trans hh
  have bound (d : ℝ) (hd : |x|/2≤d) : ‖momentTransform α ((x:ℂ)+y*I)‖/d≤4/|x|^2 := by
    have hd0 : 0<d := lt_of_lt_of_le (by positivity) hd
    calc
      _ ≤ (2/|x|)/(|x|/2) := div_le_div₀ (by positivity) hM' (by positivity) hd
      _ = _ := by field_simp; ring
  unfold pairedMomentKernel
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_div,Complex.norm_conj]
  have h1 := bound _ hp
  have h2 := bound _ hm
  calc
    _ ≤ 4/|x|^2+4/|x|^2 := add_le_add h1 h2
    _ = _ := by ring

end AperyMoments
