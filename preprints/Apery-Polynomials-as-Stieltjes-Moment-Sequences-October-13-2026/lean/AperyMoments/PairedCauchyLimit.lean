import AperyMoments.PairedCauchyKernel
import AperyMoments.ResolventBoundaryVanishing
import AperyMoments.JumpExceptionalSet

noncomputable section
namespace AperyMoments
open Complex Set Filter
open scoped Topology

theorem pairedCauchyKernel_tendsto {ι : Type*} {l : Filter ι}
    {A : ι→ℂ} {t c : ι→ℝ} {x L : ℝ} {z : ℂ} (hz : 0<z.im)
    (ht : Tendsto t l (𝓝 x)) (hc : Tendsto c l (𝓝 0))
    (hi : Tendsto (fun i=>(A i).im) l (𝓝 L))
    (hv : Tendsto (fun i=>(c i:ℂ)*A i) l (𝓝 0)) :
    Tendsto (fun i=>pairedCauchyKernel (A i) z (t i) (c i)) l
      (𝓝 (2*I*(L:ℂ)/((x:ℂ)-z))) := by
  have htc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hcc := Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have hic := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hp := (htc.add (hcc.mul_const I)).sub_const z
  have hm := (htc.sub (hcc.mul_const I)).sub_const z
  simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_zero] at hp hm
  have hxz : (x:ℂ)-z≠0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im] at hh
    linarith
  have hvc := Complex.continuous_conj.continuousAt.tendsto.comp hv
  simp only [map_zero] at hvc
  have hl := ((hic.const_mul (2*I)).div hp hxz).sub
    ((hvc.const_mul (2*I)).div (hp.mul hm) (mul_ne_zero hxz hxz))
  simp only [mul_zero,zero_div,sub_zero] at hl
  apply hl.congr'
  filter_upwards [hp.eventually (eventually_ne_nhds hxz),hm.eventually (eventually_ne_nhds hxz)]
    with i hpi hmi
  rw [pairedCauchyKernel_split _ _ _ _ hpi hmi]
  simp only [Function.comp_def,Pi.div_apply,map_mul,Complex.conj_ofReal,mul_assoc]

theorem pairedMomentKernel_tendsto_positive {ι : Type*} {l : Filter ι}
    {t c : ι→ℝ} {α x : ℝ} {z : ℂ} (hα : 0<α) (hx : 0<x)
    (he : x∉jumpExceptionalSet α) (hz : 0<z.im)
    (ht : Tendsto t l (𝓝 x)) (hc : Tendsto c l (𝓝 0)) (hcp : ∀ᶠ i in l,0<c i) :
    Tendsto (fun i=>pairedMomentKernel α (c i) z (t i)) l
      (𝓝 ((2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ)))) := by
  have hne : x≠α := by intro h; exact he (Or.inl (by simp [h]))
  have hcut : reciprocalRadius α x≠2*Real.sqrt α+4 := by
    intro h; exact he (Or.inr ⟨hx,h⟩)
  have htc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hcc := Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have hpath : Tendsto (fun i=>(t i:ℂ)+(c i:ℂ)*I) l
      (𝓝[{s:ℂ | 0<s.im}] (x:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,add_zero] using htc.add (hcc.mul_const I)
    · simpa using hcp
  have hi := (momentTransform_im_boundary hα hx he).comp hpath
  have hv := (momentTransform_imaginary_mul_tendsto_zero hα hx hne hcut).comp hpath
  simp only [Function.comp_def,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hv
  have hl := pairedCauchyKernel_tendsto hz ht hc hi hv
  convert hl using 1
  · rfl
  · congr 1
    push_cast
    rw [show (x:ℂ)-z= -(z-(x:ℂ)) by ring,div_neg]
    ring

end AperyMoments
