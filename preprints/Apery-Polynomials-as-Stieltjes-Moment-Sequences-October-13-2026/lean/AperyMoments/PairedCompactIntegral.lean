import AperyMoments.PairedCompactDomination

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem compactPairedKernel_tendsto_ae {α δ R : ℝ} {z : ℂ}
    (hα : 0<α) (hδ : 0<δ) (hz : 0<z.im) :
    ∀ᵐ u:ℝ, Tendsto (fun y=>compactPairedKernel α δ R z y u) (𝓝[>] (0:ℝ))
      (𝓝 (compactJumpKernel α δ R z u)) := by
  let E := jumpExceptionalSet α ∪ {δ,R}
  have hE : E.Finite := (jumpExceptionalSet_finite α).union (Set.toFinite _)
  have hpre : ((fun u:ℝ=>α+u) ⁻¹' E).Finite :=
    Set.Finite.preimage (fun u _ v _ h=>by linarith) hE
  have he : ∀ᵐ u:ℝ, α+u∉E := by
    apply ae_iff.mpr
    simp only [not_not]
    exact hpre.measure_zero volume
  filter_upwards [he] with u hu
  have hex : α+u∉jumpExceptionalSet α := fun h=>hu (Or.inl h)
  have hl : α+u≠δ := by intro h; exact hu (Or.inr (by simp [h]))
  have hr : α+u≠R := by intro h; exact hu (Or.inr (by simp [h]))
  exact compactPairedKernel_tendsto hα hδ hz u hex hl hr

theorem compactPairedKernel_integral_tendsto {α δ R : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hδ : 0<δ) (hR : 0<R) (hz : 0<z.im) :
    Tendsto (fun y=>∫ u:ℝ,compactPairedKernel α δ R z y u) (𝓝[>] (0:ℝ))
      (𝓝 (∫ u:ℝ,compactJumpKernel α δ R z u)) := by
  obtain ⟨C,hC,hbound⟩ := compactPairedKernel_majorant hα hα1 hδ hR hz
  have hev : ∀ᶠ y:ℝ in 𝓝[>] (0:ℝ), 0<y ∧ y≤α/2 ∧ y≤1 ∧ y≤z.im/2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ)<α/2)),
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ)<z.im/2))] with y hy hya hy1 hyz
    exact ⟨hy,hya.le,hy1.le,hyz.le⟩
  apply tendsto_integral_filter_of_dominated_convergence
    ((Icc (-α) R).indicator (fun u:ℝ=>C*(1+‖u‖^(-(1/3:ℝ)))))
  · filter_upwards [hev] with y hy
    exact (compactPairedKernel_integrable hα hα1 hy.1 (by linarith [hy.2.2.2])).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    exact hbound y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  · exact compactPaired_majorant_integrable α R C
  · exact compactPairedKernel_tendsto_ae hα hδ hz

theorem pairedMomentKernel_integral_Icc_tendsto {α δ R : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hδ : 0<δ) (hR : 0<R) (hz : 0<z.im) :
    Tendsto (fun y=>∫ x in Icc δ R,pairedMomentKernel α y z x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x in Icc δ R,(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ)))) := by
  have hl := compactPairedKernel_integral_tendsto hα hα1 hδ hR hz
  have h1 (y : ℝ) : (∫ u:ℝ,compactPairedKernel α δ R z y u)=
      ∫ x in Icc δ R,pairedMomentKernel α y z x := by
    unfold compactPairedKernel
    rw [integral_add_left_eq_self,integral_indicator measurableSet_Icc]
  have h2 : (∫ u:ℝ,compactJumpKernel α δ R z u)=
      ∫ x in Icc δ R,(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ)) := by
    unfold compactJumpKernel
    rw [integral_add_left_eq_self,integral_indicator measurableSet_Icc]
  simpa only [h1,h2] using hl

end AperyMoments
