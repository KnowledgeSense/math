import AperyMoments.PairedCompactLimit

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem compactPairedKernel_integrable {α δ R y : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hy : 0<y) (hyz : y<z.im) :
    Integrable (compactPairedKernel α δ R z y) := by
  have hi := (pairedMomentKernel_integrable hα hα1 hy hyz).indicator (s := Icc δ R) measurableSet_Icc
  exact (measurePreserving_add_left volume (horizontalCritical α y)).integrable_comp_of_integrable hi

theorem compactPairedKernel_majorant {α δ R : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hδ : 0<δ) (hR : 0<R) (hz : 0<z.im) :
    ∃ C:ℝ, 0≤C ∧ ∀ y:ℝ, 0<y → y≤α/2 → y≤1 → y≤z.im/2 →
      ∀ᵐ u:ℝ, ‖compactPairedKernel α δ R z y u‖≤
        (Icc (-α) R).indicator (fun u=>C*(1+‖u‖^(-(1/3:ℝ)))) u := by
  obtain ⟨C,hC,hbound⟩ := pairedMomentKernel_shifted_majorant hα hα1 hδ hR hz
  refine ⟨C,hC,?_⟩
  intro y hy hyα hy1 hyz
  have ha := horizontalCritical_bounds hα hy.le hyα
  have hne : ∀ᵐ u:ℝ, u≠0 := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton (0:ℝ) : volume {(0:ℝ)}=0)
  filter_upwards [hne] with u hu
  by_cases ht : horizontalCritical α y+u∈Icc δ R
  · have huK : u∈Icc (-α) R := by constructor <;> linarith [ht.1,ht.2]
    rw [compactPairedKernel,indicator_of_mem ht,indicator_of_mem huK]
    have hh := hbound y (horizontalCritical α y+u) hy hyα hy1 hyz ht.1 ht.2 (by simpa using hu)
    simpa only [add_sub_cancel_left] using hh
  · rw [compactPairedKernel,indicator_of_notMem ht,norm_zero]
    exact indicator_nonneg (fun u _=>by positivity) u

theorem compactPaired_majorant_integrable (α R C : ℝ) :
    Integrable ((Icc (-α) R).indicator (fun u:ℝ=>C*(1+‖u‖^(-(1/3:ℝ))))) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Integrable.const_mul
  exact (continuous_const.integrableOn_Icc (a := -α) (b := R)).add
    ((norm_rpow_locallyIntegrable (by norm_num : (1/3:ℝ)<1)).integrableOn_isCompact isCompact_Icc)

end AperyMoments
