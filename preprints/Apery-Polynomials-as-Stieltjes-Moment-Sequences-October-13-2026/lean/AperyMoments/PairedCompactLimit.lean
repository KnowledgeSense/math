import AperyMoments.PairedCauchyLimit
import AperyMoments.PairedMomentMajorant
import AperyMoments.ShiftedPowerIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def compactPairedKernel (α δ R : ℝ) (z : ℂ) (y u : ℝ) : ℂ :=
  (Icc δ R).indicator (pairedMomentKernel α y z) (horizontalCritical α y+u)

def compactJumpKernel (α δ R : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (Icc δ R).indicator (fun x=>(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ))) (α+u)

theorem horizontalCritical_tendsto {α : ℝ} (hα : 0≤α) :
    Tendsto (horizontalCritical α) (𝓝 (0:ℝ)) (𝓝 α) := by
  have h : Continuous (horizontalCritical α) := by unfold horizontalCritical; fun_prop
  simpa only [horizontalCritical,zero_pow (by decide : 2≠0),sub_zero,Real.sqrt_sq hα] using h.tendsto 0

theorem compactPairedKernel_tendsto {α δ R : ℝ} {z : ℂ} (hα : 0<α)
    (hδ : 0<δ) (hz : 0<z.im) (u : ℝ)
    (he : α+u∉jumpExceptionalSet α) (hleft : α+u≠δ) (hright : α+u≠R) :
    Tendsto (fun y=>compactPairedKernel α δ R z y u) (𝓝[>] (0:ℝ))
      (𝓝 (compactJumpKernel α δ R z u)) := by
  have ht := ((horizontalCritical_tendsto hα.le).add_const u).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hc : Tendsto (fun y:ℝ=>y) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  by_cases hx : α+u∈Icc δ R
  · have hxi : α+u∈Ioo δ R := ⟨lt_of_le_of_ne hx.1 hleft.symm,lt_of_le_of_ne hx.2 hright⟩
    have hev := ht.eventually (isOpen_Ioo.mem_nhds hxi)
    have hl := pairedMomentKernel_tendsto_positive hα (hδ.trans_le hx.1) he hz ht hc self_mem_nhdsWithin
    rw [compactJumpKernel,indicator_of_mem hx]
    apply hl.congr'
    filter_upwards [hev] with y hy
    simp only [compactPairedKernel,indicator_of_mem (show horizontalCritical α y+u∈Icc δ R from ⟨hy.1.le,hy.2.le⟩)]
  · have hev := ht.eventually (isClosed_Icc.isOpen_compl.mem_nhds hx)
    rw [compactJumpKernel,indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with y hy
    simp only [compactPairedKernel,indicator_of_notMem hy]

end AperyMoments
