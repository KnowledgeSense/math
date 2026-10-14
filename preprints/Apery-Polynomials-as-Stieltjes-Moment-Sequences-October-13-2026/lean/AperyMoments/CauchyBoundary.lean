import AperyMoments.CauchyLocalDecomposition
import AperyMoments.CauchyRemainderContinuity
import AperyMoments.CauchyInterval

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem outsideCauchy_differentiableAt {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {a r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ ball (a : ℂ) r) :
    DifferentiableAt ℂ (densityCauchyTransform (outsideDensity h a r)) z := by
  have hn : ‖z - (a : ℂ)‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  apply densityCauchyTransform_differentiableAt (outsideDensity_measurable hh a r)
    (outsideDensity_integrable hi a r) (sub_pos.mpr hn)
  intro t ht
  have hs := outsideDensity_separation h hr t ht
  have ht' := norm_sub_le_norm_sub_add_norm_sub (a : ℂ) z (t : ℂ)
  rw [norm_sub_rev (a : ℂ) z] at ht'
  linarith

def cauchyLocalBoundary (h : ℝ → ℝ) (F : ℂ → ℂ) (a r x : ℝ) : ℂ :=
  densityCauchyTransform (outsideDensity h a r) (x : ℂ) +
    localCauchyRemainder F a r (x : ℂ) +
    F (x : ℂ) * ((Real.log (x - (a - r)) : ℂ) - (Real.log (a + r - x) : ℂ))

theorem densityCauchy_tendsto_upper {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    (heq : ∀ t ∈ Icc (a - r) (a + r), (h t : ℂ) = F (t : ℂ))
    {x : ℝ} (hx : x ∈ Ioo (a - r) (a + r)) :
    Tendsto (densityCauchyTransform h) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (cauchyLocalBoundary h F a r x - Real.pi * Complex.I * F (x : ℂ))) := by
  have hxb : (x : ℂ) ∈ ball (a : ℂ) r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hcF : ContinuousAt F (x : ℂ) := hF.continuousOn.continuousAt
    (mem_of_superset (isOpen_ball.mem_nhds hxb)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))))
  have ho := ((outsideCauchy_differentiableAt hh hi hr hxb).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.im}))
  have hR := (localCauchyRemainder_continuousAt hr hF hxb).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.im}))
  have hI := cauchyInterval_tendsto_upper (a-r) (a+r) x hx.1 hx.2
  have hl := (ho.add hR).add ((hcF.tendsto.mono_left nhdsWithin_le_nhds).mul hI)
  have he : (fun z => densityCauchyTransform (outsideDensity h a r) z +
      localCauchyRemainder F a r z + F z * cauchyInterval (a-r) (a+r) z) =ᶠ[
      𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)] densityCauchyTransform h := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (densityCauchy_local_decomposition hh hi hr hF heq (ne_of_gt hz)).symm
  convert hl.congr' he using 1
  congr 1
  unfold cauchyLocalBoundary
  ring

theorem densityCauchy_tendsto_lower {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    (heq : ∀ t ∈ Icc (a - r) (a + r), (h t : ℂ) = F (t : ℂ))
    {x : ℝ} (hx : x ∈ Ioo (a - r) (a + r)) :
    Tendsto (densityCauchyTransform h) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (cauchyLocalBoundary h F a r x + Real.pi * Complex.I * F (x : ℂ))) := by
  have hxb : (x : ℂ) ∈ ball (a : ℂ) r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hcF : ContinuousAt F (x : ℂ) := hF.continuousOn.continuousAt
    (mem_of_superset (isOpen_ball.mem_nhds hxb)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))))
  have ho := ((outsideCauchy_differentiableAt hh hi hr hxb).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  have hR := (localCauchyRemainder_continuousAt hr hF hxb).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  have hI := cauchyInterval_tendsto_lower (a-r) (a+r) x hx.1 hx.2
  have hl := (ho.add hR).add ((hcF.tendsto.mono_left nhdsWithin_le_nhds).mul hI)
  have he : (fun z => densityCauchyTransform (outsideDensity h a r) z +
      localCauchyRemainder F a r z + F z * cauchyInterval (a-r) (a+r) z) =ᶠ[
      𝓝[{z : ℂ | z.im < 0}] (x : ℂ)] densityCauchyTransform h := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (densityCauchy_local_decomposition hh hi hr hF heq (ne_of_lt hz)).symm
  convert hl.congr' he using 1
  congr 1
  unfold cauchyLocalBoundary
  ring

end AperyMoments
