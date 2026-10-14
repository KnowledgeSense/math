import AperyMoments.EllipticComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Asymptotics

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace AperyMoments

/-- The elementary translated inverse-square-root majorant is locally integrable. -/
theorem inverse_sqrt_distance_integrableAt (x : ℝ) :
    IntegrableAtFilter (fun t : ℝ => ‖t - x‖ ^ (-(1 / 2 : ℝ))) (𝓝 x) volume := by
  have hlocal : LocallyIntegrable (fun t : ℝ => ‖t‖ ^ (-(1 / 2 : ℝ))) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := (1 / 2 : ℝ))
      (by simp) (by norm_num)
    · exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg t) _), one_mul]
    · exact (measurable_id.norm.pow measurable_const).aestronglyMeasurable
  obtain ⟨s, hs, hi⟩ := hlocal 0
  refine ⟨(fun t : ℝ => t - x) ⁻¹' s, ?_, ?_⟩
  · exact ((continuous_id.sub continuous_const).tendsto x).eventually (by simpa using hs)
  · exact ((measurePreserving_sub_right volume x).integrableOn_comp_preimage
      (MeasurableEquiv.subRight x).measurableEmbedding).mpr hi

/-- A simple real zero produces only an integrable inverse-square-root singularity. -/
theorem simple_zero_inverse_sqrt_integrableAt {f : ℝ → ℝ} {x f' : ℝ}
    (hf : Measurable f) (hd : HasDerivAt f f' x) (hder : f' ≠ 0) (hzero : f x = 0) :
    IntegrableAtFilter (fun t => ‖f t‖ ^ (-(1 / 2 : ℝ))) (𝓝 x) volume := by
  have ht := (hd.hasDerivAtFilter le_rfl).isTheta_sub hder
  have ht' : (fun t => f t - f x) =Θ[𝓝 x] (fun t => t - x) :=
    ⟨ht.1.comp_tendsto (tendsto_id.prodMk tendsto_const_pure),
      ht.2.comp_tendsto (tendsto_id.prodMk tendsto_const_pure)⟩
  have hn := ht'.norm_left.norm_right
  have hp := hn.rpow (r := -(1 / 2 : ℝ))
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  simp only [hzero, sub_zero] at hp
  apply hp.1.integrableAtFilter _ (inverse_sqrt_distance_integrableAt x)
  exact (hf.norm.pow measurable_const).stronglyMeasurable.stronglyMeasurableAtFilter

/-- The real majorant at any point of the elliptic branch cut is integrable on bounded intervals. -/
theorem elliptic_cut_majorant_locallyIntegrable {m : ℝ} (hm : 1 < m) :
    LocallyIntegrable (fun θ : ℝ => ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ))) volume := by
  intro θ
  let f : ℝ → ℝ := fun t => 1 - m * Real.sin t ^ 2
  have hf : Continuous f := by fun_prop
  by_cases hz : f θ = 0
  · apply simple_zero_inverse_sqrt_integrableAt hf.measurable
      ((((Real.hasDerivAt_sin θ).pow 2).const_mul m).const_sub 1) _ hz
    have hs : Real.sin θ ≠ 0 := by intro h; simp [f, h] at hz
    have hc : Real.cos θ ≠ 0 := by
      intro h
      have htrig := Real.sin_sq_add_cos_sq θ
      dsimp [f] at hz
      rw [h] at htrig
      nlinarith
    simp only [neg_ne_zero, mul_ne_zero_iff, Nat.reduceSub, pow_one]
    exact ⟨ne_of_gt (by linarith), ⟨⟨by norm_num, hs⟩, hc⟩⟩
  · have ho : IsOpen {t | f t ≠ 0} := isOpen_ne_fun hf continuous_const
    have hcont : ContinuousOn (fun t => ‖f t‖ ^ (-(1 / 2 : ℝ))) {t | f t ≠ 0} :=
      hf.norm.continuousOn.rpow_const (fun t ht => Or.inl (norm_ne_zero_iff.mpr ht))
    have hi := hcont.integrableAt_nhdsWithin (μ := volume) ho.measurableSet hz
    rwa [nhdsWithin_eq_nhds.mpr (ho.mem_nhds hz)] at hi

 theorem elliptic_cut_majorant_intervalIntegrable {m : ℝ} (hm : 1 < m) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)))
      volume a b := by
  have hi := (elliptic_cut_majorant_locallyIntegrable hm).integrableOn_isCompact
    (k := uIcc a b) isCompact_uIcc
  exact ⟨hi.mono_set (fun t ht => ⟨(min_le_left a b).trans ht.1.le, ht.2.trans (le_max_right a b)⟩),
    hi.mono_set (fun t ht => ⟨(min_le_right a b).trans ht.1.le, ht.2.trans (le_max_left a b)⟩)⟩

end AperyMoments
