import AperyMoments.SpectralMeasure
import AperyMoments.EllipticBounds

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem latticeDensity_continuousAt_positive {t : ℝ} (ht : 0 < t) (ht4 : t ≠ 4) :
    ContinuousAt latticeDensity t := by
  by_cases hh : t < 4
  · have hm : 1 - t^2/16 < 1 := by nlinarith [sq_pos_of_pos ht]
    have hK := (ellipticK_continuousOn.continuousAt (Iio_mem_nhds hm)).comp
      (f := fun u : ℝ => 1-u^2/16) (by fun_prop)
    apply (hK.div_const (2 * Real.pi^2)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht hh] with u hu
    simp [latticeDensity, latticeExpression, abs_of_pos hu.1, hu.2]
  · have hgt : 4 < t := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm ht4)
    apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with u hu
    change 4 < u at hu
    have hup : 0 < u := by linarith
    simp [latticeDensity, abs_of_pos hup, not_lt.mpr hu.le]

theorem latticeDensity_bound_away_zero {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    |latticeDensity t| ≤ ellipticK (1-δ^2/16) / (2*Real.pi^2) := by
  rw [abs_of_nonneg (latticeDensity_nonneg t)]
  have hm : 1-δ^2/16 < 1 := by nlinarith [sq_pos_of_pos hδ]
  by_cases hh : |t| < 4
  · rw [latticeDensity, ite_eq_left hh, latticeExpression]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply ellipticK_mono _ hm
    nlinarith
  · rw [latticeDensity, ite_eq_right hh]
    exact div_nonneg (ellipticK_nonneg hm.le) (by positivity)

theorem cosine_level_null {b : ℝ} (hb : 0 < b) (w c : ℝ) :
    volume {θ : ℝ | θ ∈ Icc 0 Real.pi ∧ w-b*Real.cos θ=c} = 0 := by
  apply Set.Subsingleton.measure_zero
  intro θ hθ φ hφ
  apply Real.strictAntiOn_cos.injOn hθ.1 hφ.1
  nlinarith [hθ.2, hφ.2]

/-- The truncated spectral density is continuous on the whole outer interval, including
where the lattice support endpoint passes through an angular endpoint. -/
theorem spectralDensity_continuousAt_outer {b w : ℝ} (hb : 0 < b) (hw : b < w) :
    ContinuousAt (spectralDensity b) w := by
  let δ := (w-b)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let M := ellipticK (1-δ^2/16)/(2*Real.pi^2)
  change Tendsto _ _ _
  unfold spectralDensity
  apply Tendsto.const_mul
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => M)
  · apply Eventually.of_forall
    intro u
    exact (latticeDensity_measurable.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show w-δ < w by linarith)] with u hu
    change w-δ < u at hu
    apply Eventually.of_forall
    intro θ _
    rw [Real.norm_eq_abs]
    apply latticeDensity_bound_away_zero hδ
    have hcos := Real.cos_le_one θ
    have hm := mul_le_mul_of_nonneg_left hcos hb.le
    dsimp [δ] at *
    linarith
  · exact intervalIntegrable_const
  · have hne : ∀ᵐ θ : ℝ ∂volume, θ ∉ {θ : ℝ | θ ∈ Icc 0 Real.pi ∧ w-b*Real.cos θ=4} := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using cosine_level_null hb w 4
    filter_upwards [hne] with θ hθ hθI
    rw [uIoc_of_le Real.pi_pos.le] at hθI
    have hpos : 0 < w-b*Real.cos θ := by
      have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb.le
      linarith
    have hnot : w-b*Real.cos θ ≠ 4 := by
      intro he
      exact hθ ⟨⟨hθI.1.le,hθI.2⟩,he⟩
    exact ((latticeDensity_continuousAt_positive hpos hnot).comp (f := fun u : ℝ => u-b*Real.cos θ)
      (by fun_prop)).tendsto

end AperyMoments
