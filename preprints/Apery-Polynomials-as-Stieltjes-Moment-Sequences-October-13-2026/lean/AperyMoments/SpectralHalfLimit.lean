import AperyMoments.SpectralSplit

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

def spectralHalfBound (δ R : ℝ) : ℝ :=
  (R * δ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ))) *
    ((8 * (δ / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) / (2 * Real.pi ^ 2))

theorem spectralHalfKernel_bound {b δ R σ : ℝ} (hδ : 0 < δ) (hR4 : R < 4)
    (hσ : |σ| = 1) {w : ℂ} (hw : w.im < 0)
    (hl : δ ≤ b + w.re) (hr : δ ≤ b - w.re) (hR : b - w.re ≤ R)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    ‖spectralHalfKernel b w σ v‖ ≤ spectralHalfBound δ R * convolutionEndpointWeight v := by
  have ha0 : 0 < b - w.re := hδ.trans_le hr
  have hR0 := ha0.trans_le hR
  have hweight := arcsineHalfWeight_nonneg (by linarith : -b < w.re) (by linarith : w.re < b)
    ⟨hv.1.le, hv.2.le⟩
  have hP := continuedLattice_scaled_bound hδ hR4 hr hR hv
    (z := ((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ))
    (by simpa using hw) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
      rw [abs_mul, abs_mul, hσ, abs_of_pos ha0, abs_of_pos hv.1, one_mul])
  have hW := arcsineHalfWeight_bound hδ hr hl hR hv
  unfold spectralHalfKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight]
  have hB : 0 ≤ R * δ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ)) := by positivity
  calc
    _ ≤ ((R * δ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ))) * (1 - v) ^ (-(1 / 2 : ℝ))) *
        (((8 * (δ / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) /
        (2 * Real.pi ^ 2)) * v ^ (-(1 / 8 : ℝ))) :=
      mul_le_mul hW hP (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg (by linarith [hv.2]) _))
    _ = _ := by unfold spectralHalfBound convolutionEndpointWeight; ring

theorem spectralHalfKernel_continuousOn {b σ : ℝ} {w : ℂ} (hw : w.im < 0)
    (hl : -b < w.re) (hr : w.re < b) :
    ContinuousOn (spectralHalfKernel b w σ) (Ioo 0 1) := by
  have hW : ContinuousOn (arcsineHalfWeight b w.re) (Ioo 0 1) := by
    unfold arcsineHalfWeight
    apply ContinuousOn.mul
    · apply continuousOn_const.mul
      apply ContinuousOn.rpow_const (by fun_prop)
      intro v hv
      left
      have ha := sub_pos.mpr hr
      nlinarith [mul_pos ha hv.1]
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro v hv
      left
      linarith [hv.2]
  apply hW.smul
  intro v _
  have hz : (((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ)).im < 0 := by simpa using hw
  exact ((continuedLattice_analyticOnNhd _ hz).continuousAt.comp
    (f := fun v : ℝ => ((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ))
    (by fun_prop)).continuousWithinAt

/-- Both moving singularities have fixed endpoints after the affine split. -/
theorem spectralHalfIntegral_boundary {b a σ : ℝ} (hb2 : b ≤ 2) (hl : -b < a) (hr : a < b)
    (hσ : |σ| = 1) :
    Tendsto (fun w : ℂ => ∫ v in (0 : ℝ)..1, spectralHalfKernel b w σ v)
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝 (∫ v in (0 : ℝ)..1, arcsineHalfWeight b a v • latticeLowerBoundary (σ * (b - a) * v))) := by
  let δ : ℝ := min (b - a) (b + a) / 2
  let R : ℝ := (max (b - a) (b + a) + 4) / 2
  have hmin : 0 < min (b - a) (b + a) := lt_min (by linarith) (by linarith)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < b - a := by dsimp [δ]; linarith [min_le_left (b - a) (b + a)]
  have hδl : δ < b + a := by dsimp [δ]; linarith [min_le_right (b - a) (b + a)]
  have hm4 : max (b - a) (b + a) < 4 := max_lt (by linarith) (by linarith)
  have hR4 : R < 4 := by dsimp [R]; linarith
  have hRr : b - a < R := by dsimp [R]; linarith [le_max_left (b - a) (b + a)]
  have hRl : b + a < R := by dsimp [R]; linarith [le_max_right (b - a) (b + a)]
  have hnear : ∀ᶠ w : ℂ in 𝓝[{z : ℂ | z.im < 0}] (a : ℂ),
      δ < b - w.re ∧ b - w.re < R ∧ δ < b + w.re ∧ b + w.re < R ∧ w.im < 0 := by
    have hright : Tendsto (fun w : ℂ => b - w.re) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝 (b - a)) :=
      ((show Continuous (fun w : ℂ => b - w.re) by fun_prop).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hleft : Tendsto (fun w : ℂ => b + w.re) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝 (b + a)) :=
      ((show Continuous (fun w : ℂ => b + w.re) by fun_prop).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    filter_upwards [hright.eventually (Ioo_mem_nhds hδr hRr),
      hleft.eventually (Ioo_mem_nhds hδl hRl), self_mem_nhdsWithin] with w hw1 hw2 hw3
    exact ⟨hw1.1, hw1.2, hw2.1, hw2.2, hw3⟩
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v => spectralHalfBound δ R * convolutionEndpointWeight v)
  · filter_upwards [hnear] with w hw
    exact (spectralHalfKernel_continuousOn hw.2.2.2.2 (by linarith [hw.2.2.1]) (by linarith [hw.1])).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [hnear] with w hw
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact spectralHalfKernel_bound hδ hR4 hσ hw.2.2.2.2 hw.2.2.1.le hw.1.le hw.2.1.le hv
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (IntervalIntegrable.const_mul convolutionEndpointWeight_integrable (spectralHalfBound δ R))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact spectralHalfKernel_tendsto hb2 hl hr hσ hv

end AperyMoments
