import AperyMoments.LatticeHalfStrip
import AperyMoments.ShiftedArcsineBound
import AperyMoments.ArcsineSplit
import AperyMoments.SpectralContinuation

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def spectralEndpointHalfBound (b : ℝ) : ℝ :=
  latticeWeakConstant*b^(-(1/8 : ℝ))*shiftedArcsineBound +
    latticeHalfStripConstant*(∫ v in (0 : ℝ)..1, (1-v)^(-(1/2 : ℝ)))

theorem arcsineHalfWeight_zero_bound {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo 0 1) :
    arcsineHalfWeight b 0 v ≤ (1-v)^(-(1/2 : ℝ)) := by
  have h := arcsineHalfWeight_bound (b := b) (a := 0) (v := v) (δ := b) (R := b) hb (by simp) (by simp) (by simp) hv
  have he : b*b^(-(1/2 : ℝ))*b^(-(1/2 : ℝ)) = 1 := by
    rw [mul_assoc, ← Real.rpow_add hb]
    norm_num
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hb.ne'
  simpa only [he, one_mul] using h

theorem spectralHalf_point_bound {b c v : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hc : |c| = b) (hw : w.im < 0) (hl : b/2 ≤ w.re) (_hu : w.re ≤ 2*b)
    (hv : v ∈ Ioo 0 1) (hne : v ≠ w.re/c) :
    ‖arcsineHalfWeight b 0 v • continuedLattice (w-(c*v : ℝ))‖ ≤
      (latticeWeakConstant*b^(-(1/8 : ℝ)))*shiftedArcsineMajorant (w.re/c) v +
        latticeHalfStripConstant*(1-v)^(-(1/2 : ℝ)) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc; linarith
  have hcv : |c*v| ≤ b := by rw [abs_mul, hc, abs_of_pos hv.1]; nlinarith [hv.2]
  have hr : (w-(c*v : ℝ)).re = w.re-c*v := by simp
  have he : |w.re-c*v| = b*‖v-w.re/c‖ := by
    have he : w.re-c*v = -(c*(v-w.re/c)) := by field_simp; ring
    rw [he, abs_neg, abs_mul, hc, Real.norm_eq_abs]
  have hn : (w-(c*v : ℝ)).re ≠ 0 := by
    rw [hr]
    intro h
    apply hne
    apply (eq_div_iff hc0).mpr
    nlinarith
  have hP := continuedLattice_halfStrip_bound (z := w-(c*v : ℝ))
    (by simpa using hw) (by rw [hr]; have := le_abs_self (c*v); linarith) hn
  rw [hr, he, Real.mul_rpow hb.le (norm_nonneg _)] at hP
  have hW := arcsineHalfWeight_zero_bound hb hv
  have hW0 := arcsineHalfWeight_nonneg (a := 0) (by linarith : -b < 0) hb ⟨hv.1.le,hv.2.le⟩
  have hA := latticeWeakConstant_nonneg
  have hB := latticeHalfStripConstant_nonneg
  have hp := Real.rpow_nonneg hb.le (-(1/8 : ℝ))
  have hq := Real.rpow_nonneg (norm_nonneg (v-w.re/c)) (-(1/8 : ℝ))
  have hE := Real.rpow_nonneg (by linarith [hv.2] : 0 ≤ 1-v) (-(1/2 : ℝ))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hW0]
  have hh := mul_le_mul hW hP (norm_nonneg _) hE
  have hy := mul_le_mul_of_nonneg_left (shiftedArcsine_power_bound (a := w.re/c) hv.2.le)
    (mul_nonneg hA hp)
  nlinarith

theorem spectralHalf_integral_bound {b c : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hc : |c| = b) (hw : w.im < 0) (hl : b/2 ≤ w.re) (hu : w.re ≤ 2*b) :
    ‖∫ v in (0 : ℝ)..1, arcsineHalfWeight b 0 v • continuedLattice (w-(c*v : ℝ))‖ ≤
      spectralEndpointHalfBound b := by
  let a := w.re/c
  have ha : |a| ≤ 2 := by
    dsimp only [a]
    rw [abs_div, hc, abs_of_nonneg (by linarith : 0 ≤ w.re)]
    exact (div_le_iff₀ hb).mpr hu
  have hi := ((shiftedArcsineMajorant_integrable a).const_mul
    (latticeWeakConstant*b^(-(1/8 : ℝ)))).add
    ((endpointPower_integrable (by norm_num : (1/2 : ℝ)<1)).const_mul latticeHalfStripConstant)
  have hn : ∀ᵐ v : ℝ ∂volume, v ≠ a ∧ v ≠ 1 := by
    have h₁ : ∀ᵐ v : ℝ ∂volume, v ≠ a := by
      apply ae_iff.mpr
      simp
    have h₂ : ∀ᵐ v : ℝ ∂volume, v ≠ 1 := by
      apply ae_iff.mpr
      simp
    exact h₁.and h₂
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (f := fun v : ℝ =>
    arcsineHalfWeight b 0 v • continuedLattice (w-(c*v : ℝ))) (by norm_num : (0 : ℝ) ≤ 1)
    (show ∀ᵐ v : ℝ ∂volume, v ∈ Ioc (0 : ℝ) 1 →
      ‖arcsineHalfWeight b 0 v • continuedLattice (w-(c*v : ℝ))‖ ≤
        (latticeWeakConstant*b^(-(1/8 : ℝ)))*shiftedArcsineMajorant a v +
          latticeHalfStripConstant*(1-v)^(-(1/2 : ℝ)) from by
      filter_upwards [hn] with v hv hmem
      exact spectralHalf_point_bound hb hb2 hc hw hl hu
        ⟨hmem.1, lt_of_le_of_ne hmem.2 hv.2⟩ hv.1) hi
  apply hbound.trans
  rw [intervalIntegral.integral_add
    ((shiftedArcsineMajorant_integrable a).const_mul _)
    ((endpointPower_integrable (by norm_num : (1/2 : ℝ)<1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold spectralEndpointHalfBound
  exact add_le_add (mul_le_mul_of_nonneg_left (shiftedArcsine_integral_bound ha)
    (mul_nonneg latticeWeakConstant_nonneg (Real.rpow_nonneg hb.le _))) le_rfl

def spectralEndpointBound (b : ℝ) : ℝ := 2*Real.pi⁻¹*spectralEndpointHalfBound b

theorem spectralEndpointHalfBound_nonneg {b : ℝ} (hb : 0 < b) :
    0 ≤ spectralEndpointHalfBound b := by
  have hi : 0 ≤ ∫ v in (0 : ℝ)..1, (1-v)^(-(1/2 : ℝ)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact Real.rpow_nonneg (by linarith [hv.2]) _
  unfold spectralEndpointHalfBound
  exact add_nonneg (mul_nonneg (mul_nonneg latticeWeakConstant_nonneg (Real.rpow_nonneg hb.le _))
    shiftedArcsineBound_nonneg) (mul_nonneg latticeHalfStripConstant_nonneg hi)

theorem spectralEndpointBound_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ spectralEndpointBound b := by
  unfold spectralEndpointBound
  exact mul_nonneg (by positivity) (spectralEndpointHalfBound_nonneg hb)

theorem continuedSpectral_endpoint_bound {b : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hw : w.im < 0) (hl : b/2 ≤ w.re) (hu : w.re ≤ 2*b) :
    ‖continuedSpectral b w‖ ≤ spectralEndpointBound b := by
  have hi := (continuedSpectral_integrand_continuous hb.le (Or.inl hw)).intervalIntegrable
    (μ := volume) 0 Real.pi
  have hs := arcsine_split (a := 0) hb (by linarith) hb
    (fun u : ℝ => continuedLattice (w-u)) hi
  simp only [neg_zero, add_zero, sub_zero, zero_sub, zero_add] at hs
  have hleft := spectralHalf_integral_bound hb hb2 (c := -b)
    (by rw [abs_neg, abs_of_pos hb]) hw hl hu
  have hright := spectralHalf_integral_bound hb hb2 (c := b) (abs_of_pos hb) hw hl hu
  have he : (fun v : ℝ => arcsineHalfWeight b 0 v • continuedLattice (w-(-b*v : ℝ))) =
      (fun v : ℝ => arcsineHalfWeight b 0 v • continuedLattice (w-(-(b*v) : ℝ))) := by
    funext v
    rw [neg_mul]
  rw [he] at hleft
  unfold continuedSpectral
  rw [hs, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hn := norm_add_le
    (∫ v in (0 : ℝ)..1, arcsineHalfWeight b 0 v • continuedLattice (w-(-(b*v) : ℝ)))
    (∫ v in (0 : ℝ)..1, arcsineHalfWeight b 0 v • continuedLattice (w-(b*v : ℝ)))
  have hh : ‖(∫ v in (0 : ℝ)..1, arcsineHalfWeight b 0 v • continuedLattice (w-(-(b*v) : ℝ))) +
      (∫ v in (0 : ℝ)..1, arcsineHalfWeight b 0 v • continuedLattice (w-(b*v : ℝ)))‖ ≤
      2*spectralEndpointHalfBound b := by linarith
  have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  unfold spectralEndpointBound
  nlinarith

end AperyMoments
