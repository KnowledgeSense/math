import AperyMoments.LatticeSectorBound
import AperyMoments.SpectralContinuation

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def spectralDecayConstant : ℝ := latticeSectorConstant * (2 : ℝ) ^ (7 / 8 : ℝ)

theorem spectralDecayConstant_nonneg : 0 ≤ spectralDecayConstant := by
  unfold spectralDecayConstant
  have h := latticeSectorConstant_nonneg
  positivity

theorem spectral_shift_sector {b : ℝ} {w : ℂ} (hb : 0 ≤ b) (hre : 0 ≤ w.re)
    (hn : 4 * b ≤ ‖w‖) (θ : ℝ) :
    ‖w‖ / 2 ≤ ‖w - (b * Real.cos θ : ℝ)‖ ∧
      -‖w - (b * Real.cos θ : ℝ)‖ / 2 ≤ (w - (b * Real.cos θ : ℝ)).re := by
  have hu : |b * Real.cos θ| ≤ b := by
    rw [abs_mul, abs_of_nonneg hb]
    nlinarith [Real.abs_cos_le_one θ]
  have hu' : b * Real.cos θ ≤ b := (le_abs_self _).trans hu
  have hh := norm_sub_norm_le w ((b * Real.cos θ : ℝ) : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at hh
  simp only [Complex.sub_re, Complex.ofReal_re]
  constructor <;> linarith

theorem continuedLattice_spectral_bound {b : ℝ} {w : ℂ} (hb : 0 < b)
    (him : w.im < 0) (hre : 0 ≤ w.re) (hn : 4 * b ≤ ‖w‖) (θ : ℝ) :
    ‖continuedLattice (w - (b * Real.cos θ : ℝ))‖ ≤
      spectralDecayConstant * ‖w‖ ^ (-(7 / 8 : ℝ)) := by
  have hs := spectral_shift_sector hb.le hre hn θ
  have hi : (w - (b * Real.cos θ : ℝ)).im < 0 := by simpa using him
  have h := continuedLattice_sector_bound hi hs.2
  have hw0 : 0 < ‖w‖ := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ‖w‖ / 2) hs.1
    (by norm_num : -(7 / 8 : ℝ) ≤ 0)
  have he : (‖w‖ / 2) ^ (-(7 / 8 : ℝ)) = (2 : ℝ) ^ (7 / 8 : ℝ) * ‖w‖ ^ (-(7 / 8 : ℝ)) := by
    rw [show ‖w‖ / 2 = (2 : ℝ)⁻¹ * ‖w‖ by ring,
      Real.mul_rpow (by norm_num) hw0.le, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_left hp latticeSectorConstant_nonneg
  unfold spectralDecayConstant
  nlinarith

theorem continuedSpectral_decay {b : ℝ} {w : ℂ} (hb : 0 < b)
    (him : w.im < 0) (hre : 0 ≤ w.re) (hn : 4 * b ≤ ‖w‖) :
    ‖continuedSpectral b w‖ ≤ spectralDecayConstant * ‖w‖ ^ (-(7 / 8 : ℝ)) := by
  have hi := (continuedSpectral_integrand_continuous hb.le (Or.inl him)).intervalIntegrable
    (μ := volume) 0 Real.pi
  have hI : ‖∫ θ in (0 : ℝ)..Real.pi, continuedLattice (w - (b * Real.cos θ : ℝ))‖ ≤
      Real.pi * (spectralDecayConstant * ‖w‖ ^ (-(7 / 8 : ℝ))) := by
    calc
      _ ≤ ∫ θ in (0 : ℝ)..Real.pi, ‖continuedLattice (w - (b * Real.cos θ : ℝ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
      _ ≤ ∫ _θ in (0 : ℝ)..Real.pi, spectralDecayConstant * ‖w‖ ^ (-(7 / 8 : ℝ)) := by
        apply intervalIntegral.integral_mono Real.pi_pos.le hi.norm intervalIntegrable_const
        exact continuedLattice_spectral_bound hb him hre hn
      _ = _ := by simp; ring
  unfold continuedSpectral
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr Real.pi_pos.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul] using h

end AperyMoments
