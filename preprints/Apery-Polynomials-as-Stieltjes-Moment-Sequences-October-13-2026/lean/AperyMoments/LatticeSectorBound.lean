import AperyMoments.LowerEllipticSector
import AperyMoments.LatticeContinuation

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def latticeSectorConstant : ℝ :=
  (((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * 8 / (2 * Real.pi ^ 2)) * (4 : ℝ) ^ (7 / 8 : ℝ)

theorem latticeSectorConstant_nonneg : 0 ≤ latticeSectorConstant := by
  unfold latticeSectorConstant
  positivity

theorem lowerEllipticIntegral_sector_decay {z : ℂ} (him : z.im < 0)
    (hz : -‖z‖ / 2 ≤ z.re) :
    ‖lowerEllipticIntegral z‖ ≤ (((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * 8) *
      ‖z‖ ^ (-(7 / 8 : ℝ)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at him
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hK := ellipticK_negative_large_bound (sq_pos_of_pos hR)
  rw [← Real.rpow_natCast_mul hR.le] at hK
  norm_num at hK
  have hh := mul_le_mul_of_nonneg_left hK (sq_nonneg ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))))
  nlinarith [lowerEllipticIntegral_sector_bound him hz]

theorem continuedLattice_sector_bound {z : ℂ} (him : z.im < 0)
    (hz : -‖z‖ / 2 ≤ z.re) :
    ‖continuedLattice z‖ ≤ latticeSectorConstant * ‖z‖ ^ (-(7 / 8 : ℝ)) := by
  have hn : ‖z / 4‖ = ‖z‖ / 4 := by rw [norm_div]; norm_num
  have him' : (z / 4).im < 0 := by simpa using div_neg_of_neg_of_pos him (by norm_num : (0 : ℝ) < 4)
  have hz' : -‖z / 4‖ / 2 ≤ (z / 4).re := by
    have hr : (z / 4).re = z.re / 4 := by simp
    rw [hn, hr]
    linarith
  have h := lowerEllipticIntegral_sector_decay him' hz'
  rw [hn] at h
  have he : (‖z‖ / 4) ^ (-(7 / 8 : ℝ)) = (4 : ℝ) ^ (7 / 8 : ℝ) * ‖z‖ ^ (-(7 / 8 : ℝ)) := by
    rw [show ‖z‖ / 4 = (4 : ℝ)⁻¹ * ‖z‖ by ring,
      Real.mul_rpow (by norm_num) (norm_nonneg z), Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [he] at h
  unfold continuedLattice
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2)]
  have hd := div_le_div_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.pi ^ 2)
  unfold latticeSectorConstant
  convert hd using 1; ring

end AperyMoments
