import MeanMaximumForests.Data.Roots0
import MeanMaximumForests.Data.Roots1

namespace MeanMaximumForests.Release
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root0_sign : ∀ i : Fin 32, 0 ≤ ((generators0 i).root100 false).x := by decide
theorem root1_sign : ∀ i : Fin 331, 0 ≤ ((generators1 i).root100 true).x := by decide

theorem unscale_mem {G : Set ConeVector} {v : ConeVector} {d : ℝ}
    (hd : 0 < d) (h : GeneratedCone G (scale d v)) : GeneratedCone G v := by
  have hs := GeneratedCone.scale d⁻¹ (inv_nonneg.mpr hd.le) h
  rw [scale_unscale _ (ne_of_gt hd)] at hs
  exact hs

theorem root0_mem (i : Fin 32) :
    GeneratedCone (generatorSet generators1) (plant (47 / 100) false (generators0 i).toReal) := by
  have h := CertificateData.sound _ _ _ (roots0_valid i)
  rw [IntegerVector.toReal_root100] at h
  exact unscale_mem (by norm_num) h

theorem root1_mem (i : Fin 331) :
    GeneratedCone (generatorSet generators0) (plant (47 / 100) true (generators1 i).toReal) := by
  have h := CertificateData.sound _ _ _ (roots1_valid i)
  rw [IntegerVector.toReal_root100] at h
  exact unscale_mem (by norm_num) h

theorem root_sign_real (v : IntegerVector) (f : Bool) (h : 0 ≤ (v.root100 f).x) :
    0 ≤ (plant (47 / 100) f v.toReal).x := by
  have hc : (0 : ℝ) ≤ (v.root100 f).toReal.x := Int.cast_nonneg h
  rw [IntegerVector.toReal_root100] at hc
  exact nonneg_of_mul_nonneg_right hc (by norm_num : (0 : ℝ) < 100)

end MeanMaximumForests.Release
