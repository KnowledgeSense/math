import AperyMoments.PairedCauchyKernel
import AperyMoments.ResolventShiftedMajorant

noncomputable section
namespace AperyMoments
open Complex

theorem pairedMomentKernel_shifted_majorant {α δ R : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hδ : 0<δ) (hR : 0<R) (hz : 0<z.im) :
    ∃ C:ℝ, 0≤C ∧ ∀ y t:ℝ, 0<y → y≤α/2 → y≤1 → y≤z.im/2 →
      δ≤t → t≤R → t≠horizontalCritical α y →
      ‖pairedMomentKernel α y z t‖≤C*(1+‖t-horizontalCritical α y‖^(-(1/3:ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := momentTransform_shifted_majorant hα hα1 hδ hR
  let D := 4/z.im+8/z.im^2
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨D*C,mul_nonneg hD hC,?_⟩
  intro y t hy hyα hy1 hyz htδ htR hne
  have hk := pairedCauchyKernel_bound hz hy.le hyz
    (momentTransform α ((t:ℂ)+y*I)) t
  have hw := hbound y t hy hyα hy1 htδ htR hne
  have hA : 0≤|(momentTransform α ((t:ℂ)+y*I)).im| := abs_nonneg _
  have hB : 0≤y*‖momentTransform α ((t:ℂ)+y*I)‖ := by positivity
  have h1 : 0≤4/z.im := by positivity
  have h2 : 0≤8/z.im^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hw hD
  change ‖pairedCauchyKernel (momentTransform α ((t:ℂ)+y*I)) z t y‖≤_
  dsimp [D] at hm ⊢
  have hk' : ‖pairedCauchyKernel (momentTransform α ((t:ℂ)+y*I)) z t y‖≤
      (4/z.im)*|(momentTransform α ((t:ℂ)+y*I)).im|+
      (8/z.im^2)*(y*‖momentTransform α ((t:ℂ)+y*I)‖) := by convert hk using 1; ring
  nlinarith [mul_nonneg h1 hB,mul_nonneg h2 hA]

end AperyMoments
