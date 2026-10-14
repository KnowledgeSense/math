import AperyMoments.OuterResolvent
import AperyMoments.ReciprocalSpectralCoefficients
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def densityCauchyTerm (h : ℝ→ℝ) (y : ℝ) (n : ℕ) (w : ℝ) : ℂ :=
  (h w:ℂ)*((w:ℂ)/(y:ℂ))^n/(y:ℂ)

theorem densityCauchyTerm_integral (h : ℝ→ℝ) (y : ℝ) (n : ℕ) :
    (∫ w:ℝ,densityCauchyTerm h y n w)=((∫ w:ℝ,(w^n*h w : ℝ)):ℂ)/(y:ℂ)^(n+1) := by
  have he (w:ℝ) : densityCauchyTerm h y n w=((w^n*h w:ℝ):ℂ)/(y:ℂ)^(n+1) := by
    simp only [densityCauchyTerm,Complex.ofReal_mul,Complex.ofReal_pow,div_pow,pow_succ]
    ring
  simp_rw [he]
  rw [integral_div,integral_complex_ofReal]

theorem densityCauchy_hasSum {h : ℝ→ℝ} (hh : Measurable h) (hi : Integrable h)
    (hn : ∀w,0≤h w) {B y : ℝ} (hB : 0≤B) (hy : B<y)
    (hs : ∀w,h w≠0→|w|≤B) :
    HasSum (fun n => ((∫ w:ℝ,(w^n*h w : ℝ)):ℂ)/(y:ℂ)^(n+1)) (densityCauchyTransform h (y:ℂ)) := by
  have hyp : 0<y := hB.trans_lt hy
  have hyr : B/y<1 := (div_lt_one hyp).mpr hy
  have hsum := summable_geometric_of_lt_one (div_nonneg hB hyp.le) hyr
  have hlim (w:ℝ) : HasSum (fun n => densityCauchyTerm h y n w) (densityCauchyKernel h (y:ℂ) w) := by
    by_cases hw : h w=0
    · simp [densityCauchyTerm,densityCauchyKernel,hw]
    · have hratio : ‖(w:ℂ)/(y:ℂ)‖<1 := by
        rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hyp]
        exact (div_lt_one hyp).mpr ((hs w hw).trans_lt hy)
      have hh := (hasSum_geometric_of_norm_lt_one hratio).mul_left ((h w:ℂ)/(y:ℂ))
      convert hh using 1
      · funext n; unfold densityCauchyTerm; ring
      · unfold densityCauchyKernel
        have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hyp.ne'
        have hd : (y : ℂ)*(1-(w : ℂ)/(y : ℂ)) = (y : ℂ)-w := by field_simp
        rw [← hd]
        simp only [div_eq_mul_inv, mul_inv]
        ring
  have hbound (n:ℕ) (w:ℝ) : ‖densityCauchyTerm h y n w‖≤h w*(B/y)^n/y := by
    by_cases hw : h w=0
    · simp [densityCauchyTerm,hw]
    · simp only [densityCauchyTerm,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hyp,abs_of_nonneg (hn w)]
      gcongr
      · exact hn w
      · exact hs w hw
  have he := hasSum_integral_of_dominated_convergence
    (F := fun n w => densityCauchyTerm h y n w)
    (f := densityCauchyKernel h (y:ℂ)) (fun n w => h w*(B/y)^n/y)
    (fun n => (show Measurable (densityCauchyTerm h y n) by
      unfold densityCauchyTerm
      exact ((Complex.continuous_ofReal.measurable.comp hh).mul ((by fun_prop : Measurable (fun w:ℝ => (w:ℂ)/(y:ℂ))).pow_const n)).div_const _).aestronglyMeasurable)
    (fun n => Eventually.of_forall (hbound n))
    (Eventually.of_forall (fun w => (hsum.mul_left (h w)).div_const y))
    (by
      simp_rw [tsum_div_const,tsum_mul_left]
      exact (hi.mul_const _).div_const y)
    (Eventually.of_forall hlim)
  simpa only [densityCauchyTerm_integral,densityCauchyTransform] using he

end AperyMoments
