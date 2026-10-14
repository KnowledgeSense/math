import AperyMoments.ReciprocalTransformSeriesBinomial

noncomputable section
namespace AperyMoments
open Complex Finset
open scoped Topology

theorem reciprocalEvenTerm_eq {α R : ℝ} (hR : 0<R) (m : ℕ) :
    reciprocalEvenTerm α R m=
      ((spectralMomentCoefficient m α:ℂ)/(reciprocalRadius α R:ℂ)^(2*m+1))/
        (Real.sqrt R:ℂ) := by
  have hs0 : (Real.sqrt R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hR))
  have hR0 : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hs : (Real.sqrt R:ℂ)^2=(R:ℂ) := by exact_mod_cast Real.sq_sqrt hR.le
  have hy : (reciprocalRadius α R:ℂ)=(Real.sqrt R:ℂ)*(1+(α:ℂ)/(R:ℂ)) := by
    simp only [reciprocalRadius,Complex.ofReal_add,Complex.ofReal_div]
    field_simp
    linear_combination -(α:ℂ) * hs
  rw [hy]
  have hp : (Real.sqrt R:ℂ)^(2*m+1)*(Real.sqrt R:ℂ)=(R:ℂ)^(m+1) := by
    rw [← pow_succ,show 2*m+1+1=2*(m+1) by omega,pow_mul,hs]
  simp only [reciprocalEvenTerm,mul_pow,div_div]
  congr 1
  rw [mul_assoc, mul_comm ((1+(α:ℂ)/(R:ℂ))^(2*m+1)),← mul_assoc,hp]

theorem reciprocalEvenTerm_hasSum {α R : ℝ} (hα : 0<α) (hα1 : α≤1)
    (hR : 256<R) : HasSum (reciprocalEvenTerm α R) (outerResolvent α (R:ℂ)) := by
  have hR0 : 0<R := by linarith
  have hs := (spectralCauchy_even_hasSum hα.le
    (reciprocalRadius_large hα hα1 (by linarith : 64<R))).div_const (Real.sqrt R:ℂ)
  simpa only [← reciprocalEvenTerm_eq hR0,outerResolvent,reciprocalMap_ofReal α hR0.le,
    complexSqrt_ofReal_nonneg hR0.le] using hs

end AperyMoments
