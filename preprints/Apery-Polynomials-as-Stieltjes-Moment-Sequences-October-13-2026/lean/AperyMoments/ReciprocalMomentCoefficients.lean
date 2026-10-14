import AperyMoments.MomentReconstructionReal
import AperyMoments.PowerSeriesCoefficientUniqueness

set_option maxHeartbeats 400000
noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def reciprocalDensityMoment (α : ℝ) (n : ℕ) : ℝ :=
  ∫ t:ℝ,t^n*reciprocalMomentDensity α t

theorem reciprocalDensityMoment_hasSum {α R : ℝ}
    (hα : 0<α) (hα1 : α≤1) (hR : 64<R) :
    HasSum (fun n=>(reciprocalDensityMoment α n:ℂ)/(R:ℂ)^(n+1))
      (densityCauchyTransform (reciprocalMomentDensity α) (R:ℂ)) := by
  have hs := densityCauchy_hasSum (reciprocalMomentDensity_measurable α)
    (reciprocalMomentDensity_integrable hα hα1) (reciprocalMomentDensity_nonneg hα.le)
    (by norm_num : (0:ℝ)≤64) hR (fun t ht=>by
      have hh : t∈Icc 0 64 := by
        by_contra hn
        exact ht (reciprocalMomentDensity_support hα hα1 hn)
      rw [abs_of_nonneg hh.1]
      exact hh.2)
  simp_rw [integral_complex_ofReal] at hs
  exact hs

theorem powerSeries_hasSum_of_reciprocal {a : ℕ→ℝ} {t : ℝ} {G : ℂ} (ht : 0<t)
    (hs : HasSum (fun n=>(a n:ℂ)/((t⁻¹:ℝ):ℂ)^(n+1)) G) :
    HasSum (fun n=>a n*t^n) (G.re/t) := by
  have hr := Complex.hasSum_re hs
  simp only [← Complex.ofReal_pow,← Complex.ofReal_div,Complex.ofReal_re] at hr
  convert hr.div_const t using 1
  funext n
  simp only [inv_pow,pow_succ,div_eq_mul_inv]
  field_simp

theorem reciprocalDensityMoment_eq {α : ℝ} (hα : 0<α) (hα1 : α≤1) (n : ℕ) :
    reciprocalDensityMoment α n=reciprocalPolynomial n α := by
  have hd (t : ℝ) (ht : 0<t) (ht1 : t≤(1/1024:ℝ)) : 256<t⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) ht]
    linarith
  have hM (t : ℝ) (ht : 0<t) (ht1 : t≤(1/1024:ℝ)) :
      HasSum (fun n=>reciprocalDensityMoment α n*t^n)
        ((densityCauchyTransform (reciprocalMomentDensity α) ((t⁻¹:ℝ):ℂ)).re/t) :=
    powerSeries_hasSum_of_reciprocal (a := reciprocalDensityMoment α) (t := t)
      (G := densityCauchyTransform (reciprocalMomentDensity α) ((t⁻¹:ℝ):ℂ)) ht
      (reciprocalDensityMoment_hasSum (R := t⁻¹) hα hα1
      (by have := hd t ht ht1; linarith : 64<t⁻¹))
  have hP (t : ℝ) (ht : 0<t) (ht1 : t≤(1/1024:ℝ)) :
      HasSum (fun n=>reciprocalPolynomial n α*t^n)
        ((densityCauchyTransform (reciprocalMomentDensity α) ((t⁻¹:ℝ):ℂ)).re/t) :=
    powerSeries_hasSum_of_reciprocal (a := fun n=>reciprocalPolynomial n α) (t := t)
      (G := densityCauchyTransform (reciprocalMomentDensity α) ((t⁻¹:ℝ):ℂ)) ht
      (reciprocalMomentCauchy_hasSum (R := t⁻¹) hα hα1 (hd t ht ht1))
  have he := scalar_powerSeries_coeff_unique (a := reciprocalDensityMoment α)
    (b := fun n=>reciprocalPolynomial n α) (by norm_num : (0:ℝ)<1/1024)
    (hM _ (by norm_num) le_rfl).summable (hP _ (by norm_num) le_rfl).summable
    (fun t ht htr=>(hM t ht htr.le).tsum_eq.trans (hP t ht htr.le).tsum_eq.symm)
  exact congrFun he n

end AperyMoments
