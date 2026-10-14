import Dowling.ActualApexWeightsUniqueness

noncomputable section
namespace Dowling
open PowerSeries

def apexSingleUnraised (n j : ℕ) : ℝ :=
  dowlingQuadraticWeight ((n : ℝ)/2) j+
    if j=0 then 0 else dowlingQuadraticWeight ((n : ℝ)/2) (j-1)

def apexSingleRaised (n j : ℕ) : ℝ :=
  (1/(n : ℝ))*(apexSingleUnraised n j/(n+1-2*j)-
    if j=0 then 0 else apexSingleUnraised n (j-1)/(n+1-2*(j-1)))

theorem quadraticWeightSeries_add (v w : ℕ→ℝ) :
    quadraticWeightSeries (fun j => v j+w j)=quadraticWeightSeries v+quadraticWeightSeries w := by
  apply PowerSeries.ext
  intro d
  simp only [map_add,quadraticWeightSeries,coeff_mk]
  split <;> simp [add_mul]

theorem apexSingleUnraised_kernel (n : ℕ) :
    quadraticWeightedKernel (apexSingleUnraised n) 1=
      (1+PowerSeries.C Polynomial.X*PowerSeries.X^2)*dowlingFixedKernel ((n : ℝ)/2) 1 := by
  change quadraticWeightSeries (fun j => dowlingQuadraticWeight ((n : ℝ)/2) j+
    if j=0 then 0 else dowlingQuadraticWeight ((n : ℝ)/2) (j-1))*_= _
  rw [quadraticWeightSeries_add,← quadraticWeightSeries_shift,quadraticWeightSeries_corrected]
  dsimp [dowlingFixedKernel,dowlingFixedGaussianProduct,dowlingCorrectedQuadratic]
  ring

theorem apexSingleUnraised_coeff (n : ℕ) (hn : 0<n) :
    coeff n (quadraticWeightedKernel (apexSingleUnraised n) 1)=
      (1+Polynomial.X)*coeff (n-1) (dowlingFixedKernel ((n : ℝ)/2) 1) := by
  have hz := dowlingFixedKernel_lower_coeff 1 n (by norm_num; exact_mod_cast hn.ne')
  norm_num at hz
  have he : (1+PowerSeries.C Polynomial.X*PowerSeries.X^2)*dowlingFixedKernel ((n : ℝ)/2) 1=
      PowerSeries.C (1+Polynomial.X)*PowerSeries.X*dowlingFixedKernel ((n : ℝ)/2) 1+
      dowlingFixedKernel ((n : ℝ)/2) 0 := by
    have h := dowlingFixedKernel_lower_exponent ((n : ℝ)/2) 1
    norm_num at h
    rw [h]
    simp only [map_add,map_one]
    ring
  rw [apexSingleUnraised_kernel,he,map_add,hz,add_zero,mul_assoc,coeff_C_mul]
  have hc : coeff n (PowerSeries.X*dowlingFixedKernel ((n : ℝ)/2) 1)=
      coeff (n-1) (dowlingFixedKernel ((n : ℝ)/2) 1) := by
    simpa only [show n-1+1=n by omega] using
      coeff_succ_X_mul (n-1) (dowlingFixedKernel ((n : ℝ)/2) 1)
  exact congrArg (fun p : Polynomial ℝ => (1+Polynomial.X)*p) hc

theorem fullY_unit_kernel (n : ℕ) :
    (fullY Unit n).map (Int.castRingHom ℝ)=
      Polynomial.C (n.factorial : ℝ)*coeff n (dowlingFixedKernel (((n : ℝ)+1)/2) 1) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,dowlingFixedKernel_coeff]
  change ((fullY Unit n).coeff k : ℝ)=_
  rw [fullY_coeff_real]
  simp only [Fintype.card_unique,Nat.cast_one,one_pow,mul_one,inv_one]
  rfl

end Dowling
