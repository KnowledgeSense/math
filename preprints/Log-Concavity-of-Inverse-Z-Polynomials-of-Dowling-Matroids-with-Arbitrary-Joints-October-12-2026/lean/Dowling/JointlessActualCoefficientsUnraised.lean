import Dowling.JointlessActualCoefficientsEuler
import Dowling.DowlingJointlessDefinitions

noncomputable section
namespace Dowling
open PowerSeries

theorem quadraticWeightSeries_sub (v w : ℕ→ℝ) :
    quadraticWeightSeries (fun j => v j-w j)=quadraticWeightSeries v-quadraticWeightSeries w := by
  apply PowerSeries.ext
  intro d
  simp only [map_sub,quadraticWeightSeries,coeff_mk]
  split <;> simp [sub_mul]

theorem quadraticWeightSeries_scalar (c : ℝ) (v : ℕ→ℝ) :
    quadraticWeightSeries (fun j => c*v j)=C (Polynomial.C c)*quadraticWeightSeries v := by
  apply PowerSeries.ext
  intro d
  simp only [coeff_C_mul,quadraticWeightSeries,coeff_mk]
  split <;> simp [map_mul,mul_assoc]

theorem quadraticWeightSeries_corrected (c : ℝ) :
    quadraticWeightSeries (dowlingQuadraticWeight c)=dowlingCorrectedQuadratic c := by
  apply PowerSeries.ext
  intro d
  by_cases he : d%2=0
  · rw [show d=2*(d/2) by omega,quadraticWeightSeries_even,dowlingCorrectedQuadratic_coeff_even]
  · rw [show d=2*(d/2)+1 by omega,quadraticWeightSeries_odd,dowlingCorrectedQuadratic_coeff_odd]

theorem quadraticWeightSeries_shift_twice (v : ℕ→ℝ) :
    C (Polynomial.X^2)*X^4*quadraticWeightSeries v=
      quadraticWeightSeries (fun j => if j<2 then 0 else v (j-2)) := by
  have he : C (Polynomial.X^2)*X^4*quadraticWeightSeries v=
      C Polynomial.X*X^2*(C Polynomial.X*X^2*quadraticWeightSeries v) := by rw [map_pow]; ring
  rw [he,quadraticWeightSeries_shift,quadraticWeightSeries_shift]
  apply congrArg quadraticWeightSeries
  funext j
  cases j with
  | zero => simp
  | succ j =>
    cases j with
    | zero => simp
    | succ j => simp

theorem jointlessUnraisedKernel_weighted (a : ℝ) (n : ℕ) :
    jointlessUnraisedKernel a n=quadraticWeightedKernel (jointlessUnraisedWeight a n) a := by
  have he : quadraticWeightSeries (jointlessUnraisedWeight a n)=
      dowlingCorrectedQuadratic (((n : ℝ)+a)/2)-
      C (Polynomial.C (a*n/(n+a-1)))*dowlingCorrectedQuadratic (((n : ℝ)+a-1)/2)-
      C (Polynomial.C (a*(1-a)))*C Polynomial.X*X^2*dowlingCorrectedQuadratic (((n : ℝ)+a-1)/2)-
      C (Polynomial.C (a^2/3))*C (Polynomial.X^2)*X^4*dowlingCorrectedQuadratic (((n : ℝ)+a-1)/2) := by
    have hd : jointlessUnraisedWeight a n=(fun j =>
        dowlingQuadraticWeight (((n : ℝ)+a)/2) j-
        (a*n/(n+a-1))*dowlingQuadraticWeight (((n : ℝ)+a-1)/2) j-
        a*(1-a)*(if j=0 then 0 else dowlingQuadraticWeight (((n : ℝ)+a-1)/2) (j-1))-
        (a^2/3)*(if j<2 then 0 else dowlingQuadraticWeight (((n : ℝ)+a-1)/2) (j-2))) := by
      funext j
      simp only [jointlessUnraisedWeight,mul_ite,mul_zero]
    rw [hd,quadraticWeightSeries_sub,quadraticWeightSeries_sub,quadraticWeightSeries_sub,
      quadraticWeightSeries_scalar,quadraticWeightSeries_scalar,quadraticWeightSeries_scalar,
      ← quadraticWeightSeries_shift,← quadraticWeightSeries_shift_twice]
    simp only [quadraticWeightSeries_corrected]
    ring
  rw [quadraticWeightedKernel,he]
  dsimp [jointlessUnraisedKernel,dowlingFixedKernel,dowlingFixedGaussianProduct,dowlingCorrectedQuadratic]
  ring

theorem jointlessSeries_unraised_coeff (m : ℝ) (hm : m≠0) (n k : ℕ)
    (hn : (n : ℝ)+m⁻¹-1≠0) :
    (coeff n (jointlessSeries m)).coeff k=m^n*
      quadraticWeightedRow (jointlessUnraisedWeight m⁻¹ n) m⁻¹ n k := by
  rw [jointlessSeries_raw_kernel m hm n,jointlessRawKernel_coeff_eq m⁻¹ n hn,
    jointlessUnraisedKernel_weighted,Polynomial.coeff_C_mul,quadraticWeightedKernel_coeff]

end Dowling
