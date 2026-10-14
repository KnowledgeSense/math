import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace CircleKernel

theorem inverse_power_series (k : ℕ) :
    HasFPowerSeriesAt (fun x:ℝ=>1/(1+x)^(k+1))
      (FormalMultilinearSeries.ofScalars ℝ (fun j=>(-1:ℝ)^j*((k+j).choose k:ℝ))) 0 := by
  have hp := (Real.one_div_sub_pow_hasFPowerSeriesOnBall_zero k (r:=1) (by norm_num)).hasFPowerSeriesAt
  simp only [one_pow,inv_one,one_mul] at hp
  have hp' : HasFPowerSeriesAt (fun x:ℝ=>1/(1-x)^(k+1))
      (FormalMultilinearSeries.ofScalars ℝ (fun j=>((k+j).choose k:ℝ)))
      ((-ContinuousLinearMap.id ℝ ℝ) 0) := by simpa using hp
  have h := hp'.compContinuousLinearMap
  simpa only [Function.comp_def,neg_apply,ContinuousLinearMap.id_apply,
    sub_neg_eq_add,FormalMultilinearSeries.ofScalars_comp_neg_id] using h

theorem inverse_power_taylor (k M : ℕ) :
    (fun x:ℝ=>1/(1+x)^(k+1)-∑j∈Finset.range M,(-1:ℝ)^j*((k+j).choose k:ℝ)*x^j)
      =O[𝓝 0] (fun x:ℝ=>‖x‖^M) := by
  have h := (inverse_power_series k).isBigO_sub_partialSum_pow M
  simpa only [zero_add,FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using h

theorem log_one_add_taylor (M : ℕ) :
    (fun x:ℝ=>Real.log (1+x)-∑j∈Finset.range M,(-(-1:ℝ)^j/(j:ℝ))*x^j)
      =O[𝓝 0] (fun x:ℝ=>‖x‖^M) := by
  have h := hasFPowerSeriesAt_log_one_add.isBigO_sub_partialSum_pow M
  simpa only [zero_add,FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using h

end CircleKernel
