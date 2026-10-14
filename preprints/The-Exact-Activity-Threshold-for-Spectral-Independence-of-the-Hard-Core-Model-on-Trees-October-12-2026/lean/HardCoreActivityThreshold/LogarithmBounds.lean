import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset
namespace HardCoreActivityThreshold
open scoped BigOperators

def logApproximation (a : ℚ) (n : ℕ) : ℚ :=
  2*∑i∈range n,((a-1)/(a+1))^(2*i+1)/(2*i+1)
def logRemainder (a : ℚ) (n : ℕ) : ℚ :=
  2*((a-1)/(a+1))^(2*n+1)/(1-((a-1)/(a+1))^2)

theorem logApproximation_bounds (a : ℚ) (ha : 1≤a) (n : ℕ) :
    (logApproximation a n : ℝ)≤Real.log a ∧
      Real.log a≤(logApproximation a n+logRemainder a n : ℚ) := by
  have ha' : (1 : ℝ)≤a := by exact_mod_cast ha
  let w : ℝ := ((a : ℝ)-1)/((a : ℝ)+1)
  have hw0 : 0≤w := div_nonneg (by linarith) (by linarith)
  have hw1 : w<1 := by
    dsimp [w]
    apply (div_lt_one (by linarith)).mpr
    linarith
  have he : (1+w)/(1-w)=(a : ℝ) := by
    dsimp [w]
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hw0 hw1 n
  have hhi := Real.log_div_le_sum_range_add hw0 hw1 n
  rw [he] at hlo hhi
  have hlo' : 2*(∑i∈range n,w^(2*i+1)/(2*i+1))≤Real.log a := by linarith
  have hhi' : Real.log a≤2*(∑i∈range n,w^(2*i+1)/(2*i+1))+2*w^(2*n+1)/(1-w^2) := by
    have hm := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ)≤2)
    convert hm using 1 <;> ring
  constructor
  · convert hlo' using 1; simp [logApproximation,w]
  · convert hhi' using 1; simp [logApproximation,logRemainder,w]

def scaledLogLower (a : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  logApproximation (a*2^k) n-(k : ℚ)*(if 0≤k then logApproximation 2 n+logRemainder 2 n else logApproximation 2 n)
def scaledLogUpper (a : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  logApproximation (a*2^k) n+logRemainder (a*2^k) n-(k : ℚ)*(if 0≤k then logApproximation 2 n else logApproximation 2 n+logRemainder 2 n)

theorem scaledLog_bounds (a : ℚ) (k : ℤ) (n : ℕ) (ha : 0<a) (hu : 1≤a*2^k) :
    (scaledLogLower a k n : ℝ)≤Real.log a ∧ Real.log a≤(scaledLogUpper a k n : ℝ) := by
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  have hp : (0 : ℝ)<(2 : ℝ)^k := by positivity
  have he : Real.log ((a*2^k : ℚ) : ℝ)=Real.log (a : ℝ)+(k : ℝ)*Real.log 2 := by
    push_cast
    rw [Real.log_mul (ne_of_gt ha') (ne_of_gt hp),Real.log_zpow]
  have h := logApproximation_bounds (a*2^k) hu n
  have h2 := logApproximation_bounds 2 (by norm_num) n
  rw [he] at h
  by_cases hk : 0≤k
  · have hk' : (0 : ℝ)≤k := by exact_mod_cast hk
    have hm0 := mul_le_mul_of_nonneg_left h2.1 hk'
    have hm1 := mul_le_mul_of_nonneg_left h2.2 hk'
    simp only [scaledLogLower,scaledLogUpper,ite_eq_left hk]
    push_cast at *
    constructor <;> linarith
  · have hk' : (k : ℝ)≤0 := by exact_mod_cast (le_of_not_ge hk)
    have hm0 := mul_le_mul_of_nonpos_left h2.1 hk'
    have hm1 := mul_le_mul_of_nonpos_left h2.2 hk'
    simp only [scaledLogLower,scaledLogUpper,ite_eq_right hk]
    push_cast at *
    constructor <;> linarith

end HardCoreActivityThreshold
