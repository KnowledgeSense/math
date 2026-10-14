import Dowling.DowlingApexComponentSums
import Dowling.DowlingJointlessBase

noncomputable section
namespace Dowling
open Finset

theorem apexNormalizedWeight_pos (n k j : ℕ) (hn : 2≤n) (hk : 1≤k)
    (hkn : k≤n) (hj : 2*j≤n) : 0<apexNormalizedWeight n k j := by
  rw [apexNormalizedWeight_components n k j hk hkn hj]
  apply mul_pos (by exact_mod_cast (show 0<k by omega))
  apply sum_pos'
  · intro h hh
    have hhj : h≤j := by have := mem_range.mp hh; omega
    exact mul_nonneg (apexAttenuation_nonneg n k h hk hkn (by omega))
      (mul_nonneg (apexComponentCoefficient_pos n h (by omega)).le (apexF_nonneg n h j hj))
  · refine ⟨0,by simp,?_⟩
    simp only [apexAttenuation,ite_true,apexComponent,apexComponentCoefficient,
      apexF_zero_component,mul_one,one_mul]
    positivity

theorem apexNormalizedWeight_budget_transfer (n k j : ℕ) (B : ℝ) (hB : 0≤B)
    (hk : 1≤k) (hkn : k≤n) (hj : 1≤j) (hjn : 2*(j+1)≤n)
    (hbudget : apexNormalizedWeight n 1 (j-1)+apexNormalizedWeight n 1 (j+1)-
      2*apexNormalizedWeight n 1 j≤B*apexNormalizedWeight n 1 j) :
    apexNormalizedWeight n k (j-1)+apexNormalizedWeight n k (j+1)-
      2*apexNormalizedWeight n k j≤B*apexNormalizedWeight n k j := by
  let N := j+2
  have hN : 2*(N-1)≤n := by dsimp [N]; omega
  have hsum : (∑h∈range N,apexComponentDefect n j B h)≤0 := by
    rw [apexNormalizedWeight_one_components n (j-1) N (by omega) (by dsimp [N]; omega) hN,
      apexNormalizedWeight_one_components n (j+1) N (by omega) (by dsimp [N]; omega) hN,
      apexNormalizedWeight_one_components n j N (by omega) (by dsimp [N]; omega) hN] at hbudget
    simp only [apexComponentDefect,sum_add_distrib,sum_sub_distrib,← mul_sum]
    linarith
  have ht := apex_single_crossing_attenuation (apexComponentDefect n j B) (apexAttenuation n k) N
    (fun h hh=>apexAttenuation_nonneg n k h hk hkn (by omega))
    (fun i h hih hh=>apexAttenuation_antitone n k i h (by omega) hk hkn hih (by omega))
    (fun i h hih _ hi=>apexComponentDefect_single_crossing n j B hB hj hjn i h hih hi) hsum
  have heq : (∑h∈range N,apexAttenuation n k h*apexComponentDefect n j B h)=
      (∑h∈range N,apexAttenuation n k h*apexComponent n h (j-1))+
      (∑h∈range N,apexAttenuation n k h*apexComponent n h (j+1))-
      (2+B)*(∑h∈range N,apexAttenuation n k h*apexComponent n h j) := by
    rw [mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro h hh
    unfold apexComponentDefect
    ring
  rw [heq] at ht
  rw [apexNormalizedWeight_components_extended n k (j-1) N hk hkn (by omega) (by dsimp [N]; omega),
    apexNormalizedWeight_components_extended n k (j+1) N hk hkn hjn (by dsimp [N]; omega),
    apexNormalizedWeight_components_extended n k j N hk hkn (by omega) (by dsimp [N]; omega)]
  have hmul := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤k by positivity) ht
  nlinarith

end Dowling
