import Dowling.DowlingApexChoose

noncomputable section
namespace Dowling
open Finset

theorem apex_decreasing_average_step (f : ℕ→ℝ) (n : ℕ) (hn : 0<n)
    (hf : ∀i,i<n→f n≤f i) :
    (∑i∈range (n+1),f i)/(n+1)≤(∑i∈range n,f i)/n := by
  have hsum : (n:ℝ)*f n≤∑i∈range n,f i := by
    calc
      _ = ∑i∈range n,f n := by simp
      _ ≤ _ := sum_le_sum (fun i hi=>hf i (mem_range.mp hi))
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [sum_range_succ]
  apply (div_le_div_iff₀ (by positivity) hnR).mpr
  nlinarith

theorem apexChooseRatio_defect_sum (A B z : ℕ) (hAB : A<B) (hz : z≤B) :
    1-apexChooseRatio A B z=
      ((B-A:ℕ):ℝ)/B*∑i∈range z,apexChooseRatio A (B-1) i := by
  induction z with
  | zero => simp [apexChooseRatio_zero]
  | succ z ih =>
    have hdiff := apexChooseRatio_difference A B z hAB (by omega)
    have hprev := ih (by omega)
    rw [sum_range_succ]
    change 1-apexChooseRatio A B (z+1)=_
    linarith

theorem apexChooseRatio_antitone (A B i j : ℕ) (hAB : A≤B) (hij : i≤j) (hj : j≤B) :
    apexChooseRatio A B j≤apexChooseRatio A B i := by
  induction hij with
  | refl => rfl
  | @step j hij ih =>
    exact (apexChooseRatio_antitone_step A B j hAB (by omega)).trans (ih (by omega))

theorem apexChooseRatio_defect_average_step (A B z : ℕ) (hAB : A<B)
    (hz : 0<z) (hzB : z<B) :
    (1-apexChooseRatio A B (z+1))/(z+1)≤(1-apexChooseRatio A B z)/z := by
  rw [apexChooseRatio_defect_sum A B (z+1) hAB (by omega),
    apexChooseRatio_defect_sum A B z hAB (by omega)]
  have h := apex_decreasing_average_step (apexChooseRatio A (B-1)) z hz
    (fun i hi=>apexChooseRatio_antitone A (B-1) i z (by omega) (by omega) (by omega))
  have hc : 0≤((B-A:ℕ):ℝ)/B := by positivity
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h hc

theorem apexChooseRatio_defect_average_antitone (A B i j : ℕ) (hAB : A<B)
    (hi : 0 < i) (hij : i≤j) (hj : j≤B) :
    (1-apexChooseRatio A B j)/j ≤ (1-apexChooseRatio A B i)/i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    simpa only [Nat.cast_add,Nat.cast_one] using (apexChooseRatio_defect_average_step A B j hAB (by omega) (by omega)).trans
      (ih (by omega))

end Dowling
