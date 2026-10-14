import Dowling.DowlingJointlessBudgetOne
import Dowling.DowlingJointlessBudgetHalf
import Dowling.DowlingJointlessLower

noncomputable section
namespace Dowling

 theorem jointless_large_budget_paid {μ r J : ℝ} (hμ : 5/2≤μ) (hr : 0<r)
    (hJ : 0<J) (hJμ : J≤μ+1/2) :
    (3*μ+1)/(2*μ^2*(2*μ+1))+53/(30*μ*r^2)<1/J+1/r^2 := by
  have hm0 : 0<μ := by linarith
  have hquad : 0<4*μ^2-3*μ-1 := by nlinarith [sq_nonneg (μ-1)]
  have hprod : 0<(μ+1/2)*(4*μ^2-3*μ-1) := mul_pos (by linarith) hquad
  have hfirst : (3*μ+1)/(2*μ^2*(2*μ+1))<1/(μ+1/2) := by
    apply (div_lt_div_iff₀ (by positivity) (by linarith)).mpr
    nlinarith
  have hrec : 1/(μ+1/2)≤1/J := (div_le_div_iff₀ (by linarith) hJ).mpr (by linarith)
  have hsecond : 53/(30*μ*r^2)<1/r^2 := by
    apply (div_lt_div_iff₀ (by positivity) (sq_pos_of_pos hr)).mpr
    have hp : 0<(30*μ-53)*r^2 := mul_pos (by linarith) (sq_pos_of_pos hr)
    nlinarith
  exact add_lt_add (hfirst.trans_le hrec) hsecond

 theorem jointless_half_budget_paid {μ r J : ℝ} (hμ : 11/4≤μ) (hr : 0<r)
    (hJ : 0<J) (hJμ : J≤μ+1/4) :
    3*(1/(12*μ*(2*μ+1))+7/(11*μ*r^2))<1/J+1/r^2 := by
  have hm0 : 0<μ := by linarith
  have hfirst : 3/(12*μ*(2*μ+1))<1/J := by
    apply (div_lt_div_iff₀ (by positivity) hJ).mpr
    nlinarith [sq_nonneg μ]
  have hsecond : 21/(11*μ*r^2)<1/r^2 := by
    apply (div_lt_div_iff₀ (by positivity) (sq_pos_of_pos hr)).mpr
    have hp : 0<(11*μ-21)*r^2 := mul_pos (by linarith) (sq_pos_of_pos hr)
    nlinarith
  have heq : 3*(1/(12*μ*(2*μ+1))+7/(11*μ*r^2))=
      3/(12*μ*(2*μ+1))+21/(11*μ*r^2) := by ring
  rw [heq]
  exact add_lt_add hfirst hsecond

 theorem jointlessNormalizedWeight_budget_large {a μ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 5/2≤μ) (j : ℕ) (hj : 2≤j) (hr : 1+a/2≤μ+1/2-j) :
    jointlessNormalizedWeight a μ (j-1)+jointlessNormalizedWeight a μ (j+1)-
      2*jointlessNormalizedWeight a μ j≤
      (1/((j : ℝ)+1)+1/(μ+1/2-j)^2)*jointlessNormalizedWeight a μ j := by
  have hr0 : 0<μ+1/2-j := by linarith
  have hlow := jointlessNormalizedWeight_gt_third ha.le (show a≤1/2 by linarith) hμ j hj (by linarith)
  have hb := jointless_difference_budget_large ha ha3 hμ j hj hr
  have hp := jointless_large_budget_paid hμ hr0 (show 0<(j : ℝ)+1 by positivity) (by linarith)
  have hL : 0<1/((j : ℝ)+1)+1/(μ+1/2-j)^2 := by positivity
  have hmul := mul_lt_mul_of_pos_left hlow hL
  nlinarith

 theorem jointlessNormalizedWeight_budget_one {a μ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 3/2≤μ) (hr : 1+a/2≤μ-1/2) :
    jointlessNormalizedWeight a μ 0+jointlessNormalizedWeight a μ 2-
      2*jointlessNormalizedWeight a μ 1≤
      (1/2+1/(μ-1/2)^2)*jointlessNormalizedWeight a μ 1 := by
  have hlow := jointlessNormalizedWeight_one_gt_half ha ha3 (by linarith : 1/2<μ)
  have hb := jointless_difference_budget_one ha ha3 hμ hr
  have hr0 : 0<μ-1/2 := by linarith
  have hinv : 0<1/(μ-1/2)^2 := by positivity
  have hmul := mul_lt_mul_of_pos_left hlow (show 0<(1/2 : ℝ)+1/(μ-1/2)^2 by positivity)
  have heq : (575/729 : ℝ)/(μ-1/2)^2=(575/729 : ℝ)*(1/(μ-1/2)^2) := by ring
  rw [heq] at hb
  nlinarith

 theorem jointlessNormalizedWeight_budget_half {μ : ℝ} (hμ : 11/4≤μ)
    (j : ℕ) (hj : 2≤j) (hr : 5/4≤μ+1/2-j) :
    jointlessNormalizedWeight (1/2) μ (j-1)+jointlessNormalizedWeight (1/2) μ (j+1)-
      2*jointlessNormalizedWeight (1/2) μ j≤
      (1/((j : ℝ)+1)+1/(μ+1/2-j)^2)*jointlessNormalizedWeight (1/2) μ j := by
  have hr0 : 0<μ+1/2-j := by linarith
  have hlow := jointlessNormalizedWeight_gt_third (a := (1/2 : ℝ)) (by norm_num) le_rfl
    (by linarith : 5/2≤μ) j hj (by linarith)
  have hb := jointless_difference_budget_half hμ j hj hr
  have hp := jointless_half_budget_paid hμ hr0 (show 0<(j : ℝ)+1 by positivity) (by linarith)
  have hL : 0<1/((j : ℝ)+1)+1/(μ+1/2-j)^2 := by positivity
  have hmul := mul_lt_mul_of_pos_left hlow hL
  nlinarith

end Dowling
