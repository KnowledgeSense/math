import Dowling.DowlingJointlessPayment
import Dowling.DowlingJointlessHalfBoundary
import Dowling.DowlingJointlessBase

noncomputable section
namespace Dowling

 theorem retainedNontrivialWeight_pos {a θ : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (hθ : 0≤θ) (hθ1 : θ≤1) (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    0<retainedNontrivialWeight a θ n j :=
  mul_pos (dowlingBaseWeight_pos ha n j hj)
    (dowling_interpolated_pos (jointlessNormalizedWeight_pos ha ha2 n j hn hj) hθ hθ1)

 theorem retainedNontrivialWeight_strict_of_budget {a θ : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (hθ : 0≤θ) (hθ1 : θ≤1) (n j : ℕ) (hj : 1≤j) (hjn : 2*(j+1)≤n)
    (hbudget : jointlessNormalizedWeight a ((n+a-1)/2) (j-1)+
      jointlessNormalizedWeight a ((n+a-1)/2) (j+1)-2*jointlessNormalizedWeight a ((n+a-1)/2) j≤
      (1/((j : ℝ)+1)+1/(((n : ℝ)+a)/2-j)^2)*jointlessNormalizedWeight a ((n+a-1)/2) j) :
    retainedNontrivialWeight a θ n (j-1)*retainedNontrivialWeight a θ n (j+1)<
      (retainedNontrivialWeight a θ n j)^2 := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hjnR : (2 : ℝ)*(j+1)≤n := by exact_mod_cast hjn
  have hr : 1<((n : ℝ)+a)/2-j := by linarith
  have hA0 : 0<1/((j : ℝ)+1) := by positivity
  have hA1 : 1/((j : ℝ)+1)<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hB0 : 0<1/(((n : ℝ)+a)/2-j)^2 := by positivity
  have hB1 : 1/(((n : ℝ)+a)/2-j)^2<1 :=
    (div_lt_one (by positivity)).mpr (by nlinarith)
  have hq (k : ℕ) (hk : 2*k≤n) : 0<1-θ+θ*jointlessNormalizedWeight a ((n+a-1)/2) k :=
    dowling_interpolated_pos (jointlessNormalizedWeight_pos ha ha2 n k (by omega) hk) hθ hθ1
  exact dowling_curvature_payment hA0 hA1 hB0 hB1
    (dowlingBaseWeight_pos ha n (j-1) (by omega)) (dowlingBaseWeight_pos ha n j (by omega))
    (dowlingBaseWeight_pos ha n (j+1) hjn) (hq (j-1) (by omega)).le (hq j (by omega))
    (hq (j+1) hjn).le (dowlingBaseWeight_curvature ha n j hj hjn)
    (dowling_interpolated_budget hθ hθ1 (by positivity) hbudget)

 theorem retainedNontrivialWeight_strict_small_parameter {a θ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hθ : 0≤θ) (hθ1 : θ≤1) (n j : ℕ) (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    retainedNontrivialWeight a θ n (j-1)*retainedNontrivialWeight a θ n (j+1)<
      (retainedNontrivialWeight a θ n j)^2 := by
  apply retainedNontrivialWeight_strict_of_budget ha (by linarith) hθ hθ1 n j hj hjn
  let μ : ℝ := (n+a-1)/2
  have heq : μ+1/2=((n : ℝ)+a)/2 := by dsimp [μ]; ring
  have hjnR : (2 : ℝ)*(j+1)≤n := by exact_mod_cast hjn
  have hr : 1+a/2≤μ+1/2-j := by dsimp [μ]; linarith
  by_cases hj1 : j=1
  · subst j
    have hnR : (4 : ℝ)≤n := by exact_mod_cast (show 4≤n by omega)
    have hm : 3/2≤μ := by dsimp [μ]; linarith
    have h := jointlessNormalizedWeight_budget_one ha ha3 hm (by linarith : 1+a/2≤μ-1/2)
    have heq' : μ-1/2=((n : ℝ)+a)/2-1 := by dsimp [μ]; ring
    simpa only [heq',Nat.sub_self,Nat.reduceAdd,Nat.cast_one,one_add_one_eq_two] using h
  · have hj2 : 2≤j := by omega
    have hnR : (6 : ℝ)≤n := by exact_mod_cast (show 6≤n by omega)
    have hm : 5/2≤μ := by dsimp [μ]; linarith
    have h := jointlessNormalizedWeight_budget_large ha ha3 hm j hj2 hr
    simpa only [heq] using h

 theorem retainedNontrivialWeight_strict_half_large {θ : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (n j : ℕ) (hj : 2≤j) (hjn : 2*(j+1)≤n) :
    retainedNontrivialWeight (1/2) θ n (j-1)*retainedNontrivialWeight (1/2) θ n (j+1)<
      (retainedNontrivialWeight (1/2) θ n j)^2 := by
  apply retainedNontrivialWeight_strict_of_budget (by norm_num : (0 : ℝ)<1/2) le_rfl hθ hθ1 n j (by omega) hjn
  let μ : ℝ := (n+(1/2 : ℝ)-1)/2
  have heq : μ+1/2=((n : ℝ)+1/2)/2 := by dsimp [μ]; ring
  have hnR : (6 : ℝ)≤n := by exact_mod_cast (show 6≤n by omega)
  have hjnR : (2 : ℝ)*(j+1)≤n := by exact_mod_cast hjn
  have hm : 11/4≤μ := by dsimp [μ]; linarith
  have hr : 5/4≤μ+1/2-j := by dsimp [μ]; linarith
  have h := jointlessNormalizedWeight_budget_half hm j hj hr
  simpa only [heq] using h

end Dowling
