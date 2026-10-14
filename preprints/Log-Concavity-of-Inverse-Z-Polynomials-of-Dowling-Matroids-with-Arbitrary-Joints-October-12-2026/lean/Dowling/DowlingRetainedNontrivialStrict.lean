import Dowling.DowlingRetainedNontrivialWeights
import Dowling.DowlingWeightedMixtureStrict

noncomputable section
namespace Dowling

 theorem retainedNontrivialWeight_strict_half_one {θ : ℝ} (hθ : 0≤θ) (hθ1 : θ≤1)
    (n : ℕ) (hn : 4≤n) :
    retainedNontrivialWeight (1/2) θ n 0*retainedNontrivialWeight (1/2) θ n 2<
      (retainedNontrivialWeight (1/2) θ n 1)^2 := by
  let μ : ℝ := (n+(1/2 : ℝ)-1)/2
  have hnR : (4 : ℝ)≤n := by exact_mod_cast hn
  have hm : 7/4≤μ := by dsimp [μ]; linarith
  have hU (j : ℕ) (hj : 2*j≤n) : 0<dowlingBaseWeight (1/2) n j :=
    dowlingBaseWeight_pos (by norm_num) n j hj
  have hq (j : ℕ) (hj : 2*j≤n) : 0<jointlessNormalizedWeight (1/2) μ j :=
    jointlessNormalizedWeight_pos (by norm_num) le_rfl n j (by omega) hj
  have hbase := dowlingBaseWeight_curvature (a := (1/2 : ℝ)) (by norm_num) n 1 le_rfl (by omega)
  norm_num only at hbase
  have hr : 1<((n : ℝ)+1/2)/2-1 := by linarith
  have hprod : 0<(1/(((n : ℝ)+1/2)/2-1)^2)*(dowlingBaseWeight (1/2) n 1)^2 :=
    mul_pos (by positivity) (sq_pos_of_pos (hU 1 (by omega)))
  have hbase2 : 2*dowlingBaseWeight (1/2) n 0*dowlingBaseWeight (1/2) n 2<
      (dowlingBaseWeight (1/2) n 1)^2 := by nlinarith
  exact dowling_half_boundary_payment (hU 0 (by omega)) (hU 1 (by omega)) (hU 2 (by omega))
    hbase2 (hq 0 (by omega)) (hq 1 (by omega)) (hq 2 (by omega))
    (jointlessNormalizedWeight_half_zero_lt μ (by linarith))
    (jointlessNormalizedWeight_one_gt_four_ninths (by linarith))
    (jointlessNormalizedWeight_half_two_lt hm) hθ hθ1

 theorem retainedNontrivialWeight_strict {a θ : ℝ} (ha : 0<a)
    (haCases : a≤1/3 ∨ a=1/2) (hθ : 0≤θ) (hθ1 : θ≤1)
    (n j : ℕ) (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    retainedNontrivialWeight a θ n (j-1)*retainedNontrivialWeight a θ n (j+1)<
      (retainedNontrivialWeight a θ n j)^2 := by
  rcases haCases with ha3 | rfl
  · exact retainedNontrivialWeight_strict_small_parameter ha ha3 hθ hθ1 n j hj hjn
  · by_cases hj1 : j=1
    · subst j
      exact retainedNontrivialWeight_strict_half_one hθ hθ1 n (by omega)
    · exact retainedNontrivialWeight_strict_half_large hθ hθ1 n j (by omega) hjn

/-- The literal supported raised-weight row for every nontrivial retained-joint parameter. -/
def retainedNontrivialScalar (a θ : ℝ) (n k : ℕ) : ℝ :=
  weightedMixtureCoefficient (retainedNontrivialWeight a θ n) (a+1) n k

 theorem retainedNontrivialScalar_pos {a θ : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (hθ : 0≤θ) (hθ1 : θ≤1) (n k : ℕ) (hn : 2≤n) (hk : k≤n) :
    0<retainedNontrivialScalar a θ n k := by
  rw [retainedNontrivialScalar,← weightedMixtureFunction_sum]
  exact weightedMixtureFunction_sum_pos n k
    (fun j hj=>retainedNontrivialWeight_pos ha ha2 hθ hθ1 n j hn hj) (by linarith) hk

 theorem retainedNontrivialScalar_strict_log_concave {a θ : ℝ} (ha : 0<a)
    (haCases : a≤1/3 ∨ a=1/2) (hθ : 0≤θ) (hθ1 : θ≤1)
    (n k : ℕ) (hn : 2≤n) (hk : 1≤k) (hkn : k<n) :
    retainedNontrivialScalar a θ n (k-1)*retainedNontrivialScalar a θ n (k+1)<
      (retainedNontrivialScalar a θ n k)^2 := by
  have ha2 : a≤1/2 := by rcases haCases with h | rfl <;> linarith
  exact weightedMixtureCoefficient_strict_of_log_concave n k
    (fun j hj=>retainedNontrivialWeight_pos ha ha2 hθ hθ1 n j hn hj)
    (fun j hj hjn=>(retainedNontrivialWeight_strict ha haCases hθ hθ1 n j hj hjn).le)
    (by linarith) hk hkn

end Dowling
