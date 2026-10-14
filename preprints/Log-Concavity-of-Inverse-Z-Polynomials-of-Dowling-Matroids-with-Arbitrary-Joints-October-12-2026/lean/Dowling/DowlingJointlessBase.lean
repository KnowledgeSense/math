import Dowling.DowlingJointlessDefinitions

noncomputable section
namespace Dowling

 theorem dowlingBaseWeight_pos {a : ℝ} (ha : 0<a) (n j : ℕ) (hj : 2*j≤n) :
    0<dowlingBaseWeight a n j := by
  unfold dowlingBaseWeight
  have hjR : (2 : ℝ)*j≤n := by exact_mod_cast hj
  exact mul_pos (div_pos ha (by positivity))
    (dowlingQuadraticWeight_pos (by positivity) (by linarith))

 theorem dowlingQuadraticWeight_curvature {c : ℝ} (hc : 0<c) (j : ℕ) (hj : 1≤j)
    (hjc : (j : ℝ)+1<c) :
    dowlingQuadraticWeight c (j-1)*dowlingQuadraticWeight c (j+1)=
      (1-1/((j : ℝ)+1))*(1-1/(c-j)^2)*(dowlingQuadraticWeight c j)^2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  simp only [Nat.succ_sub_one]
  rw [dowlingQuadraticWeight_factor (ne_of_gt hc),
    dowlingQuadraticWeight_factor (ne_of_gt hc),dowlingQuadraticWeight_factor (ne_of_gt hc)]
  simp only [Nat.factorial_succ,pow_succ,Nat.cast_mul,Nat.cast_succ]
  have hcj : c-((k : ℝ)+1)≠0 := by simp only [Nat.cast_succ] at hjc; linarith
  have hf : (k.factorial : ℝ)≠0 := by positivity
  have hp : c^k≠0 := pow_ne_zero _ (ne_of_gt hc)
  field_simp
  ring

 theorem dowlingBaseWeight_curvature {a : ℝ} (ha : 0<a) (n j : ℕ)
    (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    dowlingBaseWeight a n (j-1)*dowlingBaseWeight a n (j+1)=
      (1-1/((j : ℝ)+1))*(1-1/(((n : ℝ)+a)/2-j)^2)*(dowlingBaseWeight a n j)^2 := by
  have hjR : (2 : ℝ)*(j+1)≤n := by exact_mod_cast hjn
  have h := dowlingQuadraticWeight_curvature (c := ((n : ℝ)+a)/2) (by positivity) j hj (by linarith)
  unfold dowlingBaseWeight
  calc
    _ = (a/((n : ℝ)+a))^2*(dowlingQuadraticWeight (((n : ℝ)+a)/2) (j-1)*
        dowlingQuadraticWeight (((n : ℝ)+a)/2) (j+1)) := by ring
    _ = _ := by rw [h]; ring

end Dowling
