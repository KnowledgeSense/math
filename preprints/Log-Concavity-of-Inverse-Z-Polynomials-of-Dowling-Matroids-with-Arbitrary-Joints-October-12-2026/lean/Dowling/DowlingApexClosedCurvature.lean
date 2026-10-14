import Dowling.DowlingApexPayment

noncomputable section
namespace Dowling

def apexClosedNormalizedWeight (n j : ℕ) : ℝ :=
  ((n:ℝ)/(n+1))^j*(((n:ℝ)+1)/2)^2/((n:ℝ)/2)^2*
    apexClosedRatio ((n:ℝ)/2) (((n:ℝ)+1)/2-j)/n

theorem apex_geometric_curvature (s L c : ℝ) (f : ℝ→ℝ) (hs : s≠0)
    (j : ℕ) (hj : 1≤j) :
    c*s^(j-1)*f (L-(j-1:ℕ))+c*s^(j+1)*f (L-(j+1:ℕ))-2*(c*s^j*f (L-j))=
      c*s^j*jointlessTilt s f (L-j) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  simp only [Nat.succ_sub_one,Nat.cast_succ]
  unfold jointlessTilt
  have h1 : L-((i:ℝ)+1+1)=L-((i:ℝ)+1)-1 := by ring
  have h2 : L-(i:ℝ)=L-((i:ℝ)+1)+1 := by ring
  rw [h1,h2]
  simp only [pow_succ]
  field_simp
  ring

theorem apexClosedNormalizedWeight_curvature (n j : ℕ) (hn : 0<n) (hj : 1≤j) :
    apexClosedNormalizedWeight n (j-1)+apexClosedNormalizedWeight n (j+1)-
      2*apexClosedNormalizedWeight n j=
      ((((n:ℝ)+1)/2)^2/((n:ℝ)/2)^2/n)*((n:ℝ)/(n+1))^j*
        jointlessTilt ((n:ℝ)/(n+1)) (apexClosedRatio ((n:ℝ)/2)) (((n:ℝ)+1)/2-j) := by
  have hs : (n:ℝ)/(n+1)≠0 := by positivity
  have h := apex_geometric_curvature ((n:ℝ)/(n+1)) (((n:ℝ)+1)/2)
    ((((n:ℝ)+1)/2)^2/((n:ℝ)/2)^2/n) (apexClosedRatio ((n:ℝ)/2)) hs j hj
  unfold apexClosedNormalizedWeight
  convert h using 1; ring

theorem apexClosedNormalizedWeight_budget (n j : ℕ) (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    apexClosedNormalizedWeight n (j-1)+apexClosedNormalizedWeight n (j+1)-
      2*apexClosedNormalizedWeight n j <
      (1/((j:ℝ)+1)+1/(((n:ℝ)+1)/2-j)^2)*apexClosedNormalizedWeight n j := by
  have hn : 0<n := by omega
  have hjR : (1:ℝ)≤j := by exact_mod_cast hj
  have hjnR : (2*(j+1):ℝ)≤n := by exact_mod_cast hjn
  have h := apexClosedRatio_budget j (((n:ℝ)+1)/2-j) hjR (by linarith)
  have hm : (j:ℝ)+(((n:ℝ)+1)/2-j)-1/2=(n:ℝ)/2 := by ring
  have hl : (j:ℝ)+(((n:ℝ)+1)/2-j)=((n:ℝ)+1)/2 := by ring
  rw [hm,hl] at h
  have hs : ((n:ℝ)/2)/(((n:ℝ)+1)/2)=(n:ℝ)/(n+1) := by field_simp
  rw [hs] at h
  have hp : 0<((((n:ℝ)+1)/2)^2/((n:ℝ)/2)^2/n)*((n:ℝ)/(n+1))^j := by positivity
  have hb := mul_lt_mul_of_pos_left h hp
  rw [apexClosedNormalizedWeight_curvature n j hn hj]
  unfold apexClosedNormalizedWeight
  convert hb using 1; ring

end Dowling
