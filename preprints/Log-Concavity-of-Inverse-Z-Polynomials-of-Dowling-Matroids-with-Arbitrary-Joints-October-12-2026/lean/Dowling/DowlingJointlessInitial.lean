import Dowling.DowlingJointlessDefinitions

noncomputable section
namespace Dowling

 theorem jointlessNormalizedWeight_zero (a μ : ℝ) (hμ : 0<μ) :
    jointlessNormalizedWeight a μ 0=(1-a)*(2*μ-a)/(2*μ) := by
  have hLam : μ+1/2≠0 := by linarith
  have hr : μ+1/2+1≠0 := by linarith
  unfold jointlessNormalizedWeight jointlessRatioFunction jointlessCorrection
  simp only [pow_zero,Nat.cast_zero,sub_zero]
  field_simp [ne_of_gt hμ,hLam,hr]
  ring

 theorem jointlessNormalizedWeight_one (a μ : ℝ) (hμ : 1/2<μ) :
    jointlessNormalizedWeight a μ 1=
      1-a-a*(1-3*a/2)/(μ-1/2)+a^2/(2*(μ-1/2)^2) := by
  have hm : μ≠0 := by linarith
  have hLam : μ+1/2≠0 := by linarith
  have hr : μ+1/2-1≠0 := by linarith
  have hr' : μ-1/2≠0 := by linarith
  have hs : μ+1/2-1+1≠0 := by linarith
  unfold jointlessNormalizedWeight jointlessRatioFunction jointlessCorrection
  simp only [pow_one,Nat.cast_one]
  have hn1 : -1+μ^2*4≠0 := by nlinarith
  have hn2 : -1+μ*2≠0 := by linarith
  have hn3 : 1-μ*4+μ^2*4≠0 := by nlinarith [sq_pos_of_pos (show 0<μ-1/2 by linarith)]
  ring_nf
  field_simp [hm,hLam,hr,hr',hs,hn1,hn2,hn3]
  ring_nf
  have hn4 : -4+μ^2*16≠0 := by nlinarith
  field_simp [hn3,hn4]
  ring

 theorem jointlessNormalizedWeight_one_gt_half {a μ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 1/2<μ) : 1/2<jointlessNormalizedWeight a μ 1 := by
  rw [jointlessNormalizedWeight_one a μ hμ]
  have hr : 0<μ-1/2 := by linarith
  have hs := sq_nonneg (a/(μ-1/2)-(1-3*a/2))
  have haBound : 0<a*(1-9*a/4) := mul_pos ha (by linarith)
  have heq : a^2/(2*(μ-1/2)^2)=(a/(μ-1/2))^2/2 := by field_simp
  rw [heq]
  have hcross : a*(1-3*a/2)/(μ-1/2)=(a/(μ-1/2))*(1-3*a/2) := by ring
  rw [hcross]
  nlinarith

 theorem jointlessNormalizedWeight_one_gt_four_ninths {μ : ℝ} (hμ : 1/2<μ) :
    4/9<jointlessNormalizedWeight (1/2) μ 1 := by
  rw [jointlessNormalizedWeight_one (1/2) μ hμ]
  have hr : 0<μ-1/2 := by linarith
  have hs := sq_nonneg ((1/2 : ℝ)/(μ-1/2)-1/4)
  have heq : (1/2 : ℝ)^2/(2*(μ-1/2)^2)=((1/2 : ℝ)/(μ-1/2))^2/2 := by field_simp
  rw [heq]
  have hcross : (1/2 : ℝ)*(1-3*(1/2)/2)/(μ-1/2)=((1/2 : ℝ)/(μ-1/2))*(1/4) := by ring
  rw [hcross]
  nlinarith

end Dowling
