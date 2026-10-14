import Dowling.DowlingJointlessBudget

noncomputable section
namespace Dowling

 theorem jointlessQuadratic_half_negative_bound {μ r : ℝ} (hμ : 0<μ) (hr : 0≤r) :
    -jointlessTilt (μ/(μ+1/2)) (jointlessQuadratic (1/2) μ) r≤μ/(12*(2*μ+1)) := by
  have h := jointlessQuadratic_tilt (1/2) μ r hμ
  have hrest : 0≤r^2/12+(μ/4+5/12)*r+5*μ/12+3/8 := by positivity
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

 theorem jointless_difference_budget_half {μ : ℝ} (hμ : 11/4≤μ)
    (j : ℕ) (hj : 2≤j) (hr : 5/4≤μ+1/2-j) :
    jointlessNormalizedWeight (1/2) μ (j-1)+jointlessNormalizedWeight (1/2) μ (j+1)-
      2*jointlessNormalizedWeight (1/2) μ j≤
      1/(12*μ*(2*μ+1))+7/(11*μ*(μ+1/2-j)^2) := by
  let r := μ+1/2-j
  let s := μ/(μ+1/2)
  let η := s^(j-2)
  have hm0 : 0<μ := by linarith
  have hr1 : 1<r := by dsimp [r]; linarith
  have hs0 : 0<s := by dsimp [s]; positivity
  have hs1 : s≤1 := by dsimp [s]; apply (div_le_one (by linarith)).mpr; linarith
  have hη0 : 0≤η := pow_nonneg hs0.le _
  have hη1 : η≤1 := pow_le_one₀ hs0.le hs1
  have hβ : 0≤(1/2 : ℝ)*(1-1/2)*μ/4-(1/2)^2/2 := by linarith
  have hP := jointlessRatio_tilt_lower (a := (1/2 : ℝ)) (μ := μ) hs0 hr1 hβ
  have hq := jointlessQuadratic_half_negative_bound hm0 (show 0≤r by linarith)
  have hQ0 : 0≤μ/(12*(2*μ+1)) := by positivity
  have hQ : -η*jointlessTilt s (jointlessQuadratic (1/2) μ) r≤μ/(12*(2*μ+1)) := by
    have h1 := mul_le_mul_of_nonneg_left hq hη0
    have h2 := mul_le_mul_of_nonneg_right hη1 hQ0
    dsimp only [s] at *
    nlinarith
  have hTa := jointlessAdverse_tilt_upper hs0 hs1 hr1 hη0 hη1
  have hscale := mul_le_mul_of_nonneg_left hTa (sq_nonneg r)
  have hk := jointlessAdverse_half_bound hμ hr
  have hsinv : s⁻¹=(μ+1/2)/μ := by dsimp [s]; rw [inv_div]
  rw [hsinv] at hscale
  have hK : (1/2 : ℝ)^2*r^2*η*jointlessTilt s jointlessAdverse r≤56/11 := by
    dsimp only [r] at *
    nlinarith
  have hb := jointless_tilt_budget hm0 (show 0<r by linarith) hη0 hP hQ hK
  rw [jointlessNormalizedWeight_difference_large (1/2) μ hm0 j hj]
  change -η/μ^2*jointlessTilt s (jointlessRatioFunction (1/2) μ) r≤_
  have hfirst : μ/(12*(2*μ+1))/μ^2=1/(12*μ*(2*μ+1)) := by field_simp
  have hsecond : (56/11 : ℝ)/(8*μ*r^2)=7/(11*μ*r^2) := by field_simp; norm_num
  rw [hfirst,hsecond] at hb
  exact hb

end Dowling
