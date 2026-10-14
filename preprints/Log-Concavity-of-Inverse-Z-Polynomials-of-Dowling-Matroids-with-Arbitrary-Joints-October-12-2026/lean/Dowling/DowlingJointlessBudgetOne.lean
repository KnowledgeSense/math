import Dowling.DowlingJointlessBudget

noncomputable section
namespace Dowling

 theorem jointlessAdverse_inverse_tilt_upper {s r : ℝ} (hs : 0<s) (hr : 1<r) :
    s⁻¹*jointlessTilt s jointlessAdverse r≤jointlessAdverse (r-1)+(s⁻¹)^2*jointlessAdverse (r+1) := by
  have hc := jointlessAdverse_pos (show 0<r by linarith)
  have hpos : 0≤2*s⁻¹*jointlessAdverse r := by positivity
  have heq : s⁻¹*jointlessTilt s jointlessAdverse r=
      jointlessAdverse (r-1)+(s⁻¹)^2*jointlessAdverse (r+1)-2*s⁻¹*jointlessAdverse r := by
    unfold jointlessTilt
    field_simp
  rw [heq]
  linarith

 theorem jointless_difference_budget_one {a μ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 3/2≤μ) (hr : 1+a/2≤μ-1/2) :
    2*(jointlessNormalizedWeight a μ 0+jointlessNormalizedWeight a μ 2-
      2*jointlessNormalizedWeight a μ 1)≤22/81+(575/729)/(μ-1/2)^2 := by
  let r := μ-1/2
  let s := μ/(μ+1/2)
  have hm0 : 0<μ := by linarith
  have hr1 : 1<r := by dsimp [r]; linarith
  have hs0 : 0<s := by dsimp [s]; positivity
  have hsi : s⁻¹=(μ+1/2)/μ := by dsimp [s]; rw [inv_div]
  have hη0 : 0≤s⁻¹ := inv_nonneg.mpr hs0.le
  have hP := jointlessRatio_tilt_lower (a := a) (μ := μ) hs0 hr1 (jointless_beta_nonneg ha.le ha3 hμ)
  have hq := jointlessQuadratic_negative_bound ha.le hm0 (by linarith : 0≤r) (by dsimp [r]; linarith : r≤μ)
  have hQ : -s⁻¹*jointlessTilt s (jointlessQuadratic a μ) r≤a*(3*μ+1)/(4*μ) := by
    have hh := mul_le_mul_of_nonneg_left hq hη0
    have heq : s⁻¹*(a*(3*μ+1)/(2*(2*μ+1)))=a*(3*μ+1)/(4*μ) := by
      rw [hsi]
      field_simp
      ring
    rw [heq] at hh
    dsimp only [s] at *
    nlinarith
  have hTa := jointlessAdverse_inverse_tilt_upper hs0 hr1
  have hscale := mul_le_mul_of_nonneg_left hTa (show 0≤a^2*r^2 by positivity)
  rw [hsi] at hscale
  have hk := jointlessAdverse_one_bound ha ha3 hμ hr
  have hK : a^2*r^2*s⁻¹*jointlessTilt s jointlessAdverse r≤1150/243 := by
    rw [hsi]
    dsimp only [r] at *
    nlinarith
  have hb := jointless_tilt_budget hm0 (show 0<r by linarith) hη0 hP hQ hK
  rw [jointlessNormalizedWeight_difference_one a μ hm0]
  rw [← hsi]
  change 2*(-s⁻¹/μ^2*jointlessTilt s (jointlessRatioFunction a μ) r)≤_
  have hfirst : 2*(a*(3*μ+1)/(4*μ)/μ^2)≤(22/81 : ℝ) := by
    have hfac : 0≤(2*μ-3)*(66*μ^2+99*μ+27) := mul_nonneg (by linarith) (by positivity)
    have hcube : 0<μ^3 := by positivity
    have haMul := mul_le_mul_of_nonneg_right ha3 (show 0≤3*μ+1 by positivity)
    have heq : 2*(a*(3*μ+1)/(4*μ)/μ^2)=a*(3*μ+1)/(2*μ^3) := by field_simp; ring
    rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsecond : 2*((1150/243 : ℝ)/(8*μ*r^2))≤(575/729)/r^2 := by
    have hr0 : 0<r := by linarith
    have heq : 2*((1150/243 : ℝ)/(8*μ*r^2))=(575/486)/(μ*r^2) := by field_simp; norm_num
    rw [heq]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hr0)).mpr
    have hh : 0≤(μ-3/2)*r^2 := by positivity
    nlinarith
  dsimp only [r] at hb hsecond ⊢
  linarith

end Dowling
