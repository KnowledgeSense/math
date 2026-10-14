import Dowling.DowlingJointlessDifference

noncomputable section
namespace Dowling

 theorem jointlessAdverse_left_gap {a r : ℝ} (ha : 0<a) (hr : 1+a/2≤r) :
    a^2*r^2*jointlessAdverse (r-1)≤4+2*a := by
  have hu : 0<r-1 := by linarith
  have hr0 : 0<r := by linarith
  have hgap : a≤2*(r-1) := by linarith
  have h1 : a^2≤4*(r-1)^2 := by nlinarith
  have h2 : a^2*(r-1)≤2*a*(r-1)^2 := by
    have hh := mul_nonneg (show 0≤2*(r-1)-a by linarith) (show 0≤a*(r-1) by positivity)
    nlinarith
  have heq : a^2*r^2*jointlessAdverse (r-1)=a^2*r/(r-1)^2 := by
    unfold jointlessAdverse
    rw [show r-1+1=r by ring]
    field_simp
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hu)).mpr
  nlinarith

 theorem jointlessAdverse_right {r : ℝ} (hr : 0<r) :
    r^2*jointlessAdverse (r+1)≤1/(r+2) := by
  unfold jointlessAdverse
  rw [show r+1+1=r+2 by ring]
  have hd : 0<(r+1)^2*(r+2) := by positivity
  have heq : r^2*(1/((r+1)^2*(r+2)))=r^2/((r+1)^2*(r+2)) := by ring
  rw [heq]
  apply (div_le_div_iff₀ hd (by linarith)).mpr
  have hp : 0≤(r+2)*(2*r+1) := by positivity
  nlinarith

 theorem jointless_inverse_scale_le {μ c : ℝ} (hμ : 0<μ) (h : 1/2≤(c-1)*μ) :
    (μ+1/2)/μ≤c := (div_le_iff₀ hμ).mpr (by nlinarith)

 theorem jointlessAdverse_large_bound {a μ r : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 5/2≤μ) (hr : 1+a/2≤r) :
    a^2*r^2*(jointlessAdverse (r-1)+((μ+1/2)/μ)*jointlessAdverse (r+1))≤212/45 := by
  have hr1 : 1<r := by linarith
  have hm0 : 0<μ := by linarith
  have hleft := jointlessAdverse_left_gap ha hr
  have hright := jointlessAdverse_right (show 0<r by linarith)
  have hden : 1/(r+2)≤(1/3 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hrf : r^2*jointlessAdverse (r+1)≤(1/3 : ℝ) := hright.trans hden
  have hscale : (μ+1/2)/μ≤(6/5 : ℝ) := jointless_inverse_scale_le hm0 (by linarith)
  have hscale0 : 0≤(μ+1/2)/μ := by positivity
  have haSq : a^2≤(1/9 : ℝ) := by nlinarith
  have hprod := mul_le_mul (mul_le_mul haSq hscale hscale0 (by positivity)) hrf
    (mul_nonneg (sq_nonneg r) (jointlessAdverse_pos (by linarith : 0<r+1)).le) (by norm_num : 0≤(1/9 : ℝ)*(6/5))
  nlinarith

 theorem jointlessAdverse_one_bound {a μ r : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 3/2≤μ) (hr : 1+a/2≤r) :
    a^2*r^2*(jointlessAdverse (r-1)+((μ+1/2)/μ)^2*jointlessAdverse (r+1))≤1150/243 := by
  have hr1 : 1<r := by linarith
  have hm0 : 0<μ := by linarith
  have hleft := jointlessAdverse_left_gap ha hr
  have hright := jointlessAdverse_right (show 0<r by linarith)
  have hden : 1/(r+2)≤(1/3 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hrf : r^2*jointlessAdverse (r+1)≤(1/3 : ℝ) := hright.trans hden
  have hscale : (μ+1/2)/μ≤(4/3 : ℝ) := jointless_inverse_scale_le hm0 (by linarith)
  have hscale0 : 0≤(μ+1/2)/μ := by positivity
  have hscaleSq : ((μ+1/2)/μ)^2≤(16/9 : ℝ) := by nlinarith
  have haSq : a^2≤(1/9 : ℝ) := by nlinarith
  have hprod := mul_le_mul (mul_le_mul haSq hscaleSq (sq_nonneg _) (by positivity)) hrf
    (mul_nonneg (sq_nonneg r) (jointlessAdverse_pos (by linarith : 0<r+1)).le) (by norm_num : 0≤(1/9 : ℝ)*(16/9))
  nlinarith

 theorem jointlessAdverse_half_bound {μ r : ℝ} (hμ : 11/4≤μ) (hr : 5/4≤r) :
    r^2*(jointlessAdverse (r-1)+((μ+1/2)/μ)*jointlessAdverse (r+1))≤224/11 := by
  have hm0 : 0<μ := by linarith
  have hleft := jointlessAdverse_left_gap (a := (1/2 : ℝ)) (by norm_num) (by linarith : 1+(1/2 : ℝ)/2≤r)
  have hright := jointlessAdverse_right (show 0<r by linarith)
  have hden : 1/(r+2)≤(4/13 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hrf : r^2*jointlessAdverse (r+1)≤(4/13 : ℝ) := hright.trans hden
  have hscale : (μ+1/2)/μ≤(13/11 : ℝ) := jointless_inverse_scale_le hm0 (by linarith)
  have hscale0 : 0≤(μ+1/2)/μ := by positivity
  have hprod := mul_le_mul hscale hrf
    (mul_nonneg (sq_nonneg r) (jointlessAdverse_pos (by linarith : 0<r+1)).le) (by norm_num : 0≤(13/11 : ℝ))
  nlinarith

end Dowling
