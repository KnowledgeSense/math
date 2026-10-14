import Dowling.DowlingJointlessAdverse

noncomputable section
namespace Dowling

 theorem jointlessRatio_tilt_lower {a μ r s : ℝ} (hs : 0<s) (hr : 1<r)
    (hβ : 0≤a*(1-a)*μ/4-a^2/2) :
    jointlessTilt s (jointlessQuadratic a μ) r-
      (a^2*μ/8)*jointlessTilt s jointlessAdverse r≤jointlessTilt s (jointlessRatioFunction a μ) r := by
  rw [jointlessRatio_tilt_decomposition a μ r s hr]
  have h1 := mul_nonneg hβ (jointlessTilt_recip_nonneg hs hr)
  have h2 := mul_nonneg (show 0≤3*a^2/16 by positivity) (jointlessTilt_recip_pair_nonneg hs hr)
  linarith

 theorem jointless_tilt_budget {a μ r η Q K Tp Tq Ta : ℝ}
    (hμ : 0<μ) (hr : 0<r) (hη : 0≤η)
    (hP : Tq-(a^2*μ/8)*Ta≤Tp) (hQ : -η*Tq≤Q)
    (hK : a^2*r^2*η*Ta≤K) :
    -η/μ^2*Tp≤Q/μ^2+K/(8*μ*r^2) := by
  have hp := mul_le_mul_of_nonneg_left hP hη
  have hk : a^2*η*Ta≤K/r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [hK]
  have hkm := mul_le_mul_of_nonneg_left hk (show 0≤μ/8 by positivity)
  have hnum : -η*Tp≤Q+μ/8*(K/r^2) := by nlinarith [hp,hkm]
  have hd := div_le_div_of_nonneg_right hnum (sq_nonneg μ)
  have heq : (Q+μ/8*(K/r^2))/μ^2=Q/μ^2+K/(8*μ*r^2) := by field_simp
  rw [heq] at hd
  convert hd using 1
  ring

 theorem jointlessQuadratic_negative_bound {a μ r : ℝ} (ha : 0≤a) (hμ : 0<μ)
    (hr : 0≤r) (hrμ : r≤μ) :
    -jointlessTilt (μ/(μ+1/2)) (jointlessQuadratic a μ) r≤a*(3*μ+1)/(2*(2*μ+1)) := by
  have h := jointlessQuadratic_tilt_lower ha hμ hr hrμ
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

 theorem jointless_beta_nonneg {a μ : ℝ} (ha : 0≤a) (ha3 : a≤1/3) (hμ : 3/2≤μ) :
    0≤a*(1-a)*μ/4-a^2/2 := by
  have hm : 0≤(μ-3/2)*(1-a) := mul_nonneg (by linarith) (by linarith)
  have h : 0≤a*((1-a)*μ-2*a) := mul_nonneg ha (by nlinarith)
  nlinarith

 theorem jointless_difference_budget_large {a μ : ℝ} (ha : 0<a) (ha3 : a≤1/3)
    (hμ : 5/2≤μ) (j : ℕ) (hj : 2≤j) (hr : 1+a/2≤μ+1/2-j) :
    3*(jointlessNormalizedWeight a μ (j-1)+jointlessNormalizedWeight a μ (j+1)-
      2*jointlessNormalizedWeight a μ j)≤
      (3*μ+1)/(2*μ^2*(2*μ+1))+53/(30*μ*(μ+1/2-j)^2) := by
  let r := μ+1/2-j
  let s := μ/(μ+1/2)
  let η := s^(j-2)
  have hm0 : 0<μ := by linarith
  have hr1 : 1<r := by dsimp [r]; linarith
  have hrμ : r≤μ := by
    dsimp [r]
    have hjR : (2 : ℝ)≤j := by exact_mod_cast hj
    linarith
  have hs0 : 0<s := by dsimp [s]; positivity
  have hs1 : s≤1 := by dsimp [s]; apply (div_le_one (by linarith)).mpr; linarith
  have hη0 : 0≤η := pow_nonneg hs0.le _
  have hη1 : η≤1 := pow_le_one₀ hs0.le hs1
  have hP := jointlessRatio_tilt_lower (a := a) (μ := μ) hs0 hr1 (jointless_beta_nonneg ha.le ha3 (by linarith))
  have hq := jointlessQuadratic_negative_bound ha.le hm0 (by linarith : 0≤r) hrμ
  have hQ0 : 0≤a*(3*μ+1)/(2*(2*μ+1)) := by positivity
  have hQ : -η*jointlessTilt s (jointlessQuadratic a μ) r≤a*(3*μ+1)/(2*(2*μ+1)) := by
    have h1 := mul_le_mul_of_nonneg_left hq hη0
    have h2 := mul_le_mul_of_nonneg_right hη1 hQ0
    dsimp only [s] at *
    nlinarith
  have hTa := jointlessAdverse_tilt_upper hs0 hs1 hr1 hη0 hη1
  have hscale := mul_le_mul_of_nonneg_left hTa (show 0≤a^2*r^2 by positivity)
  have hk := jointlessAdverse_large_bound ha ha3 hμ hr
  have hsinv : s⁻¹=(μ+1/2)/μ := by dsimp [s]; rw [inv_div]
  rw [hsinv] at hscale
  have hK : a^2*r^2*η*jointlessTilt s jointlessAdverse r≤212/45 := by
    dsimp only [r] at *
    nlinarith [hscale,hk]
  have hb := jointless_tilt_budget hm0 (show 0<r by linarith) hη0 hP hQ hK
  rw [jointlessNormalizedWeight_difference_large a μ hm0 j hj]
  change 3*(-η/μ^2*jointlessTilt s (jointlessRatioFunction a μ) r)≤_
  have hfirst : 3*(a*(3*μ+1)/(2*(2*μ+1)))/μ^2≤(3*μ+1)/(2*μ^2*(2*μ+1)) := by
    have hc : 0<(3*μ+1)/(2*μ^2*(2*μ+1)) := by positivity
    have hh := mul_le_mul_of_nonneg_right (show 3*a≤1 by linarith) hc.le
    convert hh using 1 <;> field_simp
  have heq : 3*((212/45 : ℝ)/(8*μ*r^2))=53/(30*μ*r^2) := by field_simp; norm_num
  rw [mul_div_assoc] at hfirst
  dsimp only [r] at hb heq ⊢
  linarith [hb,hfirst,heq]

end Dowling
