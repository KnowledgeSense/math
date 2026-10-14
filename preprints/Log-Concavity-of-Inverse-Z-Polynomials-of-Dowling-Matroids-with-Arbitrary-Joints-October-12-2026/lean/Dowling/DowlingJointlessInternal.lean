import Dowling.DowlingJointlessPositivity

noncomputable section
namespace Dowling

def jointlessRatioLinear (μ r : ℝ) : ℝ := μ*(2*μ-r+1/(4*r))

 theorem jointlessRatio_parameter_compare (a μ r : ℝ) (hr : 0<r) :
    jointlessRatioFunction (1/2) μ r-jointlessRatioFunction a μ r=
      (1/2-a)*((1/2-a)*jointlessRatioLinear μ r+(1/2+a)*jointlessRatioFunction 1 μ r) := by
  unfold jointlessRatioFunction jointlessCorrection jointlessRatioLinear
  have hr1 : r+1≠0 := by linarith
  field_simp [ne_of_gt hr,hr1]
  ring

 theorem jointlessRatio_one_formula (μ r : ℝ) (hr : 0<r) :
    jointlessRatioFunction 1 μ r=μ^2+(r-μ)^2/3+r-2*μ+1/6-1/(2*r)+
      3/(16*r*(r+1))-μ/(8*r^2*(r+1)) := by
  have hr1 : r+1≠0 := by linarith
  unfold jointlessRatioFunction jointlessCorrection
  field_simp
  ring

 theorem jointlessRatio_one_pos {μ r : ℝ} (hμ : 5/2≤μ) (hr : 1≤r) :
    0<jointlessRatioFunction 1 μ r := by
  have hr0 : 0<r := by linarith
  rw [jointlessRatio_one_formula μ r hr0]
  have h1 : 1/(2*r)≤(1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have h2 : μ/(8*r^2*(r+1))≤μ/16 := by
    have hd : 0<8*r^2*(r+1) := by positivity
    apply (div_le_iff₀ hd).mpr
    have hrr : 2≤r^2*(r+1) := by
      have hs : 1≤r^2 := by nlinarith
      nlinarith
    have hp : 0≤μ*(r^2*(r+1)-2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h3 : 0≤3/(16*r*(r+1)) := by positivity
  have hquad : 0<μ^2-33*μ/16+2/3 := by nlinarith [sq_nonneg (μ-5/2)]
  nlinarith [sq_nonneg (r-μ)]

 theorem jointlessRatio_le_half {a μ r : ℝ} (ha : 0≤a) (ha2 : a≤1/2)
    (hμ : 5/2≤μ) (hr : 1≤r) (hrμ : r≤μ) :
    jointlessRatioFunction a μ r≤jointlessRatioFunction (1/2) μ r := by
  have hp := jointlessRatio_one_pos hμ hr
  have hlin : 0≤jointlessRatioLinear μ r := by
    unfold jointlessRatioLinear
    have hrec : 0≤1/(4*r) := by positivity
    apply mul_nonneg (by linarith)
    linarith
  have hnon : 0≤(1/2-a)*((1/2-a)*jointlessRatioLinear μ r+(1/2+a)*jointlessRatioFunction 1 μ r) := by
    positivity
  rw [← jointlessRatio_parameter_compare a μ r (by linarith)] at hnon
  linarith

 theorem jointlessRatio_half_reserve (μ r : ℝ) (hr : 0<r) :
    (μ^2-μ*r/3-μ/2)-jointlessRatioFunction (1/2) μ r=
      μ^2/6+(μ*r-r^2)/12-r/4-1/24-(μ/16-1/8)/r-
        (3*r-2*μ)/(64*r^2*(r+1)) := by
  have hr1 : r+1≠0 := by linarith
  unfold jointlessRatioFunction jointlessCorrection
  field_simp
  ring

 theorem jointlessRatio_half_bound {μ r : ℝ} (hμ : 5/2≤μ) (hr : 1≤r) (hrμ : r≤μ) :
    jointlessRatioFunction (1/2) μ r<μ^2-μ*r/3-μ/2 := by
  have hr0 : 0<r := by linarith
  have h1 : (μ/16-1/8)/r≤μ/16 := by
    apply (div_le_iff₀ hr0).mpr
    have hmul : 0≤μ*(r-1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h2 : (3*r-2*μ)/(64*r^2*(r+1))≤(3/128 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hrpow : 0≤r*(r-1)*(r+2) := by positivity
    nlinarith
  have h3 : 0≤μ*r-r^2 := by nlinarith
  have hquad : 0<μ^2/6-5*μ/16-25/384 := by nlinarith [sq_nonneg (μ-5/2)]
  have heq := jointlessRatio_half_reserve μ r hr0
  nlinarith

end Dowling
