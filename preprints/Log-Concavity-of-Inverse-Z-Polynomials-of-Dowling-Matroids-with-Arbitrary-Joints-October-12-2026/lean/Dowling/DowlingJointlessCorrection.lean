import Dowling.DowlingJointlessInitial

noncomputable section
namespace Dowling

def jointlessReserve (a μ r : ℝ) : ℝ :=
  (2*a-2*a^2/3)*r*μ^2-jointlessCorrection a μ r

 theorem jointlessReserve_half (μ r : ℝ) (hr : 0<r) :
    jointlessReserve (1/2) μ r=
      r^2*(5*μ-3-r)/12+r*(μ/2-1/24)-μ/16+
        1/8-(3*r-2*μ)/(64*r*(r+1)) := by
  unfold jointlessReserve jointlessCorrection
  have hr1 : r+1≠0 := by linarith
  field_simp [ne_of_gt hr,hr1]
  ring

 theorem jointlessReserve_compare (a μ r : ℝ) :
    jointlessReserve a μ r=4*a^2*jointlessReserve (1/2) μ r+
      a*(1-2*a)*μ*(r^2-1/4) := by
  unfold jointlessReserve jointlessCorrection
  ring

 theorem jointlessReserve_half_pos {μ r : ℝ} (hr : 1/2≤r) (hμ : r+3/2≤μ) :
    0<jointlessReserve (1/2) μ r := by
  have hr0 : 0<r := by linarith
  have hμ2 : 2≤μ := by linarith
  rw [jointlessReserve_half μ r hr0]
  have hcoef : 0≤5*μ-3-r := by linarith
  have hfirst : 0≤r^2*(5*μ-3-r)/12 := by positivity
  have hmid : 0<r*(μ/2-1/24)-μ/16 := by
    have hm : 0≤(r-1/2)*(μ/2-1/24) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : 0<64*r*(r+1) := by positivity
  have hfrac : (3*r-2*μ)/(64*r*(r+1))<1/8 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_nonneg r]
  linarith

 theorem jointlessReserve_pos {a μ r : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (hr : 1/2≤r) (hμ : r+3/2≤μ) : 0<jointlessReserve a μ r := by
  rw [jointlessReserve_compare]
  have hfirst : 0<4*a^2*jointlessReserve (1/2) μ r :=
    mul_pos (by positivity) (jointlessReserve_half_pos hr hμ)
  have hrest : 0≤a*(1-2*a)*μ*(r^2-1/4) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg ha.le (by linarith)
      · linarith
    · nlinarith
  linarith

 theorem jointlessRatio_terminal (a μ : ℝ) (ha : 0<a) :
    jointlessRatioFunction a μ (a/2)=
      (2*a-2*a^2/3)*μ^2+
      (a^3/6-5*a^2/2-a*(1+a)/(2*(a+2)))*μ+
      (a^4/12+a^3/2+a^2/6-a+3*a/(4*(a+2))) := by
  have ha0 : a≠0 := ne_of_gt ha
  have hap : a+2≠0 := by linarith
  unfold jointlessRatioFunction jointlessCorrection
  field_simp
  ring

 theorem jointlessRatio_terminal_lt {a μ : ℝ} (ha : 0<a) (ha2 : a≤1/2) (hμ : 0<μ) :
    jointlessRatioFunction a μ (a/2)<(2*a-2*a^2/3)*μ^2 := by
  rw [jointlessRatio_terminal a μ ha]
  have haSq : a^2≤1/4 := by nlinarith
  have haCube : a^3≤1/8 := by
    have h := mul_le_mul_of_nonneg_left haSq ha.le
    nlinarith
  have hlinear : a^3/6-5*a^2/2-a*(1+a)/(2*(a+2))<0 := by
    have h := mul_le_mul_of_nonneg_left ha2 (sq_nonneg a)
    have hpos : 0<a*(1+a)/(2*(a+2)) := by positivity
    nlinarith [sq_pos_of_pos ha]
  have hratio : 3/(4*(a+2))≤(3/8 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hconst : a^4/12+a^3/2+a^2/6-a+3*a/(4*(a+2))<0 := by
    have hinner : a^3/12+a^2/2+a/6-1+3/(4*(a+2))<0 := by linarith
    have hprod := mul_neg_of_pos_of_neg ha hinner
    have hid : a*(a^3/12+a^2/2+a/6-1+3/(4*(a+2)))=
        a^4/12+a^3/2+a^2/6-a+3*a/(4*(a+2)) := by ring
    rwa [hid] at hprod
  have hlin := mul_neg_of_neg_of_pos hlinear hμ
  linarith

end Dowling
