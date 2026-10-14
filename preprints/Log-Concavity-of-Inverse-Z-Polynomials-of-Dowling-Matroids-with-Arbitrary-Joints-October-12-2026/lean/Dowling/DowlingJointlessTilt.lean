import Dowling.DowlingJointlessDefinitions

noncomputable section
namespace Dowling

def jointlessTilt (s : ℝ) (f : ℝ→ℝ) (r : ℝ) : ℝ := s*f (r-1)+s⁻¹*f (r+1)-2*f r

 theorem jointlessTilt_add (s r : ℝ) (f g : ℝ→ℝ) :
    jointlessTilt s (fun x=>f x+g x) r=jointlessTilt s f r+jointlessTilt s g r := by
  unfold jointlessTilt
  ring

 theorem jointlessTilt_mul (s r c : ℝ) (f : ℝ→ℝ) :
    jointlessTilt s (fun x=>c*f x) r=c*jointlessTilt s f r := by
  unfold jointlessTilt
  ring

 theorem tilted_triple_nonneg {s fm fc fp : ℝ} (hs : 0<s) (hm : 0<fm)
    (hc : fc^2≤fm*fp) : 0≤s*fm+s⁻¹*fp-2*fc := by
  have hsq := sq_nonneg (s*fm-fc)
  have hfactor : s*fm*(s*fm+s⁻¹*fp-2*fc)=(s*fm-fc)^2+(fm*fp-fc^2) := by
    field_simp
    ring
  have hpos : 0<s*fm := mul_pos hs hm
  nlinarith

 theorem jointlessTilt_recip_nonneg {s r : ℝ} (hs : 0<s) (hr : 1<r) :
    0≤jointlessTilt s (fun x=>1/x) r := by
  apply tilted_triple_nonneg hs (by positivity)
  have hd : 0<(r-1)*(r+1) := by positivity
  have hr0 : 0<r := by linarith
  change (1/r)^2≤(1/(r-1))*(1/(r+1))
  rw [one_div_mul_one_div]
  rw [div_pow,one_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hr0) hd).mpr
  nlinarith

 theorem jointlessTilt_recip_pair_nonneg {s r : ℝ} (hs : 0<s) (hr : 1<r) :
    0≤jointlessTilt s (fun x=>1/(x*(x+1))) r := by
  apply tilted_triple_nonneg hs (by positivity)
  have h0 : 0<r := by linarith
  have h1 : 0<r-1 := by linarith
  have hp : 0<r+1 := by linarith
  have hpp : 0<r+1+1 := by linarith
  simp only [show r-1+1=r by ring]
  rw [div_pow,one_pow,one_div_mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos h0 hp))
    (mul_pos (mul_pos h1 h0) (mul_pos hp hpp))).mpr
  nlinarith [mul_pos h0 hp]

/-- The polynomial part of the exact normalized correction. -/
def jointlessQuadratic (a μ r : ℝ) : ℝ :=
  a^2*r^2/3+(a^2-(a-a^2/3)*μ)*r+
    (2*a-2*a^2/3)*μ^2-2*a^2*μ+a^2/6

def jointlessAdverse (r : ℝ) : ℝ := 1/(r^2*(r+1))

 theorem jointlessRatio_decomposition (a μ r : ℝ) (hr : r≠0) :
    jointlessRatioFunction a μ r=jointlessQuadratic a μ r+
      (a*(1-a)*μ/4-a^2/2)*(1/r)+(3*a^2/16)*(1/(r*(r+1)))-
      (a^2*μ/8)*jointlessAdverse r := by
  unfold jointlessRatioFunction jointlessCorrection jointlessQuadratic jointlessAdverse
  by_cases hr1 : r+1=0
  · simp [hr1]
    field_simp
    ring
  · field_simp
    ring

 theorem jointlessQuadratic_tilt (a μ r : ℝ) (hμ : 0<μ) :
    2*μ*(2*μ+1)*jointlessTilt (μ/(μ+1/2)) (jointlessQuadratic a μ) r=
      (a^2/3)*r^2+((3*a^2-a)*μ+5*a^2/3)*r+
      (-2*a+10*a^2/3)*μ^2+(11*a^2/3-a)*μ+3*a^2/2 := by
  have hm : μ≠0 := ne_of_gt hμ
  have hp : μ+1/2≠0 := by linarith
  unfold jointlessTilt jointlessQuadratic
  field_simp
  ring

 theorem jointlessQuadratic_tilt_lower {a μ r : ℝ} (ha : 0≤a) (hμ : 0<μ)
    (hr : 0≤r) (hrμ : r≤μ) :
    -a*μ*(3*μ+1)≤2*μ*(2*μ+1)*jointlessTilt (μ/(μ+1/2)) (jointlessQuadratic a μ) r := by
  rw [jointlessQuadratic_tilt a μ r hμ]
  have hrest : 0≤a*μ*(μ-r) := by positivity
  have hpos : 0≤a^2*(r^2/3+3*μ*r+5*r/3+10*μ^2/3+11*μ/3+3/2) := by positivity
  nlinarith

end Dowling
