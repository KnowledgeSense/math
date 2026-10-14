import Dowling.DowlingJointlessInternal

noncomputable section
namespace Dowling

 theorem jointless_bernoulli (μ : ℝ) (hμ : 0<μ) (e : ℕ) :
    (μ/(μ+1/2))^e*(1+(e : ℝ)/(2*μ))≤1 := by
  have hs : 0≤μ/(μ+1/2) := by positivity
  have hrec : 0≤(1 : ℝ)/(2*μ) := by positivity
  have h := one_add_mul_le_pow (a := (1 : ℝ)/(2*μ)) (by linarith) e
  have heq : μ/(μ+1/2)*(1+1/(2*μ))=1 := by field_simp
  have hp := mul_le_mul_of_nonneg_left h (pow_nonneg hs e)
  rw [← mul_pow,heq,one_pow] at hp
  convert hp using 1
  ring

 theorem jointlessNormalizedWeight_gt_third {a μ : ℝ} (ha : 0≤a) (ha2 : a≤1/2)
    (hμ : 5/2≤μ) (j : ℕ) (hj : 2≤j) (hr : 1≤μ+1/2-j) :
    1/3<jointlessNormalizedWeight a μ j := by
  let r : ℝ := μ+1/2-j
  have hμ0 : 0<μ := by linarith
  have hrμ : r≤μ := by
    dsimp [r]
    have hjR : (2 : ℝ)≤j := by exact_mod_cast hj
    linarith
  have hP : jointlessRatioFunction a μ r<μ^2-μ*r/3-μ/2 :=
    (jointlessRatio_le_half ha ha2 hμ hr hrμ).trans_lt (jointlessRatio_half_bound hμ hr hrμ)
  have hcast : ((j-2 : ℕ) : ℝ)=(j : ℝ)-2 := by rw [Nat.cast_sub hj]; norm_num
  have heq : μ^2-μ*r/3-μ/2=(2/3 : ℝ)*μ^2*(1+((j-2 : ℕ) : ℝ)/(2*μ)) := by
    dsimp [r]
    rw [hcast]
    field_simp
    ring
  rw [heq] at hP
  have hpow : 0<(μ/(μ+1/2))^(j-2) := by positivity
  have hmul := mul_lt_mul_of_pos_left hP hpow
  have hBern := jointless_bernoulli μ hμ0 (j-2)
  have hbound := mul_le_mul_of_nonneg_left hBern (show 0≤(2/3 : ℝ)*μ^2 by positivity)
  have hfinal : (μ/(μ+1/2))^(j-2)*jointlessRatioFunction a μ r<(2/3 : ℝ)*μ^2 := by
    nlinarith [hmul,hbound]
  have hdiv := (div_lt_iff₀ (sq_pos_of_pos hμ0)).mpr hfinal
  rw [jointlessNormalizedWeight_large a μ hμ0 j hj]
  dsimp [r] at hdiv
  linarith

end Dowling
