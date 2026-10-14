import Dowling.DowlingJointlessPositivity

noncomputable section
namespace Dowling

 theorem jointlessNormalizedWeight_half_zero_lt (μ : ℝ) (hμ : 0<μ) :
    jointlessNormalizedWeight (1/2) μ 0<1/2 := by
  rw [jointlessNormalizedWeight_zero (1/2) μ hμ]
  apply (div_lt_iff₀ (by positivity)).mpr
  linarith

 theorem jointlessHalf_second_reserve (r : ℝ) (hr : 0<r) :
    jointlessCorrection (1/2) (r+3/2) r-r*(r+3/2)^2/4=
      (r+3/2)^3/4-(r+3/2)^2/4-13*(r+3/2)/48+1/8-
        (r+3/2)/(32*r)+1/(16*(r+1)) := by
  have hr1 : r+1≠0 := by linarith
  unfold jointlessCorrection
  field_simp
  ring

 theorem jointlessNormalizedWeight_half_two_lt {μ : ℝ} (hμ : 7/4≤μ) :
    jointlessNormalizedWeight (1/2) μ 2<3/4 := by
  let r := μ-3/2
  have hr : 1/4≤r := by dsimp [r]; linarith
  have hr0 : 0<r := by linarith
  have hm0 : 0<μ := by linarith
  have hμr : μ=r+3/2 := by dsimp [r]; ring
  have hid := jointlessHalf_second_reserve r hr0
  rw [← hμr] at hid
  have hfrac : μ/(32*r)≤(7/32 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [hμr]
    linarith
  have hpoly : 0<μ^3/4-μ^2/4-13*μ/48+1/8-7/32 := by
    have hcube : 0≤(μ-7/4)^3 := pow_nonneg (by linarith) 3
    nlinarith [sq_nonneg (μ-7/4)]
  have hpos : 0<1/(16*(r+1)) := by positivity
  have hc : r*μ^2/4<jointlessCorrection (1/2) μ r := by linarith
  have hP : μ^2/4<jointlessRatioFunction (1/2) μ r := by
    unfold jointlessRatioFunction
    apply (lt_div_iff₀ hr0).mpr
    nlinarith
  have hdiv : (1/4 : ℝ)<jointlessRatioFunction (1/2) μ r/μ^2 :=
    (lt_div_iff₀ (sq_pos_of_pos hm0)).mpr (by nlinarith)
  rw [jointlessNormalizedWeight_large (1/2) μ hm0 2 le_rfl]
  norm_num only
  rw [show μ+1/2-2=r by dsimp [r]; ring]
  simp only [pow_zero,one_mul]
  linarith

 theorem dowling_half_interpolation_polynomial {θ : ℝ} (_hθ : 0≤θ) (hθ1 : θ≤1) :
    (1-θ/2)*(1-θ/4)<2*(1-5*θ/9)^2 := by
  have hp : 0≤(1-θ)*(635-319*θ) := mul_nonneg (by linarith) (by linarith)
  nlinarith

 theorem dowling_half_boundary_payment {um uc up qm qc qp θ : ℝ}
    (hum : 0<um) (_huc : 0<uc) (hup : 0<up)
    (hbase : 2*um*up<uc^2) (hqm : 0<qm) (hqc : 0<qc) (hqp : 0<qp)
    (hqmB : qm<1/2) (hqcB : 4/9<qc) (hqpB : qp<3/4)
    (hθ : 0≤θ) (hθ1 : θ≤1) :
    (um*(1-θ+θ*qm))*(up*(1-θ+θ*qp))<(uc*(1-θ+θ*qc))^2 := by
  have hqm0 := dowling_interpolated_pos hqm hθ hθ1
  have hqc0 := dowling_interpolated_pos hqc hθ hθ1
  have hqp0 := dowling_interpolated_pos hqp hθ hθ1
  have hm : 1-θ+θ*qm≤1-θ/2 := by nlinarith
  have hc : 1-5*θ/9≤1-θ+θ*qc := by nlinarith
  have hp : 1-θ+θ*qp≤1-θ/4 := by nlinarith
  have hmul := mul_le_mul hm hp hqp0.le (by linarith : 0≤1-θ/2)
  have hsq : (1-5*θ/9)^2≤(1-θ+θ*qc)^2 :=
    (sq_le_sq₀ (by linarith) hqc0.le).mpr hc
  have hpoly := dowling_half_interpolation_polynomial hθ hθ1
  have hstrict : (1-θ+θ*qm)*(1-θ+θ*qp)<2*(1-θ+θ*qc)^2 := by nlinarith
  have hweight := mul_lt_mul_of_pos_left hstrict (mul_pos hum hup)
  have hbase' := mul_lt_mul_of_pos_right hbase (sq_pos_of_pos hqc0)
  nlinarith

end Dowling
