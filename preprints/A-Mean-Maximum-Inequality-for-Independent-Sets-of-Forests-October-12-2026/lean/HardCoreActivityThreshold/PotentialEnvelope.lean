import HardCoreActivityThreshold.ActivityContraction

namespace HardCoreActivityThreshold

theorem potential_exponential_bound (y : ℝ) (hy : 0≤y) : potential y≤2*Real.exp y := by
  have hz := cubicCenter_bounds
  have hzsq : cubicCenter^2≤9 := by
    have h0 : 0≤3-cubicCenter := by linarith [hz.2]
    have h1 : 0≤3+cubicCenter := by linarith [hz.1]
    nlinarith [mul_nonneg h0 h1]
  have hquad : (y-cubicCenter)^2≤2*y^2+2*cubicCenter^2 := by
    nlinarith [sq_nonneg (y+cubicCenter)]
  have hm := mul_le_mul_of_nonneg_left hquad hy
  have h1 := Real.pow_div_factorial_le_exp y hy 1
  have h3 := Real.pow_div_factorial_le_exp y hy 3
  norm_num at h1 h3
  have hzy := mul_le_mul_of_nonneg_left hzsq hy
  unfold potential cubicPotential cubicCoefficient
  nlinarith [Real.exp_pos y]

theorem potential_exponential_envelope (y : ℝ) (hy : 0≤y) :
    Real.exp (-y)*potential y≤2 := by
  have h := mul_le_mul_of_nonneg_left (potential_exponential_bound y hy) (Real.exp_pos (-y)).le
  have he : Real.exp (-y)*Real.exp y=1 := by rw [←Real.exp_add]; simp
  nlinarith

end HardCoreActivityThreshold
