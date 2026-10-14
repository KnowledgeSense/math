import MainTheorems.DiagonalSchatten.HyperbolicBounds

namespace ResearchMain.DiagonalSchatten

theorem tanh_deriv (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  convert hd using 1
  · funext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]

theorem tanh_scale_strict {m x : ℝ} (hm : 1 < m) (hx : 0 < x) :
    Real.tanh (m * x) < m * Real.tanh x := by
  let f : ℝ → ℝ := fun y => m * Real.tanh y - Real.tanh (m * y)
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hder (y : ℝ) :
      HasDerivAt f
        (m * (1 / Real.cosh y ^ 2 - 1 / Real.cosh (m * y) ^ 2)) y := by
    have hd := ((tanh_deriv y).const_mul m).sub
      ((tanh_deriv (m * y)).comp y ((hasDerivAt_id y).const_mul m))
    convert hd using 1
    · rfl
    · ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · have hd : ∀ y, DifferentiableAt ℝ f y := fun y => (hder y).differentiableAt
      exact (show Differentiable ℝ f from hd).continuous.continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hder y).deriv]
      have hyp : 0 < y := hy
      have hlt : y < m * y := by nlinarith
      have hc : Real.cosh y < Real.cosh (m * y) :=
        Real.cosh_strictMonoOn hyp.le (mul_nonneg hm0.le hyp.le) hlt
      have hs : Real.cosh y ^ 2 < Real.cosh (m * y) ^ 2 := by
        nlinarith [Real.cosh_pos y, Real.cosh_pos (m * y)]
      have hi : 1 / Real.cosh (m * y) ^ 2 < 1 / Real.cosh y ^ 2 :=
        one_div_lt_one_div_of_lt (sq_pos_of_pos (Real.cosh_pos y)) hs
      exact mul_pos hm0 (sub_pos.mpr hi)
  have he := hmono (by simp) hx.le hx
  dsimp [f] at he
  simp only [mul_zero, Real.tanh_zero, sub_self] at he
  linarith

theorem tanh_scale_between_zero_one {q x : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hx : 0 < x) : q * Real.tanh x < Real.tanh (q * x) := by
  have hm : 1 < q⁻¹ := by
    exact (one_lt_inv₀ hq).mpr hq1
  have he := tanh_scale_strict hm (mul_pos hq hx)
  rw [inv_mul_cancel_left₀ hq.ne'] at he
  have he' := mul_lt_mul_of_pos_left he hq
  simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using he'

end ResearchMain.DiagonalSchatten
