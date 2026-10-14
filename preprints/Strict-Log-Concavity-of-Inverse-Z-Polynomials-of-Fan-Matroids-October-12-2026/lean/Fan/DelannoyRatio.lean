import Fan.DelannoyLogDerivative

noncomputable section
open Polynomial
namespace Fan

private theorem ratio_algebra (a b z d d₁ d₂ i l₁ l₂ u₁ u₂ : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a+1 ≠ 0) (hb1 : b+1 ≠ 0)
    (hl₁ : a*l₁=a*d-z*d₁) (hl₂ : b*l₂=b*d-z*d₁)
    (hu₁ : u₁=(1-z)*d+(b+1)*z*i) (hu₂ : u₂=(1-z)*d+(a+1)*z*i)
    (hI : (1-z)*d₁+(a+b+1)*d=(a+1)*(b+1)*i)
    (hO : z*(1-z)*d₂+(1+(a+b-1)*z)*d₁-a*b*d=0) :
    (u₂*l₂-l₁*u₁)*(a*b*(a+1)*(b+1)) =
      (b-a)*(a+b+1)*z^2*(d*d₁-(1-z)*(d₂*d-d₁^2)) := by
  have hl₁' : l₁=(a*d-z*d₁)/a := by apply (eq_div_iff ha).mpr; nlinarith only [hl₁]
  have hl₂' : l₂=(b*d-z*d₁)/b := by apply (eq_div_iff hb).mpr; nlinarith only [hl₂]
  have hi' : i=((1-z)*d₁+(a+b+1)*d)/((a+1)*(b+1)) := by
    apply (eq_div_iff (mul_ne_zero ha1 hb1)).mpr
    nlinarith only [hI]
  rw [hl₁',hl₂',hu₁,hu₂,hi']
  field_simp
  linear_combination (b-a)*(a+b+1)*z*d*hO

/-- The strict adjacent comparison for all positive arguments and unequal parameters. -/
theorem delannoy_parameter_ratio (a b : ℕ) (hab : a < b) {z : ℝ} (hz : 0 < z) :
    delannoy z (a+1) (b+2) * delannoy z (a+1) b >
      delannoy z a (b+1) * delannoy z (a+2) (b+1) := by
  let p := delannoyPolynomial (a+1) (b+1)
  let d := delannoy z (a+1) (b+1)
  let d₁ := p.derivative.eval z
  let d₂ := p.derivative.derivative.eval z
  let i := (delannoyMeanPolynomial (a+1) (b+1)).eval z
  have hd : 0 < d := delannoy_pos hz.le _ _
  have ha : (a:ℝ)+1 > 0 := by positivity
  have hb : (b:ℝ)+1 > 0 := by positivity
  have ha1 : (a:ℝ)+1+1 > 0 := by positivity
  have hb1 : (b:ℝ)+1+1 > 0 := by positivity
  have hl₁ : ((a:ℝ)+1)*delannoy z a (b+1) = ((a:ℝ)+1)*d-z*d₁ := by
    have h := congrArg (eval z) (delannoy_lower_left a (b+1))
    simpa only [eval_mul,eval_C,eval_sub,eval_X,delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one]
      using h
  have hl₂ : ((b:ℝ)+1)*delannoy z (a+1) b = ((b:ℝ)+1)*d-z*d₁ := by
    have h := delannoy_lower_left b (a+1)
    rw [delannoyPolynomial_symm b (a+1),delannoyPolynomial_symm (b+1) (a+1)] at h
    simpa only [eval_mul,eval_C,eval_sub,eval_X,delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one]
      using congrArg (eval z) h
  have hu₁ : delannoy z (a+2) (b+1) = (1-z)*d+((b:ℝ)+1+1)*z*i := by
    have h := congrArg (eval z) (delannoy_raise_left (a+1) (b+1))
    simpa only [eval_mul,eval_C,eval_sub,eval_X,eval_add,eval_one,
      delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.reduceAdd,add_assoc,Nat.cast_ofNat,one_add_one_eq_two] using h
  have hu₂ : delannoy z (a+1) (b+2) = (1-z)*d+((a:ℝ)+1+1)*z*i := by
    have h := delannoy_raise_left (b+1) (a+1)
    rw [delannoyPolynomial_symm (b+1+1) (a+1),delannoyPolynomial_symm (b+1) (a+1),
      delannoyMeanPolynomial_symm (b+1) (a+1)] at h
    simpa only [eval_mul,eval_C,eval_sub,eval_X,eval_add,eval_one,
      delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.reduceAdd,add_assoc,Nat.cast_ofNat,one_add_one_eq_two] using congrArg (eval z) h
  have hI : (1-z)*d₁+((a:ℝ)+1+((b:ℝ)+1)+1)*d =
      ((a:ℝ)+1+1)*((b:ℝ)+1+1)*i := by
    simpa only [eval_mul,eval_C,eval_sub,eval_X,eval_add,eval_one,
      delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one] using
      congrArg (eval z) (delannoy_integrated_equation (a+1) (b+1))
  have hO : z*(1-z)*d₂+(1+((a:ℝ)+1+((b:ℝ)+1)-1)*z)*d₁-
      ((a:ℝ)+1)*((b:ℝ)+1)*d = 0 := by
    simpa only [eval_mul,eval_C,eval_sub,eval_X,eval_add,eval_one,eval_zero,
      delannoyPolynomial_eval,Nat.cast_add,Nat.cast_one] using
      congrArg (eval z) (delannoy_differential_equation (a+1) (b+1))
  have hn : p.natDegree ≠ 0 := by
    intro h
    have hc := coeff_eq_zero_of_natDegree_lt (show p.natDegree < 1 by omega)
    have he : p.coeff 1 = ((a:ℝ)+1)*((b:ℝ)+1) := by
      simp [p,delannoyPolynomial_coeff]
    rw [he] at hc
    exact (mul_pos ha hb).ne' hc
  have hlog := negative_roots_log_positive (delannoyPolynomial_splits (a+1) (b+1) (by omega))
    hn (delannoyPolynomial_roots_neg (a+1) (b+1) (by omega)) hz
  change 0 < d₁/p.eval z-(1-z)*((d₂*p.eval z-d₁^2)/(p.eval z)^2) at hlog
  have hpz : p.eval z = d := delannoyPolynomial_eval z _ _
  rw [hpz] at hlog
  have hq : 0 < d*d₁-(1-z)*(d₂*d-d₁^2) := by
    have hh := mul_pos hlog (sq_pos_of_pos hd)
    have he : (d₁/d-(1-z)*((d₂*d-d₁^2)/d^2))*d^2 =
        d*d₁-(1-z)*(d₂*d-d₁^2) := by field_simp
    rwa [he] at hh
  have hid := ratio_algebra ((a:ℝ)+1) ((b:ℝ)+1) z d d₁ d₂ i _ _ _ _
    ha.ne' hb.ne' ha1.ne' hb1.ne' hl₁ hl₂ hu₁ hu₂ hI hO
  have hba : 0 < ((b:ℝ)+1)-((a:ℝ)+1) := by
    have hh : (a:ℝ) < b := by exact_mod_cast hab
    linarith
  have hpos : 0 < (((b:ℝ)+1)-((a:ℝ)+1))*((a:ℝ)+1+((b:ℝ)+1)+1)*z^2*
      (d*d₁-(1-z)*(d₂*d-d₁^2)) := by positivity
  rw [← hid] at hpos
  have hs : 0 < ((a:ℝ)+1)*((b:ℝ)+1)*((a:ℝ)+1+1)*((b:ℝ)+1+1) := by positivity
  have he := (mul_pos_iff_of_pos_right hs).mp hpos
  linarith

/-- The fixed-imbalance adjacent ratio used by the kernel convolution argument. -/
theorem delannoy_adjacent_ratio (z : ℝ) (hz : 0 < z) (e m : ℕ) :
    delannoy z (m+1) (m+e+3) * delannoy z (m+1) (m+e+1) >
      delannoy z m (m+e+2) * delannoy z (m+2) (m+e+2) := by
  simpa only [Nat.add_assoc] using delannoy_parameter_ratio m (m+e+1) (by omega) hz

end Fan
