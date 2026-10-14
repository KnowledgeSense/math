import CircleKernel.Definitions

set_option maxHeartbeats 30000
noncomputable section
open Complex MeasureTheory
namespace CircleKernel

theorem chord_norm (θ : ℝ) (hθ : 0<θ) (hθπ : θ<2*Real.pi) :
    ‖1-Complex.exp (Complex.I*θ)‖=2*Real.sin (θ/2) := by
  rw [norm_sub_rev,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_of_pos]
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem phase_sub_one_factor (θ : ℝ) :
    1-Complex.exp (Complex.I*θ)=
      (2*(Real.sin (θ/2):ℂ))*(-Complex.I*Complex.exp (((θ:ℂ)/2)*Complex.I)) := by
  let u : ℂ := ((θ:ℂ)/2)*Complex.I
  have hm : Complex.exp (-u)*Complex.exp u=1 := by rw [← Complex.exp_add]; simp
  have hp : Complex.exp u*Complex.exp u=Complex.exp (Complex.I*θ) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [u]
    ring
  have hs : 2*(Real.sin (θ/2):ℂ)=(Complex.exp (-u)-Complex.exp u)*Complex.I := by
    simpa [u,Complex.ofReal_div,neg_mul] using (Complex.two_sin (x:=((θ:ℂ)/2)))
  rw [hs]
  change 1-Complex.exp (Complex.I*θ)=(_)*(-Complex.I*Complex.exp u)
  rw [← hm,← hp]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

theorem mode_integrand_difference (n : ℕ) (θ : ℝ) (hθ : 0<θ) (hθπ : θ<2*Real.pi) :
    (1-Complex.exp (Complex.I*θ)^(n+1))/(‖1-Complex.exp (Complex.I*θ)‖:ℂ)-
      (1-Complex.exp (Complex.I*θ)^n)/(‖1-Complex.exp (Complex.I*θ)‖:ℂ)=
        -Complex.I*Complex.exp (((n:ℂ)+1/2)*Complex.I*θ) := by
  have hs : Real.sin (θ/2)≠0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  rw [chord_norm θ hθ hθπ]
  push_cast
  rw [← sub_div]
  have hnum : (1-Complex.exp (Complex.I*θ)^(n+1))-(1-Complex.exp (Complex.I*θ)^n)=
      Complex.exp (Complex.I*θ)^n*(1-Complex.exp (Complex.I*θ)) := by rw [pow_succ]; ring
  rw [hnum,phase_sub_one_factor]
  have hsin : Complex.sin ((θ:ℂ)/2)=(Real.sin (θ/2):ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using (Complex.ofReal_sin (θ/2)).symm
  rw [hsin]
  have hsC : (Real.sin (θ/2):ℂ)≠0 := by exact_mod_cast hs
  have he : Complex.exp (Complex.I*θ)^n*Complex.exp (((θ:ℂ)/2)*Complex.I)=
      Complex.exp (((n:ℂ)+1/2)*Complex.I*θ) := by
    rw [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    ring
  calc
    _ = -Complex.I*(Complex.exp (Complex.I*θ)^n*Complex.exp (((θ:ℂ)/2)*Complex.I)) := by
      rw [mul_div_assoc,mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hsC)]
      ring
    _ = _ := by rw [he]

end CircleKernel
