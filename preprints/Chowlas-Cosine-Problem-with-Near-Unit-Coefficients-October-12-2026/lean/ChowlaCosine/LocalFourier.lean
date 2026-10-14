import ChowlaCosine.LocalForms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ChowlaCosine

noncomputable def omega : ℂ := ⟨Real.sqrt 2 / 4, Real.sqrt 2 / 4⟩

noncomputable def lambda (a b c : ℝ) : ℂ := 2 * (b : ℂ) + Complex.I * ((c-a : ℝ) : ℂ)

noncomputable def rho (z : Fin 5 → ℝ) : ℂ :=
  lambda (z 1) (z 2) (z 3)^2 - omega * lambda (z 0) (z 1) (z 2)^2 -
    star omega * lambda (z 2) (z 3) (z 4)^2

theorem omega_eq : omega = (1+Complex.I)/(2*((Real.sqrt 2 : ℝ):ℂ)) := by
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply Complex.ext <;> simp [omega, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  all_goals field_simp
  all_goals nlinarith

theorem rho_re (z : Fin 5 → ℝ) : (rho z).re = R z := by
  simp [rho, lambda, omega, R, localReal, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem rho_neg_im (z : Fin 5 → ℝ) : -(rho z).im = J z := by
  simp [rho, lambda, omega, J, localImaginary, pow_two, Complex.mul_re, Complex.mul_im]
  ring


theorem phase_eq_two_omega : Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I) = 2*omega := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]
    simp [omega, Complex.mul_re]
    ring
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]
    simp [omega, Complex.mul_im]
    ring

end ChowlaCosine
