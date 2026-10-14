import AperyMoments.ProductArcsineMoments
import Mathlib.Data.Nat.Choose.Central

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem positiveArcsineMoment_sin (n : ℕ) :
    positiveArcsineMoment n = ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ n := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos)
    (g := fun t => t ^ n * positiveArcsineWeight t)
    Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ)
    (fun θ hθ => (Real.cos_pos_of_mem_Ioo ⟨by
      rw [min_eq_left (by positivity)] at hθ
      linarith [hθ.1, Real.pi_pos], by simpa only [max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ.2⟩).le)
  simp only [Real.sin_zero, Real.sin_pi_div_two] at h
  unfold positiveArcsineMoment
  rw [← h]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
  filter_upwards [hne] with θ hne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  dsimp only [Function.comp_apply]
  rw [mul_assoc, positiveArcsine_jacobian ⟨hθ.1, lt_of_le_of_ne hθ.2 hne⟩, mul_one]

theorem positiveArcsineMoment_even (n : ℕ) :
    positiveArcsineMoment (2 * n) = (Real.pi / 2) * (n.centralBinom : ℝ) / 4 ^ n := by
  rw [positiveArcsineMoment_sin]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, integral_sin_pow]
    simp only [Real.sin_zero, zero_pow (by omega : 2 * n + 1 ≠ 0), Real.cos_zero, zero_mul,
      Real.sin_pi_div_two, one_pow, Real.cos_pi_div_two, mul_zero, sub_self, zero_div, zero_add]
    rw [ih]
    have hb := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
    push_cast at hb
    push_cast
    rw [pow_succ]
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    nlinarith [hb]

theorem cosineMoment_even (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * n)) = Real.pi * (n.centralBinom : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, integral_cos_pow]
    simp only [Real.sin_pi, mul_zero, Real.sin_zero, sub_self, zero_div, zero_add]
    rw [ih]
    have hb := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
    push_cast at hb
    push_cast
    rw [pow_succ]
    field_simp
    nlinarith [hb]

theorem cosineMoment_odd (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * n + 1)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, integral_cos_pow]
    simp only [Real.sin_pi, mul_zero, Real.sin_zero, sub_self, zero_div, zero_add, ih, mul_zero]

end AperyMoments
