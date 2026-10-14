import AperyMoments.EllipticReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def arcsineChange (k θ : ℝ) : ℝ := Real.arcsin (k * Real.sin θ)
def arcsineChangeDerivative (k θ : ℝ) : ℝ :=
  k * Real.cos θ / Real.sqrt (1 - (k * Real.sin θ) ^ 2)

theorem arcsineChange_argument_lt {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (θ : ℝ) :
    |k * Real.sin θ| < 1 := by
  rw [abs_mul, abs_of_pos hk0]
  exact (mul_le_of_le_one_right hk0.le (Real.abs_sin_le_one θ)).trans_lt hk1

theorem arcsineChange_hasDerivAt {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (θ : ℝ) :
    HasDerivAt (arcsineChange k) (arcsineChangeDerivative k θ) θ := by
  have ha := abs_lt.mp (arcsineChange_argument_lt hk0 hk1 θ)
  have h := (Real.hasDerivAt_arcsin (ne_of_gt ha.1) (ne_of_lt ha.2)).comp θ
    ((Real.hasDerivAt_sin θ).const_mul k)
  convert h using 1
  · rfl
  · unfold arcsineChangeDerivative
    ring

theorem inverse_sqrt_rpow {a : ℝ} (ha : 0 ≤ a) :
    a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
  rw [Real.rpow_neg ha, ← Real.sqrt_eq_rpow]

/-- The exact arcsine substitution evaluating the positive branch-cut contribution. -/
theorem arcsine_substitution_positive {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (∫ θ in (0 : ℝ)..Real.arcsin k, (1 - Real.sin θ ^ 2 / k ^ 2) ^ (-(1 / 2 : ℝ))) =
      k * ellipticK (k ^ 2) := by
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := arcsineChange k) (f' := arcsineChangeDerivative k)
    (g := fun θ => (1 - Real.sin θ ^ 2 / k ^ 2) ^ (-(1 / 2 : ℝ)))
    (by unfold arcsineChange; fun_prop)
    (fun θ _ => arcsineChange_hasDerivAt hk0 hk1 θ)
    (by
      intro θ hθ
      rw [min_eq_left (by positivity), max_eq_right (by positivity)] at hθ
      apply div_nonneg (mul_nonneg hk0.le _) (Real.sqrt_nonneg _)
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le)
  simp only [arcsineChange, Real.sin_zero, mul_zero, Real.arcsin_zero,
    Real.sin_pi_div_two, mul_one] at he
  rw [← he, ellipticK, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (Real.pi / 2) :
      volume {Real.pi / 2} = 0)
  filter_upwards [hne] with θ hθne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], lt_of_le_of_ne hθ.2 hθne⟩
  have ha := abs_lt.mp (arcsineChange_argument_lt hk0 hk1 θ)
  have hb : 0 < 1 - (k * Real.sin θ) ^ 2 := by nlinarith
  dsimp only [Function.comp_apply, arcsineChange, arcsineChangeDerivative]
  rw [Real.sin_arcsin ha.1.le ha.2.le]
  have hs : (k * Real.sin θ) ^ 2 / k ^ 2 = Real.sin θ ^ 2 := by field_simp
  rw [hs, show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
    inverse_sqrt_rpow (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hcos,
    inverse_sqrt_rpow (by nlinarith [show (k * Real.sin θ) ^ 2 = k ^ 2 * Real.sin θ ^ 2 by ring])]
  rw [show (k * Real.sin θ) ^ 2 = k ^ 2 * Real.sin θ ^ 2 by ring]
  field_simp

end AperyMoments
