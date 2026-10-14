import AperyMoments.ArcsineSubstitution
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def productArcsineChange (a θ : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + (1 - a ^ 2) * Real.sin θ ^ 2)

def productArcsineDerivative (a θ : ℝ) : ℝ :=
  (1 - a ^ 2) * Real.sin θ * Real.cos θ / productArcsineChange a θ

def productArcsineKernel (a r : ℝ) : ℝ :=
  ((1 - r ^ 2) * (r ^ 2 - a ^ 2)) ^ (-(1 / 2 : ℝ))

theorem productArcsine_base_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    0 < a ^ 2 + (1 - a ^ 2) * Real.sin θ ^ 2 := by
  have h1 : 0 < 1 - a ^ 2 := by nlinarith
  nlinarith [sq_pos_of_pos ha, mul_nonneg h1.le (sq_nonneg (Real.sin θ))]

theorem productArcsineChange_hasDerivAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    HasDerivAt (productArcsineChange a) (productArcsineDerivative a θ) θ := by
  have h := ((((Real.hasDerivAt_sin θ).pow 2).const_mul (1 - a ^ 2)).const_add (a ^ 2)).sqrt
    (productArcsine_base_pos ha ha1 θ).ne'
  convert h using 1
  · rfl
  · unfold productArcsineDerivative productArcsineChange
    simp only [Nat.reduceSub, pow_one, Pi.pow_apply]
    ring

theorem productArcsineDerivative_nonneg {a θ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) : 0 ≤ productArcsineDerivative a θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  unfold productArcsineDerivative productArcsineChange
  positivity

theorem productArcsine_jacobian {a θ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    productArcsineKernel a (productArcsineChange a θ) * productArcsineDerivative a θ =
      (1 - (1 - a ^ 2) * Real.cos θ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  have hbase := productArcsine_base_pos ha ha1 θ
  have hsq : productArcsineChange a θ ^ 2 = a ^ 2 + (1 - a ^ 2) * Real.sin θ ^ 2 :=
    Real.sq_sqrt hbase.le
  have he : (1 - productArcsineChange a θ ^ 2) * (productArcsineChange a θ ^ 2 - a ^ 2) =
      ((1 - a ^ 2) * Real.sin θ * Real.cos θ) ^ 2 := by
    rw [hsq]
    rw [mul_pow, mul_pow, show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
    ring
  have hr : 1 - (1 - a ^ 2) * Real.cos θ ^ 2 = a ^ 2 + (1 - a ^ 2) * Real.sin θ ^ 2 := by
    rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
    ring
  unfold productArcsineKernel productArcsineDerivative
  rw [he, inverse_sqrt_rpow (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (mul_pos hb hs) hc), hr, inverse_sqrt_rpow hbase.le]
  unfold productArcsineChange
  field_simp

theorem ellipticK_cos_integral {m : ℝ} :
    (∫ θ in (0 : ℝ)..Real.pi / 2, (1 - m * Real.cos θ ^ 2) ^ (-(1 / 2 : ℝ))) = ellipticK m := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)))
    (a := (0 : ℝ)) (b := Real.pi / 2) (Real.pi / 2)
  simpa only [Real.sin_pi_div_two_sub, sub_self, sub_zero, ellipticK] using h

/-- The exact product-arcsine density integral, with the parameter convention of K. -/
theorem productArcsine_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ r in a..1, productArcsineKernel a r) = ellipticK (1 - a ^ 2) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := productArcsineChange a) (f' := productArcsineDerivative a) (g := productArcsineKernel a)
    (by unfold productArcsineChange; fun_prop)
    (fun θ _ => productArcsineChange_hasDerivAt ha ha1 θ)
    (fun θ hθ => productArcsineDerivative_nonneg ha ha1 (by
      simpa only [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2), max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ))
  have h0 : productArcsineChange a 0 = a := by
    simp only [productArcsineChange, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have h1 : productArcsineChange a (Real.pi / 2) = 1 := by
    simp [productArcsineChange]
  rw [h0, h1] at h
  rw [← h, ← ellipticK_cos_integral]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
  filter_upwards [hne] with θ hne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  exact productArcsine_jacobian ha ha1 ⟨hθ.1, lt_of_le_of_ne hθ.2 hne⟩

theorem productArcsine_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IntervalIntegrable (productArcsineKernel a) volume a 1 := by
  have h := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := productArcsineChange a) (f' := productArcsineDerivative a) (g := productArcsineKernel a)
    (by unfold productArcsineChange; fun_prop)
    (fun θ _ => productArcsineChange_hasDerivAt ha ha1 θ)
    (fun θ hθ => productArcsineDerivative_nonneg ha ha1 (by
      simpa only [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2), max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ))
  have h0 : productArcsineChange a 0 = a := by
    simp only [productArcsineChange, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have h1 : productArcsineChange a (Real.pi / 2) = 1 := by simp [productArcsineChange]
  rw [h0, h1] at h
  apply h.mp
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
  apply (integrableOn_congr_fun (fun θ hθ => productArcsine_jacobian ha ha1 hθ) measurableSet_Ioo).mpr
  have hc : Continuous (fun θ : ℝ => (1 - (1 - a ^ 2) * Real.cos θ ^ 2) ^ (-(1 / 2 : ℝ))) := by
    apply Continuous.rpow_const (by fun_prop)
    intro θ
    left
    have he : 1 - (1 - a ^ 2) * Real.cos θ ^ 2 = a ^ 2 + (1 - a ^ 2) * Real.sin θ ^ 2 := by
      rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
      ring
    rw [he]
    exact (productArcsine_base_pos ha ha1 θ).ne'
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

end AperyMoments
