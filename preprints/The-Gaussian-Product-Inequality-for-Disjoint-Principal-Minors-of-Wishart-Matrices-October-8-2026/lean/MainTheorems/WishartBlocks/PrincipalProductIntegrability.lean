import MainTheorems.WishartBlocks.RegressionResponseIntegral
import MainTheorems.WishartBlocks.SingleResponseRegularity
import MainTheorems.WishartBlocks.WishartMarginals

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

theorem principal_matrix_norm_le {p m : ℕ} (e : Fin m → Fin p)
    (W : Matrix (Fin p) (Fin p) ℝ) : ‖W.submatrix e e‖ ≤ ‖W‖ :=
  (Matrix.norm_le_iff (norm_nonneg W)).mpr fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm W

theorem bartlettLaw_real_growth_integrable {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (S : Matrix (Fin p) (Fin p) ℝ)
    {f : Matrix (Fin p) (Fin p) ℝ → ℝ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hB : ∀ W, ‖f W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable f (bartlettLaw α S) := by
  let k := ⌈β⌉₊
  apply ((bartlett_polynomial_integrable hα S k).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun W => by
    calc
      ‖f W‖ ≤ C * (1 + ‖W‖) ^ β := hB W
      _ ≤ C * (1 + ‖W‖) ^ k := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg W]) (Nat.le_ceil β)) hC

theorem bartlett_principal_integral {p m : ℕ} {α : ℝ}
    (hαp : (p : ℝ) - 1 < α) (hαm : (m : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) (e : Fin m → Fin p)
    {g : Matrix (Fin m) (Fin m) ℝ → ℝ} (hg : Measurable g) :
    (∫ W, g (W.submatrix e e) ∂(bartlettLaw α S)) =
      ∫ B, g B ∂(bartlettLaw α (S.submatrix e e)) := by
  rw [← bartlettLaw_principal_marginal hαp hαm hS e,
    integral_map (by fun_prop : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => W.submatrix e e)).aemeasurable
      hg.aestronglyMeasurable]

theorem principal_power_product_integrable {p k m : ℕ} {α a C β : ℝ}
    (hα : (p : ℝ) - 1 < α) (ha : 0 ≤ a) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (S : Matrix (Fin p) (Fin p) ℝ) (e : Fin k → Fin p) (f : Fin m → Fin p)
    {g : Matrix (Fin m) (Fin m) ℝ → ℝ} (hg : Measurable g)
    (hgB : ∀ B, ‖g B‖ ≤ C * (1 + ‖B‖) ^ β) :
    Integrable (fun W => (W.submatrix e e).det ^ a * g (W.submatrix f f)) (bartlettLaw α S) := by
  let D := (Fintype.card (Equiv.Perm (Fin k)) : ℝ) ^ a
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdMeas : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ =>
      (W.submatrix e e).det ^ a) := by fun_prop
  apply bartlettLaw_real_growth_integrable hα S
    (hdMeas.mul (hg.comp (by fun_prop))) (C := D * C) (β := (k : ℝ) * a + β)
    (mul_nonneg hD hC)
  intro W
  have hd : ‖(W.submatrix e e).det ^ a‖ ≤ D * (1 + ‖W‖) ^ ((k : ℝ) * a) := by
    simpa only [add_zero, norm_zero, add_zero, one_pow, mul_one] using
      determinant_shift_power_growth e (0 : Matrix (Fin k) (Fin k) ℝ) W ha
  have hgW : ‖g (W.submatrix f f)‖ ≤ C * (1 + ‖W‖) ^ β :=
    (hgB _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith [principal_matrix_norm_le f W]) hβ) hC)
  change ‖(W.submatrix e e).det ^ a * g (W.submatrix f f)‖ ≤
    D * C * (1 + ‖W‖) ^ ((k : ℝ) * a + β)
  rw [norm_mul]
  calc
    _ ≤ (D * (1 + ‖W‖) ^ ((k : ℝ) * a)) * (C * (1 + ‖W‖) ^ β) :=
      mul_le_mul hd hgW (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by positivity)]; ring

theorem principal_growth_integrable {p m : ℕ} {α C β : ℝ}
    (hα : (p : ℝ) - 1 < α) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (S : Matrix (Fin p) (Fin p) ℝ) (e : Fin m → Fin p)
    {g : Matrix (Fin m) (Fin m) ℝ → ℝ} (hg : Measurable g)
    (hgB : ∀ B, ‖g B‖ ≤ C * (1 + ‖B‖) ^ β) :
    Integrable (fun W => g (W.submatrix e e)) (bartlettLaw α S) := by
  apply bartlettLaw_real_growth_integrable hα S (hg.comp (by fun_prop)) hC
  intro W
  exact (hgB _).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith [principal_matrix_norm_le e W]) hβ) hC)

end ResearchMain.WishartBlocks
