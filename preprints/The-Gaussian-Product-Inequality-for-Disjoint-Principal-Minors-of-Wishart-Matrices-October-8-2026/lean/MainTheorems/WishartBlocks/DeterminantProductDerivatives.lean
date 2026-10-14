import MainTheorems.WishartBlocks.DeterminantDerivatives
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem product_logarithmic_derivative {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (u : ι → ℝ)
    (hf : ∀ i, HasDerivAt (f i) (f i 0 * u i) 0) :
    HasDerivAt (fun t => ∏ i, f i t) ((∏ i, f i 0) * ∑ i, u i) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i)
  simp only [smul_eq_mul] at h
  have he : (∑ i, (∏ j ∈ Finset.univ.erase i, f j 0) * (f i 0 * u i)) =
      (∏ i, f i 0) * ∑ i, u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [he] at h
  exact h

noncomputable def determinantProductValue {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ) : ℝ :=
  ∏ j, (A j).det ^ b j

noncomputable def determinantProductDirectional {d : ℕ} {r : Fin d → ℕ}
    (A H : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ) : ℝ :=
  determinantProductValue A b * ∑ j, b j * ((A j)⁻¹ * H j).trace

theorem determinant_product_directional {d : ℕ} {r : Fin d → ℕ}
    (A H : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (b : Fin d → ℝ) (hA : ∀ j, 0 < (A j).det) :
    HasDerivAt (fun t : ℝ => determinantProductValue (fun j => A j + t • H j) b)
      (determinantProductDirectional A H b) 0 := by
  simpa only [determinantProductValue, determinantProductDirectional, zero_smul, add_zero] using
    product_logarithmic_derivative
    (fun j t => (A j + t • H j).det ^ b j)
    (fun j => b j * ((A j)⁻¹ * H j).trace)
    (fun j => by simpa only [zero_smul, add_zero] using
      determinant_power_directional (A j) (H j) (hA j) (b j))

theorem determinant_product_hessian_directional {d : ℕ} {r : Fin d → ℕ}
    (A H J : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (b : Fin d → ℝ) (hA : ∀ j, 0 < (A j).det) :
    HasDerivAt
      (fun t : ℝ => determinantProductDirectional (fun j => A j + t • J j) H b)
      (determinantProductValue A b *
        ((∑ j, b j * ((A j)⁻¹ * H j).trace) *
          (∑ j, b j * ((A j)⁻¹ * J j).trace) -
            ∑ j, b j * ((A j)⁻¹ * J j * (A j)⁻¹ * H j).trace)) 0 := by
  have hD := determinant_product_directional A J b hA
  have hS : HasDerivAt
      (fun t : ℝ => ∑ j, b j * ((A j + t • J j)⁻¹ * H j).trace)
      (-(∑ j, b j * ((A j)⁻¹ * J j * (A j)⁻¹ * H j).trace)) 0 := by
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (inverse_trace_directional (A j) (H j) (J j) (hA j).ne').const_mul (b j))
    simpa only [mul_neg, Finset.sum_neg_distrib] using hs
  have h := hD.mul hS
  convert h using 1
  · funext t
    rfl
  · simp only [zero_smul, add_zero, determinantProductDirectional]
    ring

end ResearchMain.WishartBlocks
