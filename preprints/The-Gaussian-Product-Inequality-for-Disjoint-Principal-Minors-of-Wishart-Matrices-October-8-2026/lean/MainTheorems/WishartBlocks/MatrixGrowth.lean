import MainTheorems.WishartBlocks.BartlettLaw
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed

namespace ResearchMain.WishartBlocks

open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

theorem determinant_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {c : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A.det‖ ≤ Fintype.card (Equiv.Perm (Fin n)) * c ^ n := by
  rw [Matrix.det_apply]
  calc
    ‖∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤
        ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, ‖A (σ i) i‖ := by
      simp only [norm_units_zsmul, norm_prod]
    _ ≤ ∑ _ : Equiv.Perm (Fin n), c ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_le_prod₀ (s := Finset.univ)
          (fun i _ => norm_nonneg (A (σ i) i)) (fun i _ => hA (σ i) i)
    _ = Fintype.card (Equiv.Perm (Fin n)) * c ^ n := by simp

theorem matrix_product_entry_bound {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    {c d : ℝ} (hc : 0 ≤ c)
    (hA : ∀ i j, ‖A i j‖ ≤ c) (hB : ∀ i j, ‖B i j‖ ≤ d) (i j) :
    ‖(A * B) i j‖ ≤ n * c * d := by
  rw [Matrix.mul_apply]
  calc
    ‖∑ l : Fin n, A i l * B l j‖ ≤ ∑ l : Fin n, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, c * d := by
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul]
      exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) hc
    _ = n * c * d := by simp [mul_assoc]

theorem bartlettMatrix_entry_bound {p : ℕ} (x : Fin p × Fin p → ℝ) (i j : Fin p) :
    ‖bartlettMatrix x i j‖ ≤ 1 + ‖x‖ := by
  unfold bartlettMatrix
  split_ifs
  · rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hx : x (i, j) ≤ ‖x‖ := le_trans (le_abs_self _) (norm_le_pi_norm x (i, j))
    nlinarith [norm_nonneg x]
  · exact (norm_le_pi_norm x (i, j)).trans (by linarith)
  · simp only [norm_zero]
    positivity

noncomputable def bartlettEntryConstant {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (p : ℝ) ^ 3 * ‖CFC.sqrt S‖ ^ 2

theorem bartlettEntryConstant_nonneg {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ bartlettEntryConstant S := by unfold bartlettEntryConstant; positivity

theorem bartlettValue_entry_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin p × Fin p → ℝ) (i j : Fin p) :
    ‖bartlettValue S x i j‖ ≤ bartlettEntryConstant S * (1 + ‖x‖) ^ 2 := by
  let Q := CFC.sqrt S * bartlettMatrix x
  have hS : ∀ i j, ‖CFC.sqrt S i j‖ ≤ ‖CFC.sqrt S‖ := fun i j =>
    Matrix.norm_entry_le_entrywise_sup_norm (CFC.sqrt S)
  have hQ : ∀ i j, ‖Q i j‖ ≤ p * ‖CFC.sqrt S‖ * (1 + ‖x‖) :=
    matrix_product_entry_bound (CFC.sqrt S) (bartlettMatrix x) (norm_nonneg _)
      hS (bartlettMatrix_entry_bound x)
  have h := matrix_product_entry_bound Q Q.transpose (by positivity)
    hQ (fun i j => hQ j i) i j
  change ‖(Q * Q.transpose) i j‖ ≤ _
  calc
    ‖(Q * Q.transpose) i j‖ ≤ p *
        (p * ‖CFC.sqrt S‖ * (1 + ‖x‖)) * (p * ‖CFC.sqrt S‖ * (1 + ‖x‖)) := h
    _ = bartlettEntryConstant S * (1 + ‖x‖) ^ 2 := by unfold bartlettEntryConstant; ring

end ResearchMain.WishartBlocks
