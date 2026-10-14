import EdgeColoringMixing.TwoRowBase
import EdgeColoringMixing.CovarianceRecursion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix
variable {d q : ℕ}

/-- Assemble the same-color blocks on the full cell space. -/
noncomputable def colorBlocks (A : Fin q → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  fun x y => if x.2 = y.2 then A x.2 x.1 y.1 else 0

theorem colorBlocks_posSemidef (A : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ c, (A c).PosSemidef) : (colorBlocks A).PosSemidef := by
  classical
  let D (c : Fin q) : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
    Matrix.diagonal (fun x => if x.2 = c then 1 else 0)
  have hp (c : Fin q) := ((hA c).submatrix Prod.fst).mul_mul_conjTranspose_same (D c)
  have hs := Matrix.posSemidef_sum (s := univ) (fun c _ => hp c)
  convert hs using 1
  ext x y
  simp only [Matrix.sum_apply, D, Matrix.diagonal_conjTranspose, star_trivial,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply]
  simp [colorBlocks, mul_ite, ite_mul]
  split_ifs with h
  · rw [h]
  · rfl

noncomputable def retainedPosterior (μ : FiniteLaw (Injection d q))
    (x : Fin d × Fin q) : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  fun y z => if y.1 ≠ z.1 ∧ y.2 = z.2 then
    -posteriorMean μ x y * posteriorMean μ x z else 0

theorem retainedNegative_blocks (μ : FiniteLaw (Injection d q)) :
    retainedNegative μ = colorBlocks (negativeBlock μ) := by
  ext x y
  simp only [retainedNegative, colorBlocks, negativeBlock]
  by_cases hc : x.2 = y.2
  · by_cases hr : x.1 = y.1 <;> simp [hc, hr]
  · simp [hc]

theorem retainedPosterior_blocks (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q) :
    retainedPosterior μ x = colorBlocks (fun c => posteriorNegativeBlock μ x c) := by
  ext ⟨i,c⟩ ⟨j,b⟩
  change (if i ≠ j ∧ c = b then -posteriorMean μ x (i,c) * posteriorMean μ x (j,b) else 0) = _
  by_cases hc : c = b
  · subst b
    by_cases hr : i = j <;> simp [colorBlocks, posteriorNegativeBlock, hr]
  · simp [colorBlocks, hc]

theorem colorBlocks_mul (A B : Fin q → Matrix (Fin d) (Fin d) ℝ) :
    colorBlocks A * colorBlocks B = colorBlocks (fun c => A c * B c) := by
  ext ⟨i,c⟩ ⟨j,b⟩
  simp only [Matrix.mul_apply, colorBlocks, Fintype.sum_prod_type]
  by_cases hc : c = b
  · subst b
    simp
  · simp [hc, mul_ite, ite_mul]

theorem colorBlocks_diagonal (p : Fin d × Fin q → ℝ) :
    Matrix.diagonal p = colorBlocks (fun c => Matrix.diagonal (fun i => p (i,c))) := by
  ext ⟨i,c⟩ ⟨j,b⟩
  by_cases hc : c = b <;> by_cases hr : i = j <;>
    simp [colorBlocks, hc, hr]

/-- The global negative-block error on the full cell space. -/
noncomputable def retainedRecursionError (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  (∑ x ∈ active μ, mean μ x.1 x.2 • retainedPosterior μ x) -
    ((d : ℝ) - 2) • retainedNegative μ +
    retainedNegative μ * Matrix.diagonal (fun x => 1 / mean μ x.1 x.2) * retainedNegative μ

theorem retainedRecursionError_blocks (μ : FiniteLaw (Injection d q)) :
    retainedRecursionError μ = colorBlocks (recursionError μ) := by
  unfold retainedRecursionError
  rw [retainedNegative_blocks, colorBlocks_diagonal, colorBlocks_mul, colorBlocks_mul]
  simp_rw [retainedPosterior_blocks]
  ext ⟨i,c⟩ ⟨j,b⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, colorBlocks, recursionError]
  by_cases hc : c = b
  · subst b
    simp only [ite_true, Matrix.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  · simp [hc]

/-- Corollary 4.7 on every cell, including zero-marginal cells. -/
theorem retainedRecursionError_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
    (((1 + 4 * V) * ((d : ℝ) - 1) / (s + 1)^2) •
      Matrix.diagonal (fun x : Fin d × Fin q => mean μ x.1 x.2) -
        retainedRecursionError μ).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let C := (1 + 4 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
    ((d : ℝ) - 1) / (s + 1)^2
  have h := colorBlocks_posSemidef
    (fun c => C • Matrix.diagonal (fun i => mean μ i c) - recursionError μ c)
    (fun c => recursionError_bound W hW c Δ hd)
  convert h using 1
  rw [retainedRecursionError_blocks, colorBlocks_diagonal]
  ext ⟨i,c⟩ ⟨j,b⟩
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, colorBlocks]
  by_cases hc : c = b <;> simp [hc, C, μ]

end EdgeColoringMixing.WeightedInjection
