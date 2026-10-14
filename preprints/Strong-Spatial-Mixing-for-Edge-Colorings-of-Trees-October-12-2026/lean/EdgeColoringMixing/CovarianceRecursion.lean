import EdgeColoringMixing.SquaredCovariance

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- The occupancy of all other rows in a specified column. -/
theorem colorMean_sub_mean_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    colorMean μ c - mean μ i c ≤ ((d : ℝ) - 1) / (s + 1) := by
  classical
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hd : 1 ≤ d := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt)
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hsum := Finset.sum_erase_add univ (fun j => mean μ j c) (mem_univ i)
  have hle : (∑ j ∈ univ.erase i, mean μ j c) ≤ ∑ _j ∈ univ.erase i, (1 : ℝ) / (s + 1) := by
    apply Finset.sum_le_sum
    intro j _
    exact (marginal_le W hW j c).trans
      (div_le_div_of_nonneg_right (hW.le_one j c) ht.le)
  have hr : (∑ _j ∈ univ.erase i, (1 : ℝ) / (s + 1)) = ((d : ℝ) - 1) / (s + 1) := by
    simp only [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin, Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hr] at hle
  change colorMean μ c - mean μ i c ≤ _
  unfold colorMean
  linarith

/-- The exact recursive negative-block error, multiplied by the number of remaining rows. -/
noncomputable def recursionError (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
    (∑ x ∈ active μ, mean μ x.1 x.2 * posteriorNegativeBlock μ x c i j) -
      ((d : ℝ) - 2) * negativeBlock μ c i j +
      (∑ l, negativeBlock μ c i l * negativeBlock μ c l j / mean μ l c)

theorem recursionError_eq (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    recursionError μ c = Matrix.diagonal (fun i =>
      (mean μ i c)^2 * (colorMean μ c - mean μ i c) + crossRowGram μ c i i) -
        crossRowGram μ c := by
  ext i j
  rw [recursionError, recursive_gram_cancellation]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs <;> ring

/-- The diagonal remainder has precisely the coefficient needed in matrix trickle-down. -/
theorem recursion_diagonal_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
    (mean μ i c)^2 * (colorMean μ c - mean μ i c) + crossRowGram μ c i i ≤
      (1 + 4 * V) * ((d : ℝ) - 1) / (s + 1)^2 * mean μ i c := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hp := mean_nonneg μ i c
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt)
  have hpmax : mean μ i c ≤ 1 / (s + 1) :=
    (marginal_le W hW i c).trans
      (div_le_div_of_nonneg_right (hW.le_one i c) ht.le)
  have h₁ := mul_le_mul_of_nonneg_left (colorMean_sub_mean_le W hW i c) (sq_nonneg (mean μ i c))
  have h₂ := mul_le_mul_of_nonneg_left hpmax
    (show 0 ≤ mean μ i c * ((d : ℝ) - 1) / (s + 1) by positivity)
  have h₃ : (mean μ i c)^2 * (colorMean μ c - mean μ i c) ≤
      ((d : ℝ) - 1) / (s + 1)^2 * mean μ i c := by
    apply h₁.trans
    convert h₂ using 1 <;> field_simp
  have hG := crossRowGram_diagonal_bound_uniform W hW i c Δ hd
  change crossRowGram μ c i i ≤ 4 * V * ((d : ℝ) - 1) * mean μ i c / (s + 1)^2 at hG
  change (mean μ i c)^2 * (colorMean μ c - mean μ i c) + crossRowGram μ c i i ≤
    (1 + 4 * V) * ((d : ℝ) - 1) / (s + 1)^2 * mean μ i c
  exact (add_le_add h₃ hG).trans_eq (by ring)

/-- Corollary 4.7 in unscaled block form, with an actual positive semidefinite matrix conclusion. -/
theorem recursionError_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
    (((1 + 4 * V) * ((d : ℝ) - 1) / (s + 1)^2) •
        Matrix.diagonal (fun i => mean μ i c) - recursionError μ c).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
  let C := (1 + 4 * V) * ((d : ℝ) - 1) / (s + 1)^2
  let D := fun i => C * mean μ i c -
    ((mean μ i c)^2 * (colorMean μ c - mean μ i c) + crossRowGram μ c i i)
  have hD : (Matrix.diagonal D).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact sub_nonneg.mpr (recursion_diagonal_bound W hW i c Δ hd)
  have h := hD.add (crossRowGram_posSemidef μ c)
  convert h using 1
  ext i j
  rw [recursionError_eq]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, D]
  split_ifs <;> ring

end EdgeColoringMixing.WeightedInjection
