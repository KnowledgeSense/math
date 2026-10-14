import EdgeColoringMixing.WeightedInjections

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- The probability that a color is used. -/
noncomputable def colorMean (μ : FiniteLaw (Injection d q)) (c : Fin q) : ℝ :=
  ∑ i, mean μ i c

theorem sum_cells_eq_used (σ : Injection d q) (c : Fin q) :
    (∑ i, cell i c σ) = if c ∈ Set.range σ then 1 else 0 := by
  classical
  by_cases hc : c ∈ Set.range σ
  · obtain ⟨i, rfl⟩ := hc
    simp [cell, σ.injective.eq_iff]
  · have hne (i : Fin d) : σ i ≠ c := fun h => hc ⟨i, h⟩
    simp [cell, hc, hne]

theorem colorMean_eq_expectation (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    colorMean μ c = μ.expectation (fun σ => if c ∈ Set.range σ then 1 else 0) := by
  classical
  unfold colorMean mean
  rw [← FiniteLaw.expectation_sum]
  simp_rw [sum_cells_eq_used]

theorem colorMean_nonneg (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    0 ≤ colorMean μ c := Finset.sum_nonneg (fun i _ => mean_nonneg μ i c)

theorem colorMean_le_one (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    colorMean μ c ≤ 1 := by
  rw [colorMean_eq_expectation]
  apply (μ.expectation_mono (g := fun _ => 1) ?_).trans_eq (μ.expectation_const 1)
  intro σ
  split_ifs <;> norm_num

/-- The covariance's exact same-color blocks, with cross-color entries zeroed. -/
noncomputable def columnBlock (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  fun x y => if x.2 = y.2 then
    (if x.1 = y.1 then mean μ x.1 x.2 else 0) - mean μ x.1 x.2 * mean μ y.1 y.2
    else 0

/-- The actual column-summation matrix. -/
def columnSum : Matrix (Fin q) (Fin d × Fin q) ℝ :=
  fun c x => if x.2 = c then 1 else 0

theorem columnBlock_eq_covariance (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) :
    columnBlock μ x y = if x.2 = y.2 then covariance μ x y else 0 := by
  obtain ⟨i,c⟩ := x
  obtain ⟨j,b⟩ := y
  by_cases hcb : c = b
  · subst b
    by_cases hij : i = j
    · subst j
      simp [columnBlock, covariance_diagonal, pow_two]
    · simp [columnBlock, covariance_same_color μ hij, hij]
  · simp [columnBlock, hcb]

/-- The retained color blocks form a positive semidefinite matrix. -/
theorem columnBlock_posSemidef (μ : FiniteLaw (Injection d q)) :
    (columnBlock μ).PosSemidef := by
  let P : Fin q → Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
    fun c => Matrix.diagonal (fun x => if x.2 = c then 1 else 0)
  have hrepr : columnBlock μ = ∑ c, P c * covariance μ * P c := by
    ext x y
    rw [columnBlock_eq_covariance]
    simp only [Matrix.sum_apply, P, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one]
    by_cases hxy : x.2 = y.2
    · simp [hxy]
    · simp [hxy]
  rw [hrepr]
  apply Matrix.posSemidef_sum
  intro c _
  simpa [P] using (covariance_posSemidef μ).conjTranspose_mul_mul_same (P c)

/-- Exact variance matching for the arcsine metric, equation (2.1) of the release. -/
theorem column_variance_identity (μ : FiniteLaw (Injection d q)) :
    columnSum * columnBlock μ * columnSumᵀ =
      Matrix.diagonal (fun c => colorMean μ c * (1 - colorMean μ c)) := by
  ext c b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columnSum, columnBlock,
    Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hcb : c = b
  · subst b
    simp only [ite_true, Matrix.diagonal_apply_eq, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum,
      ← Finset.sum_mul, colorMean]
    ring
  · simp [hcb, Ne.symm hcb]

end EdgeColoringMixing.WeightedInjection
