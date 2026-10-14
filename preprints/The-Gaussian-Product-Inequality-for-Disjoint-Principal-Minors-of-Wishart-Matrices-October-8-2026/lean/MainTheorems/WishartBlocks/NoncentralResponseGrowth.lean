import MainTheorems.WishartBlocks.NoncentralExpectationContinuity

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory Filter
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

theorem matrix_rectangular_product_norm {k m n : ℕ}
    (A : Matrix (Fin k) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A * B‖ ≤ (m : ℝ) * ‖A‖ * ‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  calc
    ‖(A * B) i j‖ ≤ ∑ a : Fin m, ‖A i a * B a j‖ := by
      simpa only [Matrix.mul_apply] using
        norm_sum_le Finset.univ (fun a : Fin m => A i a * B a j)
    _ ≤ ∑ _ : Fin m, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem positive_matrix_sqrt_norm_bound {r : ℕ} {W : Matrix (Fin r) (Fin r) ℝ}
    (hW : W.PosSemidef) : ‖CFC.sqrt W‖ ≤ 1 + ‖W‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  have he : ∑ a : Fin r, (CFC.sqrt W i a) ^ 2 = W i i := by
    have h := congrArg (fun A : Matrix (Fin r) (Fin r) ℝ => A i i) (sqrt_column_gramSum hW)
    simpa only [gramSum, Matrix.sum_apply, Matrix.vecMulVec_apply, pow_two] using h
  have hs : (CFC.sqrt W i j) ^ 2 ≤ W i i := by
    rw [← he]
    exact Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ j)
  have hnorm : W i i ≤ ‖W‖ := (le_abs_self _).trans (Matrix.norm_entry_le_entrywise_sup_norm W)
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (CFC.sqrt W i j), abs_nonneg (CFC.sqrt W i j), norm_nonneg W]

noncomputable def covarianceMeanBound {p r : ℕ} (K : Matrix (Fin r) (Fin p) ℝ) : ℝ :=
  ContinuousLinearMap.opNorm (E := Fin r → Fin p → ℝ) (meanRowsCLM p r) * (r : ℝ) * ‖K‖

theorem covarianceMeanBound_nonneg {p r : ℕ} (K : Matrix (Fin r) (Fin p) ℝ) :
    0 ≤ covarianceMeanBound K := by
  unfold covarianceMeanBound
  exact mul_nonneg (mul_nonneg
    (ContinuousLinearMap.opNorm_nonneg (E := Fin r → Fin p → ℝ) (meanRowsCLM p r))
    (Nat.cast_nonneg r)) (norm_nonneg K)

theorem covarianceMeanRows_norm_bound {p r : ℕ} (K : Matrix (Fin r) (Fin p) ℝ)
    {W : Matrix (Fin r) (Fin r) ℝ} (hW : W.PosSemidef) :
    ‖covarianceMeanRows W K‖ ≤ covarianceMeanBound K * (1 + ‖W‖) := by
  change ‖meanRowsCLM p r ((CFC.sqrt W).transpose * K)‖ ≤ _
  have hN := ContinuousLinearMap.opNorm_nonneg (E := Fin r → Fin p → ℝ) (meanRowsCLM p r)
  apply (ContinuousLinearMap.le_opNorm (E := Fin r → Fin p → ℝ) (meanRowsCLM p r) _).trans
  calc
    _ ≤ ContinuousLinearMap.opNorm (E := Fin r → Fin p → ℝ) (meanRowsCLM p r) *
        ((r : ℝ) * ‖CFC.sqrt W‖ * ‖K‖) := by
      apply mul_le_mul_of_nonneg_left _ hN
      change ‖(CFC.sqrt W).transpose * K‖ ≤ (r : ℝ) * ‖CFC.sqrt W‖ * ‖K‖
      have hprod := matrix_rectangular_product_norm (CFC.sqrt W).transpose K
      rwa [Matrix.norm_transpose] at hprod
    _ ≤ ContinuousLinearMap.opNorm (E := Fin r → Fin p → ℝ) (meanRowsCLM p r) *
        ((r : ℝ) * (1 + ‖W‖) * ‖K‖) := by
      apply mul_le_mul_of_nonneg_left _ hN
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg K)
      exact mul_le_mul_of_nonneg_left (positive_matrix_sqrt_norm_bound hW) (Nat.cast_nonneg r)
    _ = _ := by unfold covarianceMeanBound; ring

noncomputable def covarianceNoncentralBound {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) : ℝ :=
  (r : ℝ) * ((p : ℝ) * ‖CFC.sqrt S‖ + covarianceMeanBound K) ^ 2

theorem covarianceNoncentralBound_nonneg {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) : 0 ≤ covarianceNoncentralBound S K := by
  unfold covarianceNoncentralBound
  positivity

theorem covarianceNoncentralGrowth_bound {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) {W : Matrix (Fin r) (Fin r) ℝ} (hW : W.PosSemidef) :
    noncentralGrowthConstant S (covarianceMeanRows W K) ≤
      covarianceNoncentralBound S K * (1 + ‖W‖) ^ (2 : ℕ) := by
  have hM := covarianceMeanRows_norm_bound K hW
  have hD := covarianceMeanBound_nonneg K
  have ha : 0 ≤ (p : ℝ) * ‖CFC.sqrt S‖ := by positivity
  have hsum : (p : ℝ) * ‖CFC.sqrt S‖ + ‖covarianceMeanRows W K‖ ≤
      ((p : ℝ) * ‖CFC.sqrt S‖ + covarianceMeanBound K) * (1 + ‖W‖) := by
    nlinarith [norm_nonneg W]
  unfold noncentralGrowthConstant covarianceNoncentralBound
  calc
    _ ≤ (r : ℝ) * ((((p : ℝ) * ‖CFC.sqrt S‖ + covarianceMeanBound K) * (1 + ‖W‖)) ^ 2) := by
      gcongr
    _ = _ := by ring

theorem covarianceNoncentralValue_bound {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) {W : Matrix (Fin r) (Fin r) ℝ} (hW : W.PosSemidef)
    (x : NoncentralInput p r) :
    1 + ‖noncentralWishartValue S (covarianceMeanRows W K) x‖ ≤
      (1 + covarianceNoncentralBound S K) * (1 + ‖W‖) ^ (2 : ℕ) * (1 + ‖x‖) ^ (2 : ℕ) := by
  have hC := covarianceNoncentralGrowth_bound S K hW
  have h2 : 1 ≤ (1 + ‖W‖) ^ (2 : ℕ) := by nlinarith [norm_nonneg W]
  apply (noncentralValue_polynomial_bound S (covarianceMeanRows W K) x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

theorem covarianceMean_expectation_growth {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) {g : Matrix (Fin p) (Fin p) ℝ → ℝ} (hg : Measurable g)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hgB : ∀ B, ‖g B‖ ≤ C * (1 + ‖B‖) ^ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ W : Matrix (Fin r) (Fin r) ℝ, W.PosSemidef →
      ‖noncentralMeanExpectation α S g (covarianceMeanRows W K)‖ ≤ D * (1 + ‖W‖) ^ (2 * β) := by
  let μ := noncentralInputLaw (r := r) α S
  let A := C * (1 + covarianceNoncentralBound S K) ^ β
  let D := A * ∫ x : NoncentralInput p r, (1 + ‖x‖) ^ (2 * β) ∂μ
  have hD₀ := covarianceNoncentralBound_nonneg S K
  have hA : 0 ≤ A := mul_nonneg hC (Real.rpow_nonneg (by
    have h := covarianceNoncentralBound_nonneg S K
    positivity) _)
  have hi := noncentralInput_real_power_integrable hα S (2 * β)
  refine ⟨D, mul_nonneg hA (integral_nonneg fun x => Real.rpow_nonneg (by positivity) _), ?_⟩
  intro W hW
  have hgI := noncentralWishart_real_growth_integrable hα S (covarianceMeanRows W K) hg hC hgB
  have hI : Integrable (fun x => g (noncentralWishartValue S (covarianceMeanRows W K) x)) μ :=
    (integrable_map_measure hg.aestronglyMeasurable
      (measurable_noncentralWishartValue S (covarianceMeanRows W K)).aemeasurable).mp hgI
  rw [noncentralMeanExpectation_input α S hg]
  apply (norm_integral_le_integral_norm _).trans
  have hbound : ∀ x : NoncentralInput p r,
      ‖g (noncentralWishartValue S (covarianceMeanRows W K) x)‖ ≤
        (A * (1 + ‖W‖) ^ (2 * β)) * (1 + ‖x‖) ^ (2 * β) := by
    intro x
    calc
      _ ≤ C * (1 + ‖noncentralWishartValue S (covarianceMeanRows W K) x‖) ^ β := hgB _
      _ ≤ C * ((1 + covarianceNoncentralBound S K) * (1 + ‖W‖) ^ 2 * (1 + ‖x‖) ^ 2) ^ β :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
          (covarianceNoncentralValue_bound S K hW x) hβ) hC
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by
          have h := covarianceNoncentralBound_nonneg S K
          positivity) (by positivity),
          ← Real.rpow_natCast_mul (by positivity) 2, ← Real.rpow_natCast_mul (by positivity) 2]
        dsimp [A]
        ring
  calc
    _ ≤ ∫ x : NoncentralInput p r,
        (A * (1 + ‖W‖) ^ (2 * β)) * (1 + ‖x‖) ^ (2 * β) ∂μ :=
      integral_mono hI.norm (hi.const_mul _) hbound
    _ = D * (1 + ‖W‖) ^ (2 * β) := by rw [integral_const_mul]; dsimp [D]; ring

namespace BlockPartition

theorem noncentralProductResponse_growth {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ β : ℝ, ∀ W : Matrix (Fin r) (Fin r) ℝ, W.PosDef →
      ‖P.noncentralProductResponse α S K ν W‖ ≤ D * (1 + ‖W‖) ^ β := by
  obtain ⟨D, hD, hB⟩ := covarianceMean_expectation_growth hα S K (P.measurable_determinantProduct ν)
    (C := ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) : ℝ) ^ ν j)
    (β := P.productGrowthExponent ν) (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)) (fun B => by
      simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero,
        norm_zero, add_zero, one_pow, mul_one, productGrowthExponent] using
          P.shiftedDeterminantProduct_growth (fun _ => 0) ν hν B)
  exact ⟨D, hD, 2 * P.productGrowthExponent ν, fun W hW => hB W hW.posSemidef⟩

end BlockPartition
end ResearchMain.WishartBlocks
