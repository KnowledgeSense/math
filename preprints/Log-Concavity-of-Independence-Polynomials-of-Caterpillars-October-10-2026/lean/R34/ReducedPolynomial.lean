import R34.ReducedTensorCore

open scoped BigOperators Classical

namespace R34.ReducedCharge

noncomputable section

open MvPolynomial ChargeSites

theorem liftRealMatrix_mul (A B : RealMat) :
    liftRealMatrix (A * B) = liftRealMatrix A * liftRealMatrix B := by
  funext i j
  simp [liftRealMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem weighted_site_colored_sum (c : ChargedSite) :
    c.matrix = ∑ χ : Fin c.size → Bool,
      ChargeSites.chargeWeight χ • liftRealMatrix (weightedSiteTensor c χ) := by
  rw [ChargedSite.matrix_colored_sum]
  simp_rw [colorWeight_eq_extra, weightedSiteTensor, lift_smul, smul_smul]

/-- The polynomial transfer product is the weighted sum of its real colored tensors. -/
theorem Chain.matrix_colored_sum (ch : Chain) :
    ch.matrix = ∑ χ : ChargeColorings ch.sizes,
      R34.chargeWeight ch.sizes χ • liftRealMatrix (realTensor ch χ) := by
  induction ch with
  | last c =>
    rw [Chain.matrix, weighted_site_colored_sum]
    rw [chargeColorings_sum_cons]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [chargeColorings_sum_nil]
    simp [R34.chargeWeight, ChargeSites.chargeWeight, realTensor]
  | cons c K tail ih =>
    rw [Chain.matrix, weighted_site_colored_sum, ih]
    rw [chargeColorings_sum_cons]
    rw [Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [R34.chargeWeight, ChargeSites.chargeWeight, realTensor, liftRealMatrix_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm]

/-- Free boundary evaluation commutes with the finite coloring sum. -/
theorem matrixValue_eq_charge_sum (ch : Chain) (left right : ℝ × ℝ) :
    matrixValue ch left right = ∑ χ : ChargeColorings ch.sizes,
      R34.chargeWeight ch.sizes χ * C (realValue ch left right χ) := by
  unfold matrixValue
  rw [Chain.matrix_colored_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i : Fin 3, ∑ χ : ChargeColorings ch.sizes, ∑ j : Fin 3,
        C (Kernel.embed left i) *
          (R34.chargeWeight ch.sizes χ * C (realTensor ch χ i j)) *
            C (Kernel.embed right j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ χ : ChargeColorings ch.sizes, ∑ i : Fin 3, ∑ j : Fin 3,
        C (Kernel.embed left i) *
          (R34.chargeWeight ch.sizes χ * C (realTensor ch χ i j)) *
            C (Kernel.embed right j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [realValue, map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

end

end R34.ReducedCharge
