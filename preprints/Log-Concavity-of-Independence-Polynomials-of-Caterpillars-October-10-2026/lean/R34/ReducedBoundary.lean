import R34.ReducedTensorCore

noncomputable section

namespace R34.ReducedCharge

open ChargeSites
open scoped BigOperators

theorem realUnitEntry_boundary (left right : Fin 3 → ℝ) (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, left i * realUnitEntry a b i j * right j) =
      left a * right b := by
  classical
  have he : ∀ i j, realUnitEntry a b i j =
      (if i=a then if j=b then (1 : ℝ) else 0 else 0) := by
    intro i j
    by_cases hi : i=a <;> by_cases hj : j=b <;> simp [realUnitEntry, hi, hj]
  simp_rw [he]
  simp [mul_ite, ite_mul]

theorem realTensor_boundary_sum {O : Type*} [Fintype O]
    (amplitude : O → ℝ) (first last : O → Fin 3) (left right : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      left i * (∑ o : O, amplitude o • realUnitEntry (first o) (last o)) i j * right j) =
      ∑ o : O, amplitude o * left (first o) * right (last o) := by
  classical
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o ho
  calc
    (∑ j : Fin 3, ∑ i : Fin 3,
      left i * (amplitude o * realUnitEntry (first o) (last o) i j) * right j) =
        amplitude o * ∑ i : Fin 3, ∑ j : Fin 3,
          left i * realUnitEntry (first o) (last o) i j * right j := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [realUnitEntry_boundary]; ring

theorem embed_siteLeftState (c : ChargedSite) (χ : Fin c.size → Bool)
    (v : ℝ × ℝ) (o : Bool) :
    Kernel.embed v (siteLeftState c χ o) = optionBoundary v o := by
  cases c <;> cases o <;>
    simp [siteLeftState, Kernel.embed, Transfer.colorState, optionBoundary]
  all_goals split_ifs <;> rfl

theorem embed_siteRightState (c : ChargedSite) (χ : Fin c.size → Bool)
    (v : ℝ × ℝ) (o : Bool) :
    Kernel.embed v (siteRightState c χ o) = optionBoundary v o := by
  cases c <;> cases o <;>
    simp [siteRightState, Kernel.embed, Transfer.colorState, optionBoundary]
  all_goals split_ifs <;> rfl

theorem embed_optionFirstState (ch : Chain) (χ : ChargeColorings ch.sizes)
    (v : ℝ × ℝ) (o : Options ch) :
    Kernel.embed v (optionFirstState ch χ o) = optionBoundary v (firstOption ch o) := by
  cases ch <;> exact embed_siteLeftState _ _ _ _

theorem embed_optionLastState (ch : Chain) (χ : ChargeColorings ch.sizes)
    (v : ℝ × ℝ) (o : Options ch) :
    Kernel.embed v (optionLastState ch χ o) = optionBoundary v (lastOption ch o) := by
  induction ch with
  | last c => exact embed_siteRightState _ _ _ _
  | cons c K tail ih => exact ih χ.2 o.2

theorem realValue_eq_affineModel_of_tensor_options (ch : Chain)
    (χ : ChargeColorings ch.sizes) (left right : ℝ × ℝ)
    (htensor : realTensor ch χ = ∑ o : Options ch,
      optionAmplitude ch χ o • realUnitEntry (optionFirstState ch χ o) (optionLastState ch χ o)) :
    realValue ch left right χ = affineModel ch left right (equalZ ch χ) := by
  unfold realValue
  rw [htensor, realTensor_boundary_sum]
  unfold affineModel SignExpansion.affineSum
  apply Finset.sum_congr rfl
  intro o ho
  rw [embed_optionFirstState, embed_optionLastState]
  unfold optionAmplitude optionCoefficient affineEdgeProduct
  ring

theorem liftRealMatrix_mul (A B : RealMat) :
    liftRealMatrix (A*B) = liftRealMatrix A * liftRealMatrix B := by
  apply Matrix.ext
  intro i j
  simp [liftRealMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem liftRealMatrix_sum {O : Type*} [Fintype O] (A : O → RealMat) :
    liftRealMatrix (∑ o : O, A o) = ∑ o : O, liftRealMatrix (A o) := by
  apply Matrix.ext
  intro i j
  simp [liftRealMatrix, Matrix.sum_apply, map_sum]

theorem liftRealMatrix_boundary (A : RealMat) (left right : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      MvPolynomial.C (left i) * liftRealMatrix A i j * MvPolynomial.C (right j)) =
      MvPolynomial.C (∑ i : Fin 3, ∑ j : Fin 3, left i * A i j * right j) := by
  simp [liftRealMatrix, map_sum, map_mul]

end R34.ReducedCharge




