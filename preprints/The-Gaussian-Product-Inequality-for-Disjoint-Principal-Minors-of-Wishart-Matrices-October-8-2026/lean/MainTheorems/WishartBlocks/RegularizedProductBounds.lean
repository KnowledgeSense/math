import MainTheorems.WishartBlocks.RegularizedMatrices
import MainTheorems.WishartBlocks.DeterminantOperatorContraction
import MainTheorems.WishartBlocks.ShiftedDeterminantMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace BlockPartition

noncomputable def regularizedBlocks {p d : ℕ} (P : BlockPartition p d) (ε : ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
    Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ := P.block W j + ε • 1

noncomputable def regularizedFirstConstant {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∑ j, |ν j| * ((P.size j : ℝ) ^ 2 * ((P.size j : ℝ) / ε))

noncomputable def regularizedSecondConstant {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∑ j, |ν j| * ((P.size j : ℝ) ^ 4 * ((P.size j : ℝ) / ε) ^ 2)

theorem block_norm_le {p d : ℕ} (P : BlockPartition p d)
    (H : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) : ‖P.block H j‖ ≤ ‖H‖ := by
  exact (Matrix.norm_le_iff (norm_nonneg H)).mpr fun i k =>
    Matrix.norm_entry_le_entrywise_sup_norm H

theorem regularizedBlocks_posDef {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (j : Fin d) : (P.regularizedBlocks ε W j).PosDef :=
  positiveSemidefinite_add_identity_posDef (hW.submatrix (P.inclusion j)) hε

theorem regularizedFirstConstant_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) : 0 ≤ P.regularizedFirstConstant ν ε := by
  unfold regularizedFirstConstant
  exact Finset.sum_nonneg fun j _ => by positivity

theorem regularizedSecondConstant_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) : 0 ≤ P.regularizedSecondConstant ν ε := by
  unfold regularizedSecondConstant
  exact Finset.sum_nonneg fun j _ => by positivity

theorem regularized_logarithmic_direction_bound {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H : Matrix (Fin p) (Fin p) ℝ) :
    ‖∑ j, ν j * ((P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace‖ ≤
      P.regularizedFirstConstant ν ε * ‖H‖ := by
  calc
    _ ≤ ∑ j, ‖ν j * ((P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, |ν j| * (((P.size j : ℝ) ^ 2 * ((P.size j : ℝ) / ε)) * ‖H‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (regularized_trace_direction_bound (hW.submatrix (P.inclusion j)) hε
        (P.block H j)).trans
      exact mul_le_mul_of_nonneg_left (P.block_norm_le H j) (by positivity)
    _ = _ := by simp only [regularizedFirstConstant, Finset.sum_mul, mul_assoc]

theorem regularized_logarithmic_hessian_bound {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H J : Matrix (Fin p) (Fin p) ℝ) :
    ‖∑ j, ν j * ((P.regularizedBlocks ε W j)⁻¹ * P.block J j *
        (P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace‖ ≤
      P.regularizedSecondConstant ν ε * ‖H‖ * ‖J‖ := by
  calc
    _ ≤ ∑ j, ‖ν j * ((P.regularizedBlocks ε W j)⁻¹ * P.block J j *
        (P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace‖ := norm_sum_le _ _
    _ ≤ ∑ j, |ν j| * (((P.size j : ℝ) ^ 4 * ((P.size j : ℝ) / ε) ^ 2) * ‖H‖ * ‖J‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (regularized_trace_hessian_bound (hW.submatrix (P.inclusion j)) hε
        (P.block H j) (P.block J j)).trans
      gcongr
      · exact P.block_norm_le H j
      · exact P.block_norm_le J j
    _ = _ := by simp only [regularizedSecondConstant, Finset.sum_mul, mul_assoc]

noncomputable def regularizedProductDirectional {p d : ℕ} (P : BlockPartition p d)
    (ε : ℝ) (ν : Fin d → ℝ) (H W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  determinantProductDirectional (P.regularizedBlocks ε W) (fun j => P.block H j) ν

noncomputable def regularizedProductHessian {p d : ℕ} (P : BlockPartition p d)
    (ε : ℝ) (ν : Fin d → ℝ) (H J W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  determinantProductHessianValue (P.regularizedBlocks ε W)
    (fun j => P.block H j) (fun j => P.block J j) ν

theorem regularizedProductDirectional_bound {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H : Matrix (Fin p) (Fin p) ℝ) :
    ‖P.regularizedProductDirectional ε ν H W‖ ≤
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        P.regularizedFirstConstant ν ε * ‖H‖ := by
  unfold regularizedProductDirectional determinantProductDirectional
  rw [norm_mul]
  calc
    _ ≤ ‖determinantProductValue (P.regularizedBlocks ε W) ν‖ *
        (P.regularizedFirstConstant ν ε * ‖H‖) :=
      mul_le_mul_of_nonneg_left (P.regularized_logarithmic_direction_bound hW hε ν H)
        (norm_nonneg _)
    _ = _ := by
      change ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ * _ = _
      ring

theorem regularizedProductHessian_bound {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H J : Matrix (Fin p) (Fin p) ℝ) :
    ‖P.regularizedProductHessian ε ν H J W‖ ≤
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        (P.regularizedFirstConstant ν ε ^ 2 + P.regularizedSecondConstant ν ε) *
          ‖H‖ * ‖J‖ := by
  unfold regularizedProductHessian determinantProductHessianValue
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)).trans
  rw [norm_mul]
  have h1 := P.regularized_logarithmic_direction_bound hW hε ν H
  have h2 := P.regularized_logarithmic_direction_bound hW hε ν J
  have h3 := P.regularized_logarithmic_hessian_bound hW hε ν H J
  have hc := P.regularizedFirstConstant_nonneg ν hε
  calc
    _ ≤ ‖determinantProductValue (P.regularizedBlocks ε W) ν‖ *
        ((P.regularizedFirstConstant ν ε * ‖H‖) *
          (P.regularizedFirstConstant ν ε * ‖J‖) +
            P.regularizedSecondConstant ν ε * ‖H‖ * ‖J‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hc (norm_nonneg H))) h3
    _ = _ := by
      change ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ * _ = _
      ring

theorem measurable_regularizedProductDirectional {p d : ℕ} (P : BlockPartition p d)
    (ε : ℝ) (ν : Fin d → ℝ) (H : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (P.regularizedProductDirectional ε ν H) := by
  unfold regularizedProductDirectional determinantProductDirectional determinantProductValue
  have hi (j : Fin d) : Measurable (fun W => (P.regularizedBlocks ε W j)⁻¹) :=
    measurable_matrix_inverse.comp (by unfold regularizedBlocks block; fun_prop)
  have ha (j : Fin d) : Measurable (fun W => P.regularizedBlocks ε W j) := by
    unfold regularizedBlocks block
    fun_prop
  fun_prop

theorem measurable_regularizedProductHessian {p d : ℕ} (P : BlockPartition p d)
    (ε : ℝ) (ν : Fin d → ℝ) (H J : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (P.regularizedProductHessian ε ν H J) := by
  have hi (j : Fin d) : Measurable (fun W => (P.regularizedBlocks ε W j)⁻¹) :=
    measurable_matrix_inverse.comp (by unfold regularizedBlocks block; fun_prop)
  have ha (j : Fin d) : Measurable (fun W => P.regularizedBlocks ε W j) := by
    unfold regularizedBlocks block
    fun_prop
  have hp : Measurable (fun W => determinantProductValue (P.regularizedBlocks ε W) ν) := by
    unfold determinantProductValue
    exact Finset.measurable_fun_prod _ fun j _ => by fun_prop
  have ht (L : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
      Measurable (fun W => ((P.regularizedBlocks ε W j)⁻¹ * P.block L j).trace) := by
    unfold Matrix.trace
    fun_prop
  have ht₂ (j : Fin d) : Measurable (fun W =>
      ((P.regularizedBlocks ε W j)⁻¹ * P.block J j *
        (P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace) := by
    let : BorelSpace (Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) :=
      inferInstanceAs (BorelSpace (Fin (P.size j) → Fin (P.size j) → ℝ))
    let : SecondCountableTopology (Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin (P.size j) → Fin (P.size j) → ℝ))
    have hm : Measurable (fun W =>
        (P.regularizedBlocks ε W j)⁻¹ * P.block J j *
          (P.regularizedBlocks ε W j)⁻¹ * P.block H j) :=
      (((hi j).mul_const (P.block J j)).fun_mul (hi j)).mul_const (P.block H j)
    change Measurable (fun W => ∑ i,
      ((P.regularizedBlocks ε W j)⁻¹ * P.block J j *
        (P.regularizedBlocks ε W j)⁻¹ * P.block H j) i i)
    exact Finset.measurable_fun_sum _ fun i _ => hm.eval_matrix (i := i) (j := i)
  have hs (L : Matrix (Fin p) (Fin p) ℝ) : Measurable (fun W =>
      ∑ j, ν j * ((P.regularizedBlocks ε W j)⁻¹ * P.block L j).trace) :=
    Finset.measurable_fun_sum _ fun j _ => (ht L j).const_mul (ν j)
  have hs₂ : Measurable (fun W => ∑ j, ν j *
      ((P.regularizedBlocks ε W j)⁻¹ * P.block J j *
        (P.regularizedBlocks ε W j)⁻¹ * P.block H j).trace) :=
    Finset.measurable_fun_sum _ fun j _ => (ht₂ j).const_mul (ν j)
  exact hp.fun_mul (((hs H).fun_mul (hs J)).sub hs₂)

theorem noncentral_regularizedProductDirectional_integrable {p r d : ℕ}
    (P : BlockPartition p d) {α : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p))
    {ε : ℝ} (hε : 0 < ε) (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j)
    (H : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (P.regularizedProductDirectional ε ν H) (noncentralWishartLaw α S M) := by
  have hi := (P.noncentral_shiftedDeterminantProduct_integrable hα S M
    (fun _ => ε • 1) ν hν).norm.const_mul (P.regularizedFirstConstant ν ε * ‖H‖)
  apply hi.mono' (P.measurable_regularizedProductDirectional ε ν H).aestronglyMeasurable
  filter_upwards [noncentralWishart_positiveSemidefinite α S M] with W hW
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    P.regularizedProductDirectional_bound hW hε ν H

theorem noncentral_regularizedProductHessian_integrable {p r d : ℕ}
    (P : BlockPartition p d) {α : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p))
    {ε : ℝ} (hε : 0 < ε) (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j)
    (H J : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (P.regularizedProductHessian ε ν H J) (noncentralWishartLaw α S M) := by
  have hi := (P.noncentral_shiftedDeterminantProduct_integrable hα S M
    (fun _ => ε • 1) ν hν).norm.const_mul
      ((P.regularizedFirstConstant ν ε ^ 2 + P.regularizedSecondConstant ν ε) * ‖H‖ * ‖J‖)
  apply hi.mono' (P.measurable_regularizedProductHessian ε ν H J).aestronglyMeasurable
  filter_upwards [noncentralWishart_positiveSemidefinite α S M] with W hW
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    P.regularizedProductHessian_bound hW hε ν H J

theorem regularizedProduct_directional {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H : Matrix (Fin p) (Fin p) ℝ) :
    HasDerivAt (fun t : ℝ => P.shiftedDeterminantProduct (fun _ => ε • 1) ν (W + t • H))
      (P.regularizedProductDirectional ε ν H W) 0 := by
  have h := determinant_product_directional (P.regularizedBlocks ε W)
    (fun j => P.block H j) ν (fun j => (P.regularizedBlocks_posDef hW hε j).det_pos)
  convert h using 1
  · funext t
    change determinantProductValue (P.regularizedBlocks ε (W + t • H)) ν = _
    apply congrArg (fun A => determinantProductValue A ν)
    funext j
    unfold regularizedBlocks block
    simp only [Matrix.submatrix_add, Matrix.submatrix_smul]
    exact add_right_comm _ _ _
  · rfl

theorem regularizedProduct_hessian_directional {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (H J : Matrix (Fin p) (Fin p) ℝ) :
    HasDerivAt (fun t : ℝ => P.regularizedProductDirectional ε ν H (W + t • J))
      (P.regularizedProductHessian ε ν H J W) 0 := by
  have h := determinantProductHessianValue_derivative (P.regularizedBlocks ε W)
    (fun j => P.block H j) (fun j => P.block J j) ν (P.regularizedBlocks_posDef hW hε)
  convert h using 1
  · funext t
    unfold regularizedProductDirectional
    apply congrArg (fun A => determinantProductDirectional A (fun j => P.block H j) ν)
    funext j
    unfold regularizedBlocks block
    simp only [Matrix.submatrix_add, Matrix.submatrix_smul]
    exact add_right_comm _ _ _
  · rfl

end BlockPartition

end ResearchMain.WishartBlocks
