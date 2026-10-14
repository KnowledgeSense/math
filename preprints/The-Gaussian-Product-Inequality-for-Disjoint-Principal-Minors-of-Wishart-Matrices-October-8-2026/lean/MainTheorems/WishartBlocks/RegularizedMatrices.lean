import MainTheorems.WishartBlocks.OperatorPositivity
import MainTheorems.WishartBlocks.MatrixGrowth
import Mathlib.Topology.Instances.Matrix

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

theorem positiveSemidefinite_diagonal_le_trace {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) (i : Fin n) :
    G i i ≤ G.trace := by
  exact Finset.single_le_sum (fun j _ => hG.diag_nonneg (i := j)) (Finset.mem_univ i)

theorem positiveSemidefinite_entry_le_trace {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) (i j : Fin n) :
    ‖G i j‖ ≤ G.trace := by
  have hi := positiveSemidefinite_diagonal_le_trace hG i
  have hj := positiveSemidefinite_diagonal_le_trace hG j
  have hs : G j i = G i j := by simpa only [star_trivial] using hG.1.apply i j
  have hp : 0 ≤ G i i + 2 * G i j + G j j := by
    have h := hG.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) + Pi.single j 1)
    convert h using 1
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hs]
    ring
  have hm : 0 ≤ G i i - 2 * G i j + G j j := by
    have h := hG.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) - Pi.single j 1)
    convert h using 1
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
      Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hs]
    ring
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem positiveSemidefinite_norm_le_trace {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) : ‖G‖ ≤ G.trace := by
  exact (Matrix.norm_le_iff hG.trace_nonneg).mpr (positiveSemidefinite_entry_le_trace hG)

theorem positiveSemidefinite_add_identity_posDef {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (W + ε • 1).PosDef :=
  Matrix.PosDef.posSemidef_add hW ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).smul hε)

theorem regularized_inverse_trace_bound {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ((W + ε • 1)⁻¹).trace ≤ (n : ℝ) / ε := by
  let A := W + ε • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hA : A.PosDef := positiveSemidefinite_add_identity_posDef hW hε
  have hWA : W ≤ A := by
    change (W + ε • 1 - W).PosSemidef
    simpa only [add_sub_cancel_left] using
      (Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul hε.le
  have ht := (inverse_trace_bounds hA hW hWA).1
  have he : (A⁻¹ * W).trace = (n : ℝ) - ε * (A⁻¹).trace := by
    have hw : W = A - ε • 1 := by dsimp [A]; module
    rw [hw, mul_sub, Matrix.mul_smul, mul_one,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Matrix.trace_smul, smul_eq_mul]
  rw [he] at ht
  exact (le_div_iff₀ hε).mpr (by linarith)

theorem regularized_inverse_norm_bound {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ‖(W + ε • 1)⁻¹‖ ≤ (n : ℝ) / ε :=
  (positiveSemidefinite_norm_le_trace
    (positiveSemidefinite_add_identity_posDef hW hε).posSemidef.inv).trans
      (regularized_inverse_trace_bound hW hε)

theorem trace_product_entry_bound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    {c d : ℝ} (hc : 0 ≤ c) (hA : ∀ i j, ‖A i j‖ ≤ c)
    (hB : ∀ i j, ‖B i j‖ ≤ d) : ‖(A * B).trace‖ ≤ (n : ℝ) ^ 2 * c * d := by
  calc
    ‖(A * B).trace‖ ≤ ∑ i : Fin n, ‖(A * B) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, (n : ℝ) * c * d :=
      Finset.sum_le_sum fun i _ => matrix_product_entry_bound A B hc hA hB i i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

theorem matrix_product_norm_bound {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    ‖A * B‖ ≤ (n : ℝ) * ‖A‖ * ‖B‖ := by
  exact (Matrix.norm_le_iff (by positivity)).mpr
    (matrix_product_entry_bound A B (norm_nonneg A)
      (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm A)
      (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm B))

theorem regularized_trace_direction_bound {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    ‖((W + ε • 1)⁻¹ * H).trace‖ ≤ (n : ℝ) ^ 2 * ((n : ℝ) / ε) * ‖H‖ := by
  exact trace_product_entry_bound _ H (by positivity)
    (fun i j => (Matrix.norm_entry_le_entrywise_sup_norm _).trans
      (regularized_inverse_norm_bound hW hε))
    (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm H)

theorem regularized_trace_hessian_bound {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (H J : Matrix (Fin n) (Fin n) ℝ) :
    ‖((W + ε • 1)⁻¹ * J * (W + ε • 1)⁻¹ * H).trace‖ ≤
      (n : ℝ) ^ 4 * ((n : ℝ) / ε) ^ 2 * ‖H‖ * ‖J‖ := by
  let G := (W + ε • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
  have hG : ‖G‖ ≤ (n : ℝ) / ε := regularized_inverse_norm_bound hW hε
  have hGJ := matrix_product_norm_bound G J
  have hGJ' : ‖G * J‖ ≤ (n : ℝ) * ((n : ℝ) / ε) * ‖J‖ := by
    apply hGJ.trans
    gcongr
  have hGJG := matrix_product_norm_bound (G * J) G
  have ht := trace_product_entry_bound (G * J * G) H (norm_nonneg _)
    (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm _)
    (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm H)
  calc
    _ ≤ (n : ℝ) ^ 2 * ‖G * J * G‖ * ‖H‖ := ht
    _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) / ε) * ‖J‖) *
        ((n : ℝ) / ε)) * ‖H‖ := by
      gcongr
      exact hGJG.trans (by gcongr)
    _ = _ := by ring

theorem measurable_matrix_inverse {n : ℕ} :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

end ResearchMain.WishartBlocks

