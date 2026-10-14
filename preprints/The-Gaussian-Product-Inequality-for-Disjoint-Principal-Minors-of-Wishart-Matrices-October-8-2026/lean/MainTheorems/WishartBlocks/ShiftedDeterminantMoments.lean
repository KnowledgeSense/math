import MainTheorems.WishartBlocks.NoncentralPolynomialMoments
import MainTheorems.WishartBlocks.WishartRowAugmentation

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

theorem determinant_shift_growth {p n : ℕ} (e : Fin n → Fin p)
    (K : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖(W.submatrix e e + K).det‖ ≤
      (Fintype.card (Equiv.Perm (Fin n)) * (1 + ‖K‖) ^ n) * (1 + ‖W‖) ^ n := by
  have he : ∀ i j, ‖(W.submatrix e e + K) i j‖ ≤ (1 + ‖K‖) * (1 + ‖W‖) := by
    intro i j
    apply (norm_add_le _ _).trans
    have hw : ‖W (e i) (e j)‖ ≤ ‖W‖ := Matrix.norm_entry_le_entrywise_sup_norm W
    have hk : ‖K i j‖ ≤ ‖K‖ := Matrix.norm_entry_le_entrywise_sup_norm K
    simp only [Matrix.submatrix_apply]
    nlinarith [norm_nonneg K, norm_nonneg W, mul_nonneg (norm_nonneg K) (norm_nonneg W)]
  apply (determinant_entry_bound _ he).trans_eq
  rw [mul_pow]
  ring

theorem determinant_shift_power_growth {p n : ℕ} (e : Fin n → Fin p)
    (K : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin p) (Fin p) ℝ)
    {b : ℝ} (hb : 0 ≤ b) :
    ‖(W.submatrix e e + K).det ^ b‖ ≤
      (Fintype.card (Equiv.Perm (Fin n)) * (1 + ‖K‖) ^ n) ^ b *
        (1 + ‖W‖) ^ ((n : ℝ) * b) := by
  calc
    ‖(W.submatrix e e + K).det ^ b‖ ≤ ‖(W.submatrix e e + K).det‖ ^ b := by
      simpa only [Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (W.submatrix e e + K).det b
    _ ≤ ((Fintype.card (Equiv.Perm (Fin n)) * (1 + ‖K‖) ^ n) * (1 + ‖W‖) ^ n) ^ b :=
      Real.rpow_le_rpow (norm_nonneg _) (determinant_shift_growth e K W) hb
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) n b]

namespace BlockPartition

noncomputable def shiftedDeterminantProduct {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∏ j, (P.block W j + K j).det ^ ν j

theorem measurable_shiftedDeterminantProduct {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ) :
    Measurable (P.shiftedDeterminantProduct K ν) := by
  unfold shiftedDeterminantProduct block
  fun_prop

theorem shiftedDeterminantProduct_growth {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖P.shiftedDeterminantProduct K ν W‖ ≤
      (∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) * (1 + ‖K j‖) ^ P.size j) ^ ν j) *
        (1 + ‖W‖) ^ (∑ j, (P.size j : ℝ) * ν j) := by
  unfold shiftedDeterminantProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ j,
        (Fintype.card (Equiv.Perm (Fin (P.size j))) * (1 + ‖K j‖) ^ P.size j) ^ ν j *
          (1 + ‖W‖) ^ ((P.size j : ℝ) * ν j) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j _
      exact determinant_shift_power_growth (P.inclusion j) (K j) W (hν j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity)
        (fun j => (P.size j : ℝ) * ν j) Finset.univ]

theorem noncentral_shiftedDeterminantProduct_integrable {p r d : ℕ}
    (P : BlockPartition p d) {α : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p))
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    Integrable (P.shiftedDeterminantProduct K ν) (noncentralWishartLaw α S M) := by
  apply noncentralWishart_real_growth_integrable
    (C := ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) * (1 + ‖K j‖) ^ P.size j) ^ ν j)
    (β := ∑ j, (P.size j : ℝ) * ν j) hα S M
    (P.measurable_shiftedDeterminantProduct K ν)
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) (ν j))
  exact P.shiftedDeterminantProduct_growth K ν hν

theorem noncentral_determinantProduct_integrable {p r d : ℕ}
    (P : BlockPartition p d) {α : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p))
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    Integrable (P.determinantProduct ν) (noncentralWishartLaw α S M) := by
  convert P.noncentral_shiftedDeterminantProduct_integrable hα S M (fun _ => 0) ν hν using 1
  funext W
  simp only [shiftedDeterminantProduct, add_zero, determinantProduct, determinantPower]

end BlockPartition

theorem oneRowWishart_as_noncentral {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (m : EuclideanSpace ℝ (Fin p)) :
    oneRowWishartLaw q S m = noncentralWishartLaw q S (fun _ : Fin 1 => m) := by
  have hα : (p : ℝ) - 1 < q - ((1 : ℕ) : ℝ) := by norm_num; linarith
  let : IsProbabilityMeasure (oneRowWishartLaw q S m) := oneRowWishart_probability hq S m
  let : IsProbabilityMeasure (noncentralWishartLaw q S (fun _ : Fin 1 => m)) :=
    noncentralWishart_probability hα S _
  apply matrix_measure_eq_of_positive_laplace
    (oneRowWishart_positiveSemidefinite q S m) (noncentralWishart_positiveSemidefinite q S _)
  intro T hT
  rw [oneRowWishart_laplace hq hS hT, noncentralWishart_laplace hα hS hT]
  simp only [meanRowGram, Fin.sum_univ_one, Matrix.trace_mul_comm
    (Matrix.vecMulVec (fun i => m i) (fun i => m i)), trace_vectorGram]

theorem oneRowWishart_polynomial_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    Integrable (fun W : Matrix (Fin p) (Fin p) ℝ => (1 + ‖W‖) ^ k) (oneRowWishartLaw q S m) := by
  rw [oneRowWishart_as_noncentral hq hS m]
  exact noncentralWishart_polynomial_integrable (by norm_num; linarith) S _ k

theorem oneRowWishart_shifted_determinant_integrable {p : ℕ} {q b : ℝ}
    (hq : (p : ℝ) < q) (hb : 0 ≤ b) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (K : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun W : Matrix (Fin p) (Fin p) ℝ => (W + K).det ^ b) (oneRowWishartLaw q S m) := by
  rw [oneRowWishart_as_noncentral hq hS m]
  apply noncentralWishart_real_growth_integrable
    (C := (Fintype.card (Equiv.Perm (Fin p)) * (1 + ‖K‖) ^ p) ^ b)
    (β := (p : ℝ) * b) (by norm_num; linarith) S _ (by fun_prop)
    (Real.rpow_nonneg (by positivity) b)
  intro W
  simpa only [Matrix.submatrix_id_id] using determinant_shift_power_growth id K W hb

end ResearchMain.WishartBlocks
