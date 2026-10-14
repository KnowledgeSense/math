import MainTheorems.WishartBlocks.WishartDifferentialCoefficients

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

theorem euclidean_bilinear_double_sum {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ)
    (y v : EuclideanSpace ℝ (Fin p)) :
    (∑ i, ∑ j, y i * v j * T i j) = ⟪y, T.toEuclideanLin v⟫_ℝ := by
  rw [← euclidean_dotProduct_matrix]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wishart_first_coefficient_contract {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) :
    (∑ i, ∑ j, wishartDifferenceCoefficient q S v s (Sum.inl (i, j)) x * (-T i j)) =
      (q - 1) * (⟪v, T.toEuclideanLin v⟫_ℝ -
        ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ / s) := by
  calc
    _ = (q - 1) * ((∑ i, ∑ j, v i * v j * T i j) -
        (∑ i, ∑ j, oneRowGaussianVector S v s x i * v j * T i j) / s) := by
      simp only [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [wishartDifferenceCoefficient]
      ring
    _ = _ := by rw [euclidean_bilinear_double_sum, euclidean_bilinear_double_sum]

theorem euclidean_quadratic_four_sum {p : ℕ} (T V : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    (∑ i, ∑ j, ∑ k, ∑ l, V i k * v j * v l * T i j * T k l) =
      (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * V).trace := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, V i k * v j * v l * T i j * T k l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, V i k * v j * v l * T i j * T k l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      rw [Matrix.trace_mul_comm, trace_matrix_outer]
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem wishart_second_coefficient_contract {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      wishartDifferenceCoefficient q S v s (Sum.inr ((i, j), (k, l))) x * T i j * T k l) =
      -2 * (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * x.1).trace := by
  rw [← euclidean_quadratic_four_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  dsimp [wishartDifferenceCoefficient]
  ring

theorem wishartDifferenceSymbol_contract {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.IsHermitian)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    (∑ i : WishartDifferentialIndex p,
      matrixLaplaceListSymbol T (wishartDifferenceDirections i) *
        (wishartDifferenceCoefficient q S v s i x : ℂ)) =
      (((q - 1) * (⟪v, T.toEuclideanLin v⟫_ℝ -
          ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ / s) -
        2 * (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * x.1).trace : ℝ) : ℂ) := by
  have h₁ := congrArg (fun z : ℝ => (z : ℂ)) (wishart_first_coefficient_contract q S T v s x)
  have h₂ := congrArg (fun z : ℝ => (z : ℂ)) (wishart_second_coefficient_contract q S T v s x)
  push_cast at h₁ h₂
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, wishartDifferenceDirections,
    matrixLaplaceListSymbol, trace_symmetricDirection T hT.isSymm, mul_one,
    neg_mul, mul_neg, neg_neg]
  have h₁' : (∑ i, ∑ j, -((T i j : ℂ) *
      (wishartDifferenceCoefficient q S v s (Sum.inl (i, j)) x : ℂ))) =
      ((q - 1) * (⟪v, T.toEuclideanLin v⟫_ℝ -
        ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ / s) : ℝ) := by
    push_cast
    simpa only [mul_comm, neg_mul, mul_neg] using h₁
  have h₂' : (∑ i, ∑ j, ∑ k, ∑ l, (T i j : ℂ) * (T k l : ℂ) *
      (wishartDifferenceCoefficient q S v s (Sum.inr ((i, j), (k, l))) x : ℂ)) =
      (-2 * (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * x.1).trace : ℝ) := by
    push_cast
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h₂
  rw [h₁', h₂']
  push_cast
  ring

theorem wishartDifferenceCoefficient_kernel_integrable {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (i : WishartDifferentialIndex p) :
    Integrable (fun x => (wishartDifferenceCoefficient q S v s i x : ℂ) *
      (gaussianMeanLaplace S T v s x : ℂ)) (oneRowInputLaw q S) := by
  apply (wishartDifferenceCoefficient_integrable hq hs S v i).norm.mono' (by
    exact ((wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal.fun_mul
      (gaussianMeanLaplace_measurable S T v s).complex_ofReal).aestronglyMeasurable)
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have hg := gaussianMeanLaplace_bound S hT v s hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hg.1]
  simpa only [Real.norm_eq_abs, mul_one] using
    mul_le_mul_of_nonneg_left hg.2 (norm_nonneg (wishartDifferenceCoefficient q S v s i x))

theorem wishart_difference_laplace_zero {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p))
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef) :
    (∑ i : WishartDifferentialIndex p,
      matrixLaplaceListSymbol T (wishartDifferenceDirections i) *
        ∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
          (Real.exp (-(T * oneRowWishartValue S (s • v) x).trace) : ℂ)
            ∂(oneRowInputLaw q S)) = 0 := by
  have hi (i : WishartDifferentialIndex p) : Integrable
      (fun x => matrixLaplaceListSymbol T (wishartDifferenceDirections i) *
        ((wishartDifferenceCoefficient q S v s i x : ℂ) *
          (gaussianMeanLaplace S T v s x : ℂ))) (oneRowInputLaw q S) :=
    (wishartDifferenceCoefficient_kernel_integrable hq hs S hT v i).const_mul _
  change (∑ i, matrixLaplaceListSymbol T (wishartDifferenceDirections i) *
    ∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      (gaussianMeanLaplace S T v s x : ℂ) ∂(oneRowInputLaw q S)) = 0
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum (s := Finset.univ) (fun i _ => hi i)]
  have he : (fun x => ∑ i : WishartDifferentialIndex p,
      matrixLaplaceListSymbol T (wishartDifferenceDirections i) *
        ((wishartDifferenceCoefficient q S v s i x : ℂ) *
          (gaussianMeanLaplace S T v s x : ℂ))) =
      fun x => (rankOneDifferenceLaplace q S T v s x : ℂ) := by
    funext x
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, wishartDifferenceSymbol_contract q S hT.1 v s x]
    dsimp [rankOneDifferenceLaplace]
    push_cast
    ring
  rw [he, integral_complex_ofReal, rankOneDifferenceLaplace_integral_zero hq hs hS hT v,
    Complex.ofReal_zero]

end ResearchMain.WishartBlocks
