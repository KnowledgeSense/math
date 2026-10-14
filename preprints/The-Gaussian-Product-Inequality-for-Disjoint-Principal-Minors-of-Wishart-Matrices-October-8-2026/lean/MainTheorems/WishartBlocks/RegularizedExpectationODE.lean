import MainTheorems.WishartBlocks.WishartDifferentialContraction
import MainTheorems.WishartBlocks.MeanRayMonotonicity

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

theorem meanOperatorExpression_re (q s : ℝ) (z₁ z₂ : ℂ) :
    (z₂ / 2 + (q - 1 : ℂ) * z₁ / (2 * (s : ℂ))).re =
      z₂.re / 2 + (q - 1) * z₁.re / (2 * s) := by
  have hden : (2 : ℂ) * (s : ℂ) = ((2 * s : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hden]
  simp only [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofNat_re,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, sub_zero, zero_mul]

namespace BlockPartition

theorem regularized_differential_integrand_integrable {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q s : ℝ}
    (hε : 0 < ε) (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (i : WishartDifferentialIndex p) :
    Integrable (fun x => (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p))
        (P.smoothProductEuclidean ν ε)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x))) (oneRowInputLaw q S) := by
  let L := (wishartDifferenceDirections i).map (matrixCoordinates p)
  let C := P.regularizedJetConstant ν ε L.length * ∏ j : Fin L.length, ‖L.get j‖
  have hL : L.length ≤ 2 := by cases i <;> simp [L, wishartDifferenceDirections]
  have hC : 0 ≤ C := mul_nonneg (P.regularizedJetConstant_nonneg ν hε _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hf := P.smoothProductEuclidean_contDiff ν hε
  apply ((P.regularizedProduct_coefficient_integrable hq hs S v ε ν hν i).const_mul C).mono' (by
    exact (((wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal).mul
      ((functionDirections_contDiff hf L).continuous.measurable.comp
        ((matrixCoordinates p).continuous.measurable.comp
          (measurable_oneRowWishartValue S (s • v))))).aestronglyMeasurable)
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have hW := oneRowWishartValue_positive S v s hx
  rw [norm_mul, Complex.norm_real]
  have hJ := P.smoothProductEuclidean_jet_bound ν hε hW hL
  have hB := (functionDirections_norm hf L (matrixCoordinates p (oneRowWishartValue S (s • v) x))).trans
    (mul_le_mul_of_nonneg_right hJ (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  calc
    _ ≤ ‖wishartDifferenceCoefficient q S v s i x‖ *
        ((‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν (oneRowWishartValue S (s • v) x)‖ *
          P.regularizedJetConstant ν ε L.length) * ∏ j : Fin L.length, ‖L.get j‖) :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = _ := by dsimp [C]; ring

theorem regularizedProductOperator_integrable {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q s : ℝ}
    (hε : 0 < ε) (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun x => (P.regularizedProductOperator ν ε q v
      (oneRowWishartValue S (s • v) x) : ℂ)) (oneRowInputLaw q S) := by
  have hi₁ := P.gaussianProductFirst_integrable ν hν hε hq S v s
  have hi₂ := P.gaussianProductSecond_integrable ν hν hε hq S v s
  have hiD := integrable_finsetSum Finset.univ (fun i _ =>
    P.regularized_differential_integrand_integrable ν hν hε hq hs S v i)
  apply (((hi₂.div_const 2).add ((hi₁.const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ)))).sub hiD).congr
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have h := wishart_differential_contraction (P.smoothProductEuclidean_contDiff ν hε) q S v hs hx
  rw [P.smoothProductEuclidean_operator ν hε q v (oneRowWishartValue_positive S v s hx)] at h
  simp only [Pi.sub_apply, Pi.add_apply]
  linear_combination -h

theorem gaussianProduct_mean_ode {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q s : ℝ}
    (hε : 0 < ε) (hq : (p : ℝ) < q) (hs : 0 < s)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ x, (P.regularizedProductOperator ν ε q v (oneRowWishartValue S (s • v) x) : ℂ)
      ∂(oneRowInputLaw q S)) =
      P.gaussianProductSecondIntegral ν ε q S v s / 2 +
        (q - 1 : ℂ) * P.gaussianProductFirstIntegral ν ε q S v s / (2 * (s : ℂ)) := by
  have hi₁ := P.gaussianProductFirst_integrable ν hν hε hq S v s
  have hi₂ := P.gaussianProductSecond_integrable ν hν hε hq S v s
  have hiD (i : WishartDifferentialIndex p) :=
    P.regularized_differential_integrand_integrable ν hν hε hq hs S v i
  have he : (fun x => (P.regularizedProductOperator ν ε q v (oneRowWishartValue S (s • v) x) : ℂ)) =ᵐ[
      oneRowInputLaw q S] (fun x =>
        gaussianMatrixTestSecond (P.smoothProductEuclidean ν ε) S v s x / 2 +
        (q - 1 : ℂ) * gaussianMatrixTestFirst (P.smoothProductEuclidean ν ε) S v s x / (2 * (s : ℂ)) -
        ∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
          functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p))
            (P.smoothProductEuclidean ν ε)
              (matrixCoordinates p (oneRowWishartValue S (s • v) x))) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    have h := wishart_differential_contraction (P.smoothProductEuclidean_contDiff ν hε) q S v hs hx
    rw [P.smoothProductEuclidean_operator ν hε q v (oneRowWishartValue_positive S v s hx)] at h
    linear_combination h
  rw [integral_congr_ae he]
  change (∫ x, (((fun x => gaussianMatrixTestSecond (P.smoothProductEuclidean ν ε) S v s x / 2) +
    (fun x => (q - 1 : ℂ) * gaussianMatrixTestFirst (P.smoothProductEuclidean ν ε) S v s x / (2 * (s : ℂ)))) -
    (fun x => ∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p))
        (P.smoothProductEuclidean ν ε)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)))) x ∂(oneRowInputLaw q S)) = _
  simp only [Pi.sub_apply]
  rw [integral_sub
    ((hi₂.div_const 2).add ((hi₁.const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ))))
      (integrable_finsetSum Finset.univ (fun i _ => hiD i))]
  simp only [Pi.add_apply]
  rw [integral_add (hi₂.div_const 2) ((hi₁.const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ))),
    integral_div, integral_div, integral_const_mul,
    integral_finsetSum (s := Finset.univ) (fun i _ => hiD i),
    P.oneRowWishart_regularized_differential_identity hq hs hS v hε ν hν, sub_zero]
  rfl

theorem gaussianProduct_mean_ode_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q s : ℝ}
    (hε : 0 < ε) (hq : (p : ℝ) < q) (hs : 0 < s)
    (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ (P.gaussianProductSecondIntegral ν ε q S v s).re / 2 +
      (q - 1) * (P.gaussianProductFirstIntegral ν ε q S v s).re / (2 * s) := by
  have he := P.gaussianProduct_mean_ode ν hν hε hq hs hS v
  have hR : 0 ≤ (∫ x, (P.regularizedProductOperator ν ε q v
      (oneRowWishartValue S (s • v) x) : ℂ) ∂(oneRowInputLaw q S)).re := by
    rw [integral_complex_ofReal]
    change 0 ≤ ∫ x, P.regularizedProductOperator ν ε q v
      (oneRowWishartValue S (s • v) x) ∂(oneRowInputLaw q S)
    apply integral_nonneg_of_ae
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    exact P.regularizedProductOperator_nonneg ν hν hε hqB v (oneRowWishartValue_positive S v s hx)
  have hreal : (∫ x, (P.regularizedProductOperator ν ε q v
      (oneRowWishartValue S (s • v) x) : ℂ) ∂(oneRowInputLaw q S)).re =
      (P.gaussianProductSecondIntegral ν ε q S v s).re / 2 +
        (q - 1) * (P.gaussianProductFirstIntegral ν ε q S v s).re / (2 * s) := by
    rw [he]
    exact meanOperatorExpression_re q s _ _
  rwa [hreal] at hR

theorem regularizedProduct_mean_ray_monotone {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ}
    (hε : 0 < ε) (hq : (p : ℝ) < q) (hq₁ : 1 < q)
    (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun θ => (P.gaussianProductExpectation ν ε q S v (Real.sqrt θ)).re) (Set.Ici 0) := by
  apply meanRay_monotone (h := fun s => (P.gaussianProductExpectation ν ε q S v s).re) hq₁
    (h₁ := fun s => (P.gaussianProductFirstIntegral ν ε q S v s).re)
    (h₂ := fun s => (P.gaussianProductSecondIntegral ν ε q S v s).re)
  · intro s
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (P.gaussianProductExpectation_hasDerivAt ν hν hε hq S v s)
  · intro s
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (P.gaussianProductFirstIntegral_hasDerivAt ν hν hε hq S v s)
  · intro s hs
    exact P.gaussianProduct_mean_ode_nonneg ν hν hε hq hs hqB hS v

end BlockPartition
end ResearchMain.WishartBlocks
