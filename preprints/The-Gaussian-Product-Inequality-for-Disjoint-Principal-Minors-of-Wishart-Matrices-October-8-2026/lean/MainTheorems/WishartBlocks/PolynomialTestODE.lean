import MainTheorems.WishartBlocks.PolynomialPSDTest

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

namespace PolynomialPSDTest

theorem cutoff_direction_bound {p : ℕ} (F : PolynomialPSDTest p)
    (L : List (MatrixEuclidean p)) (hL : L.length ≤ 2) (C : ℕ → ℝ)
    (hC : ∀ k N (x : MatrixEuclidean p), ‖iteratedFDeriv ℝ k (expandingCutoff N) x‖ ≤ C k)
    (N : ℕ) {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    ‖functionDirections L (compactApproximation N F.toFun) (matrixCoordinates p W)‖ ≤
      ((∑ k ∈ Finset.range (L.length + 1), (L.length.choose k : ℝ) * C k *
          F.jetConstant (L.length - k)) * ∏ i : Fin L.length, ‖L.get i‖) *
        (1 + ‖W‖) ^ F.exponent := by
  apply (functionDirections_norm (compactApproximation_contDiff N F.smooth) L _).trans
  have hj := compactApproximation_jet_bound F.smooth C hC N L.length (matrixCoordinates p W)
  have hb : ‖iteratedFDeriv ℝ L.length (compactApproximation N F.toFun) (matrixCoordinates p W)‖ ≤
      (∑ k ∈ Finset.range (L.length + 1), (L.length.choose k : ℝ) * C k *
        F.jetConstant (L.length - k)) * (1 + ‖W‖) ^ F.exponent := by
    apply hj.trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hC0 : 0 ≤ C k := (norm_nonneg _).trans (hC k N (matrixCoordinates p W))
    exact (mul_le_mul_of_nonneg_left (F.jet_bound _ ((Nat.sub_le _ _).trans hL) W hW)
      (mul_nonneg (Nat.cast_nonneg _) hC0)).trans_eq (by ring)
  calc
    _ ≤ ((∑ k ∈ Finset.range (L.length + 1), (L.length.choose k : ℝ) * C k *
        F.jetConstant (L.length - k)) * (1 + ‖W‖) ^ F.exponent) *
          ∏ i : Fin L.length, ‖L.get i‖ :=
      mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

theorem coefficient_power_integrable {p : ℕ} (F : PolynomialPSDTest p)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (i : WishartDifferentialIndex p) :
    Integrable (fun x => ‖wishartDifferenceCoefficient q S v s i x‖ *
      (1 + ‖oneRowWishartValue S (s • v) x‖) ^ F.exponent) (oneRowInputLaw q S) := by
  let B := oneRowMatrixBound S v s
  have hB : 0 ≤ B := by dsimp [B, oneRowMatrixBound]; positivity
  have hC := wishartDifferenceBound_nonneg q S v s
  have hc := (wishartDifferenceCoefficient_measurable q S v s i).norm
  have hw : Measurable (fun x => ‖oneRowWishartValue S (s • v) x‖) :=
    Measurable.norm (α := Fin p → Fin p → ℝ) (measurable_oneRowWishartValue S (s • v))
  apply oneRowInput_real_growth_integrable hq S (by fun_prop)
    (C := wishartDifferenceBound q S v s * (1 + B) ^ F.exponent)
    (β := 1 + 2 * F.exponent) (by positivity)
  intro x
  have hW : 1 + ‖oneRowWishartValue S (s • v) x‖ ≤ (1 + B) * (1 + ‖x‖) ^ 2 := by
    have h := oneRowWishartValue_norm_bound S v s x
    change ‖oneRowWishartValue S (s • v) x‖ ≤ B * (1 + ‖x‖) ^ 2 at h
    nlinarith [norm_nonneg x]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (wishartDifferenceBound q S v s * (1 + ‖x‖)) *
        (((1 + B) * (1 + ‖x‖) ^ 2) ^ F.exponent) :=
      mul_le_mul (wishartDifferenceCoefficient_bound q S v hs i x)
        (Real.rpow_le_rpow (by positivity) hW F.exponent_nonneg)
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) 2, Real.rpow_add (by positivity), Real.rpow_one]
      norm_num only [Nat.cast_ofNat]
      ring

theorem differential_integrand_integrable {p : ℕ} (F : PolynomialPSDTest p)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (i : WishartDifferentialIndex p) :
    Integrable (fun x => (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) F.toFun
        (matrixCoordinates p (oneRowWishartValue S (s • v) x))) (oneRowInputLaw q S) := by
  let L := (wishartDifferenceDirections i).map (matrixCoordinates p)
  let C := F.jetConstant L.length * ∏ j : Fin L.length, ‖L.get j‖
  have hL : L.length ≤ 2 := by cases i <;> simp [L, wishartDifferenceDirections]
  have hC : 0 ≤ C := mul_nonneg (F.jetConstant_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply ((F.coefficient_power_integrable hq hs S v i).const_mul C).mono' (by
    exact (((wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal).mul
      ((functionDirections_contDiff F.smooth L).continuous.measurable.comp
        ((matrixCoordinates p).continuous.measurable.comp
          (measurable_oneRowWishartValue S (s • v))))).aestronglyMeasurable)
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  rw [norm_mul, Complex.norm_real]
  have hB := (functionDirections_norm F.smooth L _).trans
    (mul_le_mul_of_nonneg_right (F.jet_bound _ hL _ (oneRowWishartValue_positive S v s hx))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans_eq (by dsimp [C]; ring)

theorem differential_identity {p : ℕ} (F : PolynomialPSDTest p)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    (∑ i : WishartDifferentialIndex p, ∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) F.toFun
        (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂(oneRowInputLaw q S)) = 0 := by
  classical
  let μ := oneRowInputLaw q S
  let L (i : WishartDifferentialIndex p) := (wishartDifferenceDirections i).map (matrixCoordinates p)
  choose C hCpos hC using fun k : ℕ => expandingCutoff_derivative_bound (E := MatrixEuclidean p) k
  let K (i : WishartDifferentialIndex p) :=
    (∑ k ∈ Finset.range ((L i).length + 1), ((L i).length.choose k : ℝ) * C k *
      F.jetConstant ((L i).length - k)) * ∏ j : Fin (L i).length, ‖(L i).get j‖
  have hL (i : WishartDifferentialIndex p) : (L i).length ≤ 2 := by
    cases i <;> simp [L, wishartDifferenceDirections]
  have hK (i : WishartDifferentialIndex p) : 0 ≤ K i := by
    dsimp [K]
    exact mul_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hCpos k).le) (F.jetConstant_nonneg _))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hT (i : WishartDifferentialIndex p) : Tendsto (fun N : ℕ => ∫ x,
      (wishartDifferenceCoefficient q S v s i x : ℂ) * functionDirections (L i)
        (compactApproximation N F.toFun) (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ)
      atTop (𝓝 (∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) * functionDirections (L i)
        F.toFun (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => K i *
      (‖wishartDifferenceCoefficient q S v s i x‖ *
        (1 + ‖oneRowWishartValue S (s • v) x‖) ^ F.exponent))
    · intro N
      exact (((wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal).mul
        ((functionDirections_contDiff (compactApproximation_contDiff N F.smooth) (L i)).continuous.measurable.comp
          ((matrixCoordinates p).continuous.measurable.comp
            (measurable_oneRowWishartValue S (s • v))))).aestronglyMeasurable
    · exact (F.coefficient_power_integrable hq hs S v i).const_mul (K i)
    · intro N
      filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left
        (F.cutoff_direction_bound (L i) (hL i) C hC N (oneRowWishartValue_positive S v s hx))
        (norm_nonneg _)).trans_eq (by ring)
    · exact ae_of_all _ fun x => tendsto_const_nhds.mul
        (compactApproximation_directions_tendsto F.toFun (L i)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hT i)
  have he : (fun N : ℕ => ∑ i : WishartDifferentialIndex p, ∫ x,
      (wishartDifferenceCoefficient q S v s i x : ℂ) * functionDirections (L i)
        (compactApproximation N F.toFun) (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ) = 0 := by
    funext N
    exact oneRowWishart_compact_differential_identity hq hs hS v (compactApproximation N F.toFun)
      (compactApproximation_contDiff N F.smooth) (compactApproximation_compact N F.toFun)
  rw [he] at hsum
  exact tendsto_nhds_unique hsum tendsto_const_nhds

theorem operator_integrable {p : ℕ} (F : PolynomialPSDTest p)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun x => matrixTestOperator F.toFun q v (oneRowWishartValue S (s • v) x))
      (oneRowInputLaw q S) := by
  have hiD := integrable_finsetSum Finset.univ (fun i _ => F.differential_integrand_integrable hq hs S v i)
  apply ((((F.second_integrable hq S v s).div_const 2).add
    (((F.first_integrable hq S v s).const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ)))).sub hiD).congr
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have h := wishart_differential_contraction F.smooth q S v hs hx
  simp only [Pi.sub_apply, Pi.add_apply]
  linear_combination -h

theorem mean_ode {p : ℕ} (F : PolynomialPSDTest p)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ x, matrixTestOperator F.toFun q v (oneRowWishartValue S (s • v) x) ∂(oneRowInputLaw q S)) =
      F.secondIntegral q S v s / 2 + (q - 1 : ℂ) * F.firstIntegral q S v s / (2 * (s : ℂ)) := by
  have hi₁ := F.first_integrable hq S v s
  have hi₂ := F.second_integrable hq S v s
  have hiD i := F.differential_integrand_integrable hq hs S v i
  have he : (fun x => matrixTestOperator F.toFun q v (oneRowWishartValue S (s • v) x)) =ᵐ[
      oneRowInputLaw q S] (fun x => gaussianMatrixTestSecond F.toFun S v s x / 2 +
      (q - 1 : ℂ) * gaussianMatrixTestFirst F.toFun S v s x / (2 * (s : ℂ)) -
      ∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) F.toFun
          (matrixCoordinates p (oneRowWishartValue S (s • v) x))) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    have h := wishart_differential_contraction F.smooth q S v hs hx
    linear_combination h
  rw [integral_congr_ae he]
  change (∫ x, (((fun x => gaussianMatrixTestSecond F.toFun S v s x / 2) +
    (fun x => (q - 1 : ℂ) * gaussianMatrixTestFirst F.toFun S v s x / (2 * (s : ℂ)))) -
    (fun x => ∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) F.toFun
        (matrixCoordinates p (oneRowWishartValue S (s • v) x)))) x ∂(oneRowInputLaw q S)) = _
  simp only [Pi.sub_apply]
  rw [integral_sub
    ((hi₂.div_const 2).add ((hi₁.const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ))))
      (integrable_finsetSum Finset.univ (fun i _ => hiD i))]
  simp only [Pi.add_apply]
  rw [integral_add (hi₂.div_const 2) ((hi₁.const_mul (q - 1 : ℂ)).div_const (2 * (s : ℂ))),
    integral_div, integral_div, integral_const_mul,
    integral_finsetSum (s := Finset.univ) (fun i _ => hiD i),
    F.differential_identity hq hs hS v, sub_zero]
  rfl

theorem mean_ray_monotone {p : ℕ} (F : PolynomialPSDTest p)
    {q : ℝ} (hq : (p : ℝ) < q) (hq₁ : 1 < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p))
    (hR : ∀ W : Matrix (Fin p) (Fin p) ℝ, W.PosSemidef → 0 ≤ (matrixTestOperator F.toFun q v W).re) :
    MonotoneOn (fun θ => (F.expectation q S v (Real.sqrt θ)).re) (Set.Ici 0) := by
  apply meanRay_monotone (h := fun s => (F.expectation q S v s).re) hq₁
    (h₁ := fun s => (F.firstIntegral q S v s).re)
    (h₂ := fun s => (F.secondIntegral q S v s).re)
  · intro s
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (F.expectation_hasDerivAt hq S v s)
  · intro s
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (F.firstIntegral_hasDerivAt hq S v s)
  · intro s hs
    have hi := F.operator_integrable hq hs S v
    have he := F.mean_ode hq hs hS v
    have hn : 0 ≤ (∫ x, matrixTestOperator F.toFun q v (oneRowWishartValue S (s • v) x)
        ∂(oneRowInputLaw q S)).re := by
      change 0 ≤ Complex.reCLM (∫ x, matrixTestOperator F.toFun q v
        (oneRowWishartValue S (s • v) x) ∂(oneRowInputLaw q S))
      rw [← Complex.reCLM.integral_comp_comm hi]
      exact integral_nonneg_of_ae ((oneRowInput_positiveSemidefinite q S).mono fun x hx =>
        hR _ (oneRowWishartValue_positive S v s hx))
    rw [he, meanOperatorExpression_re] at hn
    exact hn

end PolynomialPSDTest
end ResearchMain.WishartBlocks
