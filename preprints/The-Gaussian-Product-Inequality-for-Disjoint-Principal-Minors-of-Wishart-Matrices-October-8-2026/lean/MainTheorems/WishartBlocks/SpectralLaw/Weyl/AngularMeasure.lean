import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CoordinateProduct

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false in
theorem jointExponentialCoordinates_contDiff (n : ℕ) :
    ContDiff ℝ 1 (jointExponentialCoordinates (n := n)) := by
  have hexp : ContDiff ℝ 1 (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) :=
    contDiff_iff_contDiffAt.mpr fun W => (NormedSpace.exp_analytic (𝕂 := ℝ) W).contDiffAt
  have hQ := hexp.comp (skewContinuousLinearMap n).contDiff
  have hQT := hexp.comp (-skewContinuousLinearMap n).contDiff
  have h := (lowerContinuousLinearMap n).contDiff.comp
    ((hQ.mul (diagonalContinuousLinearMap n).contDiff).mul hQT)
  convert h using 1
  funext z
  change symmetricCoordinates (exponentialOrthogonalMatrix z *
      Matrix.diagonal (diagonalCoordinates z) * (exponentialOrthogonalMatrix z).transpose) =
    symmetricCoordinates (exponentialOrthogonalMatrix z *
      Matrix.diagonal (diagonalCoordinates z) * NormedSpace.exp (-skewMatrix z))
  rw [exponentialOrthogonalMatrix_transpose]

theorem gapProduct_pos_of_strictMono {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    0 < gapProduct lam := by
  apply Finset.prod_pos
  intro ij hij
  exact sub_pos.mpr (hlam (Finset.mem_filter.mp hij).2)

theorem gapProduct_continuous (n : ℕ) : Continuous (gapProduct (n := n)) := by
  unfold gapProduct
  fun_prop

noncomputable def referenceSpectrum (n : ℕ) (i : Fin n) : ℝ := i.val

theorem referenceSpectrum_strictMono (n : ℕ) : StrictMono (referenceSpectrum n) := by
  intro i j hij
  change (i.val : ℝ) < (j.val : ℝ)
  exact_mod_cast (show i.val < j.val from hij)

noncomputable def angularJacobian {n : ℕ} (z : LowerIndex n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |(angularDerivative (angleCoordinates z)).det|

theorem angularJacobian_continuous (n : ℕ) : Continuous (angularJacobian (n := n)) := by
  let lam₀ := referenceSpectrum n
  have hlam₀ : StrictMono lam₀ := referenceSpectrum_strictMono n
  have hp : Continuous (spectralParameters lam₀) := by
    apply continuous_pi
    intro e
    unfold spectralParameters
    split_ifs
    · exact continuous_const
    · exact continuous_apply e
  have hd : Continuous (fun z : LowerIndex n → ℝ =>
      |(fderiv ℝ jointExponentialCoordinates (spectralParameters lam₀ z)).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      (((jointExponentialCoordinates_contDiff n).continuous_fderiv one_ne_zero).comp hp)).abs
  have hdet (z : LowerIndex n → ℝ) :
      |(angularDerivative (angleCoordinates z)).det| =
        |(fderiv ℝ jointExponentialCoordinates (spectralParameters lam₀ z)).det| /
          gapProduct lam₀ := by
    apply (eq_div_iff (ne_of_gt (gapProduct_pos_of_strictMono hlam₀))).mpr
    have h := jointExponentialCoordinates_abs_det_separated
      (spectralParameters lam₀ z) (by simpa using hlam₀)
    simpa only [diagonalCoordinates_spectralParameters,
      angleCoordinates_spectralParameters, mul_comm] using h.symm
  change Continuous (fun z : LowerIndex n → ℝ =>
    ENNReal.ofReal |(angularDerivative (angleCoordinates z)).det|)
  simp_rw [hdet]
  exact ENNReal.continuous_ofReal.comp (hd.div_const _)

theorem lintegral_coordinateProduct_restrict {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀)
    {F : (LowerIndex n → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in angularPatchDomain lam₀ hlam₀, F z) =
      ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
        ∫⁻ θ in angularParameterPatch lam₀ hlam₀, F (jointParameters lam θ) := by
  have hpre : (coordinateProductEquiv n) ⁻¹' angularPatchDomain lam₀ hlam₀ =
      {lam : Fin n → ℝ | StrictMono lam} ×ˢ angularParameterPatch lam₀ hlam₀ := by
    ext p
    exact jointParameters_mem_angularPatchDomain_iff lam₀ hlam₀ p.1 p.2
  rw [← (coordinateProductEquiv_measurePreserving n).setLIntegral_comp_preimage_emb
    (coordinateProductEquiv n).measurableEmbedding F (angularPatchDomain lam₀ hlam₀), hpre]
  exact setLIntegral_prod _ (hF.comp (coordinateProductEquiv n).measurable).aemeasurable

noncomputable def angularWeylConstant {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀) : ℝ≥0∞ :=
  (orthogonalHaar n (angularOrbitPatch lam₀ hlam₀ lam₀))⁻¹ *
    ∫⁻ θ in angularParameterPatch lam₀ hlam₀, angularJacobian (angleParameters θ)

theorem angularJacobian_jointParameters {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) :
    angularJacobian (jointParameters lam θ) = angularJacobian (angleParameters θ) := by
  simp only [angularJacobian, angleParameters, angleCoordinates_jointParameters]

end ResearchMain.WishartBlocks.Weyl
