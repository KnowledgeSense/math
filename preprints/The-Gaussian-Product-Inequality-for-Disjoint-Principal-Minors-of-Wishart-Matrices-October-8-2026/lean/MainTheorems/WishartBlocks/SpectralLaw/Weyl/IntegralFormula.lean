import MainTheorems.WishartBlocks.SpectralLaw.Weyl.AngularMeasure

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Operator

theorem symmetricCoordinates_diagonal_continuous (n : ℕ) :
    Continuous (fun lam : Fin n → ℝ => symmetricCoordinates (Matrix.diagonal lam)) := by
  unfold symmetricCoordinates
  fun_prop

theorem weyl_lintegral {n : ℕ} {lam₀ : Fin n → ℝ} (hlam₀ : StrictMono lam₀)
    {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ W, G W) = angularWeylConstant lam₀ hlam₀.injective *
      ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
        ENNReal.ofReal (gapProduct lam) * coordinateOrthogonalAverageNN G
          (symmetricCoordinates (Matrix.diagonal lam)) := by
  let mass := orthogonalHaar n (angularOrbitPatch lam₀ hlam₀.injective lam₀)
  let B := ∫⁻ θ in angularParameterPatch lam₀ hlam₀.injective,
    angularJacobian (angleParameters θ)
  let F : (LowerIndex n → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (gapProduct (diagonalCoordinates z)) * angularJacobian z *
      coordinateOrthogonalAverageNN G
        (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z)))
  have hd : Continuous (diagonalCoordinates (n := n)) :=
    continuous_pi fun _ => continuous_apply _
  have hg : Measurable (fun lam : Fin n → ℝ =>
      ENNReal.ofReal (gapProduct lam) * coordinateOrthogonalAverageNN G
        (symmetricCoordinates (Matrix.diagonal lam))) :=
    (ENNReal.continuous_ofReal.comp (gapProduct_continuous n)).measurable.mul
      ((coordinateOrthogonalAverageNN_measurable hG).comp
        (symmetricCoordinates_diagonal_continuous n).measurable)
  have hF : Measurable F :=
    ((ENNReal.continuous_ofReal.comp ((gapProduct_continuous n).comp hd)).measurable.mul
      (angularJacobian_continuous n).measurable).mul
        ((coordinateOrthogonalAverageNN_measurable hG).comp
          ((symmetricCoordinates_diagonal_continuous n).comp hd).measurable)
  have hang : Measurable (fun θ : StrictLowerIndex n → ℝ =>
      angularJacobian (angleParameters θ)) :=
    ((angularJacobian_continuous n).comp (angleParameters_continuous n)).measurable
  calc
    _ = mass⁻¹ * ∫⁻ z in angularPatchDomain lam₀ hlam₀.injective,
        ENNReal.ofReal (gapProduct (diagonalCoordinates z) *
          |(angularDerivative (angleCoordinates z)).det|) *
            coordinateOrthogonalAverageNN G
              (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z))) :=
      angularPatch_lintegral_changeOfVariables hlam₀ hG
    _ = mass⁻¹ * ∫⁻ z in angularPatchDomain lam₀ hlam₀.injective, F z := by
      congr 1
      apply setLIntegral_congr_fun (angularPatchDomain_isOpen _ _).measurableSet
      intro z hz
      dsimp only
      rw [ENNReal.ofReal_mul (gapProduct_pos_of_strictMono hz.1).le]
      rfl
    _ = mass⁻¹ * ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
        ∫⁻ θ in angularParameterPatch lam₀ hlam₀.injective,
          ENNReal.ofReal (gapProduct lam) * angularJacobian (angleParameters θ) *
            coordinateOrthogonalAverageNN G (symmetricCoordinates (Matrix.diagonal lam)) := by
      rw [lintegral_coordinateProduct_restrict _ _ hF]
      simp only [F, diagonalCoordinates_jointParameters, angularJacobian_jointParameters]
    _ = mass⁻¹ * (B * ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
        ENNReal.ofReal (gapProduct lam) *
          coordinateOrthogonalAverageNN G (symmetricCoordinates (Matrix.diagonal lam))) := by
      rw [← lintegral_const_mul B hg]
      congr 1
      apply lintegral_congr
      intro lam
      calc
        _ = (∫⁻ θ in angularParameterPatch lam₀ hlam₀.injective,
            ENNReal.ofReal (gapProduct lam) * angularJacobian (angleParameters θ)) *
              coordinateOrthogonalAverageNN G (symmetricCoordinates (Matrix.diagonal lam)) :=
          lintegral_mul_const (μ := volume.restrict (angularParameterPatch lam₀ hlam₀.injective))
            (f := fun θ => ENNReal.ofReal (gapProduct lam) * angularJacobian (angleParameters θ))
            _ (measurable_const.mul hang)
        _ = (ENNReal.ofReal (gapProduct lam) * B) *
            coordinateOrthogonalAverageNN G (symmetricCoordinates (Matrix.diagonal lam)) :=
          congrArg (fun x => x * coordinateOrthogonalAverageNN G
            (symmetricCoordinates (Matrix.diagonal lam)))
              (lintegral_const_mul
                (μ := volume.restrict (angularParameterPatch lam₀ hlam₀.injective))
                (f := fun θ => angularJacobian (angleParameters θ)) _ hang)
        _ = _ := by ac_rfl
    _ = _ := by
      change mass⁻¹ * (B * _) = (mass⁻¹ * B) * _
      exact (mul_assoc _ _ _).symm

end ResearchMain.WishartBlocks.Weyl
