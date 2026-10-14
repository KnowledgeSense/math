import MainTheorems.WishartBlocks.SpectralLaw.Weyl.InvariantDensity

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal

noncomputable def isotropicSpectralNNConstant (n : ℕ) (α : ℝ) : ℝ≥0∞ :=
  angularWeylConstant (referenceSpectrum n) (referenceSpectrum_strictMono n).injective *
    ENNReal.ofReal (wishartDensityCoefficient n α)

theorem eigenvalueWeight_eq_zero_of_not_strictMono {n : ℕ} (α : ℝ)
    {lam : Fin n → ℝ} (hlam : ¬ StrictMono lam) : eigenvalueWeight α lam = 0 := by
  have hnot : ¬ OrderedPositive lam := fun h => hlam h.2
  simp only [eigenvalueWeight, chamberWeight, hnot, ite_false]

theorem isotropicEigenvalueLaw_lintegral_weight {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ lam, f lam ∂isotropicEigenvalueLaw n α) =
      isotropicSpectralNNConstant n α * ∫⁻ lam, ENNReal.ofReal (eigenvalueWeight α lam) * f lam := by
  let G : (LowerIndex n → ℝ) → ℝ≥0∞ := fun W =>
    wishartCoordinateDensity α W * f (sortedEigenvalues n (symmetricMatrix W))
  have hmatrix : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      f (sortedEigenvalues n W)) := hf.comp (measurable_sortedEigenvalues n)
  have hG : Measurable G := (measurable_wishartCoordinateDensity n α).mul
    (hmatrix.comp (symmetricMatrix_continuous n).measurable)
  have hfg : Measurable (fun lam : Fin n → ℝ =>
      ENNReal.ofReal (eigenvalueWeight α lam) * f lam) :=
    (measurable_eigenvalueWeight α).ennreal_ofReal.mul hf
  have hrestrict : (∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
      ENNReal.ofReal (eigenvalueWeight α lam) * f lam) =
        ∫⁻ lam, ENNReal.ofReal (eigenvalueWeight α lam) * f lam := by
    rw [← lintegral_indicator (isOpen_strictMono_coordinates n).measurableSet]
    apply lintegral_congr
    intro lam
    by_cases hlam : StrictMono lam
    · simp only [indicator_apply, mem_ofPred_eq, hlam, ite_true]
    · simp only [indicator_apply, mem_ofPred_eq, hlam, ite_false,
        eigenvalueWeight_eq_zero_of_not_strictMono α hlam, ENNReal.ofReal_zero, zero_mul]
  calc
    _ = ∫⁻ W, G W := by
      rw [isotropicEigenvalueLaw, lintegral_map hf (measurable_sortedEigenvalues n),
        ← bartlettLaw_isotropic_symmetric_density hα,
        lintegral_map hmatrix (symmetricMatrix_continuous n).measurable]
      simpa only [G, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul volume
          (g := fun W => f (sortedEigenvalues n (symmetricMatrix W)))
          (measurable_wishartCoordinateDensity n α)
          (hmatrix.comp (symmetricMatrix_continuous n).measurable))
    _ = angularWeylConstant (referenceSpectrum n) (referenceSpectrum_strictMono n).injective *
        ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
          ENNReal.ofReal (gapProduct lam) * coordinateOrthogonalAverageNN G
            (symmetricCoordinates (Matrix.diagonal lam)) :=
      weyl_lintegral (referenceSpectrum_strictMono n) hG
    _ = angularWeylConstant (referenceSpectrum n) (referenceSpectrum_strictMono n).injective *
        ∫⁻ lam in {lam : Fin n → ℝ | StrictMono lam},
          ENNReal.ofReal (wishartDensityCoefficient n α) *
            (ENNReal.ofReal (eigenvalueWeight α lam) * f lam) := by
      congr 1
      apply setLIntegral_congr_fun (isOpen_strictMono_coordinates n).measurableSet
      intro lam hlam
      change ENNReal.ofReal (gapProduct lam) * coordinateOrthogonalAverageNN G
          (symmetricCoordinates (Matrix.diagonal lam)) =
        ENNReal.ofReal (wishartDensityCoefficient n α) *
          (ENNReal.ofReal (eigenvalueWeight α lam) * f lam)
      rw [show coordinateOrthogonalAverageNN G (symmetricCoordinates (Matrix.diagonal lam)) =
          wishartCoordinateDensity α (symmetricCoordinates (Matrix.diagonal lam)) * f lam from
            coordinateOrthogonalAverageNN_densitySpectrum α f hlam,
        ← mul_assoc, wishartCoordinateDensity_diagonal_gap hα hlam, mul_assoc]
    _ = _ := by
      rw [lintegral_const_mul _ hfg, hrestrict]
      exact (mul_assoc _ _ _).symm

end ResearchMain.WishartBlocks.Weyl
