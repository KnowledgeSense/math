import MainTheorems.DiagonalSchatten.TwoRowSpectrum
import MainTheorems.AHOConstants.BinarySpectrumPowers

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem hermitianTwo_isHermitian (a b : ℝ) (z : ℂ) : (hermitianTwo a b z).IsHermitian := by
  change (hermitianTwo a b z).conjTranspose = hermitianTwo a b z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianTwo, Matrix.conjTranspose_apply]

theorem hermitianTwo_real_spectrum (a b : ℝ) (z : ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ (hermitianTwo a b z)) :
    x = twoEigenvalueMinus a b z ∨ x = twoEigenvaluePlus a b z := by
  let h := hermitianTwo_isHermitian a b z
  rw [h.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have hi : ((h.eigenvalues i : ℝ) : ℂ) ∈ (hermitianTwo a b z).charpoly.roots := by
    rw [h.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [hermitianTwo_roots] at hi
  have he : h.eigenvalues i = twoEigenvaluePlus a b z ∨
      h.eigenvalues i = twoEigenvalueMinus a b z := by
    simpa only [Multiset.mem_add, Multiset.mem_singleton, Complex.ofReal_inj] using hi
  exact he.symm

theorem rowGram_spectralPower {J : Type*} [Fintype J]
    (W : Matrix (Fin 2) J ℂ) (r : ℝ)
    (hgap : 0 < twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross W)) :
    ResearchMain.AHOConstants.spectralPower (W * W.conjTranspose) r =
      twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W) ^ r •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W) ^ r -
          twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W) ^ r) /
        (twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W) -
          twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W))) •
        (W * W.conjTranspose -
          twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W) •
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply ResearchMain.AHOConstants.binarySpectrum_spectralPower
    (Matrix.posSemidef_self_mul_conjTranspose W)
  · unfold twoEigenvalueMinus twoEigenvaluePlus
    linarith
  · intro x hx
    rw [twoRow_gram] at hx
    exact hermitianTwo_real_spectrum _ _ _ hx

theorem rowGram_posDef {J : Type*} [Fintype J] (W : Matrix (Fin 2) J ℂ)
    (hdet : 0 < rowMass W 0 * rowMass W 1 - ‖rowCross W‖ ^ 2) :
    (W * W.conjTranspose).PosDef := by
  apply (Matrix.posSemidef_self_mul_conjTranspose W).posDef_iff_det_ne_zero.mpr
  rw [twoRow_gram, hermitianTwo_det]
  exact_mod_cast hdet.ne'

theorem rowGram_power_inverse {J : Type*} [Fintype J] (W : Matrix (Fin 2) J ℂ)
    (hdet : 0 < rowMass W 0 * rowMass W 1 - ‖rowCross W‖ ^ 2)
    {r : ℝ} (hr : r ≠ 0) :
    ResearchMain.AHOConstants.spectralPower
      (ResearchMain.AHOConstants.spectralPower (W * W.conjTranspose) r) (1 / r) =
        W * W.conjTranspose := by
  change CFC.rpow (CFC.rpow (W * W.conjTranspose) r) (1 / r) = _
  simpa only [one_div, ← CFC.rpow_eq_pow] using CFC.rpow_rpow_inv (W * W.conjTranspose) r hr
    (rowGram_posDef W hdet).isStrictlyPositive

theorem rowGram_power_offDiagonal {J : Type*} [Fintype J]
    (W : Matrix (Fin 2) J ℂ) (r : ℝ)
    (hgap : 0 < twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross W)) :
    ResearchMain.AHOConstants.spectralPower (W * W.conjTranspose) r 0 1 =
      ((twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W) ^ r -
          twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W) ^ r) /
        (twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W) -
          twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W))) • rowCross W := by
  rw [rowGram_spectralPower W r hgap]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    twoRow_gram, hermitianTwo]

end

end ResearchMain.DiagonalSchatten
