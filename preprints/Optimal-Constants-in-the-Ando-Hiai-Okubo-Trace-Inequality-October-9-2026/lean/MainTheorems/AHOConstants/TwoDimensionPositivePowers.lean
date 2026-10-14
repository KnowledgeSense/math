import MainTheorems.AHOConstants.BinarySpectrumPowers
import MainTheorems.AHOConstants.ConjugationPowers
import MainTheorems.DiagonalSchatten.TwoSpectrumPower

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

theorem hermitianTwo_diagonal_nonnegative {a b c : ℝ}
    (hB : (hermitianTwo a b (c : ℂ)).PosSemidef) : 0 ≤ a ∧ 0 ≤ b := by
  constructor
  · simpa [hermitianTwo] using (RCLike.nonneg_iff.mp (hB.diag_nonneg (i := 0))).1
  · simpa [hermitianTwo] using (RCLike.nonneg_iff.mp (hB.diag_nonneg (i := 1))).1

theorem hermitianTwo_nonnegative_power_entries {a b c r : ℝ} (hc : 0 ≤ c)
    (hB : (hermitianTwo a b (c : ℂ)).PosSemidef) (hr : 0 ≤ r)
    (i j : Fin 2) :
    0 ≤ (spectralPower (hermitianTwo a b (c : ℂ)) r i j).re ∧
      (spectralPower (hermitianTwo a b (c : ℂ)) r i j).im = 0 := by
  obtain ⟨ha, hb⟩ := hermitianTwo_diagonal_nonnegative hB
  have hdet := (RCLike.nonneg_iff.mp hB.det_nonneg).1
  rw [hermitianTwo_det] at hdet
  have hprod : ‖(c : ℂ)‖ ^ 2 ≤ a * b := by
    change 0 ≤ a * b - ‖(c : ℂ)‖ ^ 2 at hdet
    linarith
  let l := twoEigenvalueMinus a b (c : ℂ)
  let u := twoEigenvaluePlus a b (c : ℂ)
  have hl : 0 ≤ l := twoEigenvalueMinus_nonneg _ ha hb hprod
  have hlu : l ≤ u := by
    have hg := Real.sqrt_nonneg ((a - b) ^ 2 + 4 * ‖(c : ℂ)‖ ^ 2)
    dsimp [l, u, twoEigenvalueMinus, twoEigenvaluePlus, twoEigenvalueGap]
    linarith
  by_cases hgap : l = u
  · have hg : twoEigenvalueGap a b (c : ℂ) = 0 := by
      dsimp [l, u, twoEigenvalueMinus, twoEigenvaluePlus] at hgap
      linarith
    have hs : (a - b) ^ 2 + 4 * c ^ 2 = 0 := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ (a - b) ^ 2 + 4 * ‖(c : ℂ)‖ ^ 2)
      change twoEigenvalueGap a b (c : ℂ) ^ 2 = _ at hs
      rw [hg] at hs
      simpa only [Complex.norm_real, Real.norm_of_nonneg hc,
        zero_pow (by decide : 2 ≠ 0)] using hs.symm
    have hab : b = a := by nlinarith [sq_nonneg c]
    have hc₀ : c = 0 := by nlinarith [sq_nonneg (a - b)]
    have he : hermitianTwo a b (c : ℂ) = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp [hermitianTwo, hab, hc₀]
    rw [he, spectralPower_scalar_identity ha]
    fin_cases i <;> fin_cases j <;>
      simp [Real.rpow_nonneg ha]
  · have he := binarySpectrum_spectralPower hB hgap
      (fun x hx => hermitianTwo_real_spectrum a b (c : ℂ) hx) r
    have hp : 0 ≤ (u ^ r - l ^ r) / (u - l) :=
      div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hl hlu hr)) (sub_nonneg.mpr hlu)
    have hpower := spectralPower_positiveSemidefinite (hermitianTwo a b (c : ℂ)) r
    fin_cases i <;> fin_cases j
    · exact RCLike.nonneg_iff.mp (hpower.diag_nonneg (i := 0))
    · rw [he]
      simpa [hermitianTwo, Matrix.one_apply, RCLike.real_smul_eq_coe_mul,
        ← Complex.ofReal_sub, ← Complex.ofReal_div] using
        (show 0 ≤ ((u ^ r - l ^ r) / (u - l)) * c ∧ (0 : ℝ) = 0 from
          ⟨mul_nonneg hp hc, rfl⟩)
    · rw [he]
      simpa [hermitianTwo, Matrix.one_apply, RCLike.real_smul_eq_coe_mul,
        ← Complex.ofReal_sub, ← Complex.ofReal_div] using
        (show 0 ≤ ((u ^ r - l ^ r) / (u - l)) * c ∧ (0 : ℝ) = 0 from
          ⟨mul_nonneg hp hc, rfl⟩)
    · exact RCLike.nonneg_iff.mp (hpower.diag_nonneg (i := 1))

end ResearchMain.AHOConstants
