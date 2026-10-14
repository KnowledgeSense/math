import MainTheorems.DiagonalSchatten.HessianSignContinuation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem signed_compressionHessian_nonneg_of_principal {p : ℝ} (hp : 1 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) (s : ℝ)
    (hps : (s • radialPrincipalMinor (compressionHessianMatrix p B)).PosSemidef)
    (E : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ s * compressionHessian p B E E := by
  let t := E 0 0 / B 0 0
  let F := E - t • B
  let v : Fin 3 → ℝ := ![F 0 1, F 1 0, F 1 1]
  have hF0 : F 0 0 = 0 := by
    dsimp [F, t]
    rw [div_mul_cancel₀ _ (hB 0 0).ne', sub_self]
  have hF : matrixFromCoordinates (principalExtension v) = F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixFromCoordinates, principalExtension, v, hF0]
  have hrad := compressionHessian_radial_zero hp B hB hdet
  have hEB : compressionHessian p B E B = 0 := by
    rw [compressionHessian_symmetric (by linarith) B hB hdet, hrad]
    rfl
  have hFF : compressionHessian p B F F = compressionHessian p B E E := by
    dsimp [F]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hrad, hEB, zero_apply,
      mul_zero, sub_zero]
  have hv := hps.dotProduct_mulVec_nonneg v
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    radialPrincipalMinor_quadratic, compressionHessianMatrix_quadratic, hF, hFF] at hv
  exact hv

theorem positive_determinant_compressionHessian_nonneg {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays)
    (E : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ compressionHessian p B E E := by
  have hps := (compressionHessian_principal_positive hp hp2 B hB).posSemidef
  simpa only [one_mul] using signed_compressionHessian_nonneg_of_principal hp B hB.1
    (positiveDeterminantArrays_rootGram (by linarith) B hB) 1 (by simpa using hps) E

theorem positive_determinant_compressionHessian_nonpos {p : ℝ} (hp : 2 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays)
    (E : Matrix (Fin 2) (Fin 2) ℝ) : compressionHessian p B E E ≤ 0 := by
  have hps := (compressionHessian_neg_principal_positive hp B hB).posSemidef
  have he := signed_compressionHessian_nonneg_of_principal (by linarith) B hB.1
    (positiveDeterminantArrays_rootGram (by linarith) B hB) (-1) (by simpa using hps) E
  simpa only [neg_one_mul, neg_nonneg] using he

theorem two_column_compressionHessian_nonneg {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : (realEntryRoot p B).det ≠ 0) : 0 ≤ compressionHessian p B E E := by
  have hp0 : 0 < p := by linarith
  rcases lt_or_gt_of_ne hdet with hn | hpdet
  · have hBS := exchangeColumns_positive B hB
    have hroot : 0 < (realEntryRoot p (exchangeColumns B)).det := by
      rw [realEntryRoot_exchangeColumns, exchangeColumns_det]
      exact neg_pos.mpr hn
    have hBdet : exchangeColumns B ∈ positiveDeterminantArrays :=
      ⟨hBS, (entryRoot_determinant_positive_iff hp0 _ hBS).mp hroot⟩
    have he := positive_determinant_compressionHessian_nonneg hp hp2
      (exchangeColumns B) hBdet (exchangeColumns E)
    rw [compressionHessian_exchangeColumns hp B E E hB] at he
    · exact he
    · rw [twoByTwo_gramDet_eq_det_sq]
      exact sq_pos_of_ne_zero hdet
  · exact positive_determinant_compressionHessian_nonneg hp hp2 B
      ⟨hB, (entryRoot_determinant_positive_iff hp0 B hB).mp hpdet⟩ E

theorem two_column_compressionHessian_nonpos {p : ℝ} (hp : 2 < p)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : (realEntryRoot p B).det ≠ 0) : compressionHessian p B E E ≤ 0 := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  rcases lt_or_gt_of_ne hdet with hn | hpdet
  · have hBS := exchangeColumns_positive B hB
    have hroot : 0 < (realEntryRoot p (exchangeColumns B)).det := by
      rw [realEntryRoot_exchangeColumns, exchangeColumns_det]
      exact neg_pos.mpr hn
    have hBdet : exchangeColumns B ∈ positiveDeterminantArrays :=
      ⟨hBS, (entryRoot_determinant_positive_iff hp0 _ hBS).mp hroot⟩
    have he := positive_determinant_compressionHessian_nonpos hp
      (exchangeColumns B) hBdet (exchangeColumns E)
    rw [compressionHessian_exchangeColumns hp1 B E E hB] at he
    · exact he
    · rw [twoByTwo_gramDet_eq_det_sq]
      exact sq_pos_of_ne_zero hdet
  · exact positive_determinant_compressionHessian_nonpos hp B
      ⟨hB, (entryRoot_determinant_positive_iff hp0 B hB).mp hpdet⟩ E

end

end ResearchMain.DiagonalSchatten
