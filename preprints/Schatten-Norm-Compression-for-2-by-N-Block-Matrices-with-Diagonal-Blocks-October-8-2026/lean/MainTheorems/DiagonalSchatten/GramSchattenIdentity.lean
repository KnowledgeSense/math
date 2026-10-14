import MainTheorems.DiagonalSchatten.TwoRowSpectrum

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

theorem hermitianTwo_row_data (a b : ℝ) (c : ℂ) :
    rowMass (hermitianTwo a b c) 0 = a ^ 2 + ‖c‖ ^ 2 ∧
      rowMass (hermitianTwo a b c) 1 = b ^ 2 + ‖c‖ ^ 2 ∧
      rowCross (hermitianTwo a b c) = (a + b) * c := by
  constructor
  · simp [rowMass, hermitianTwo, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  constructor
  · simp [rowMass, hermitianTwo, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  · simp [rowCross, hermitianTwo, Fin.sum_univ_two]
    ring

theorem hermitianTwo_squared_eigenvalues {a b : ℝ} (c : ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoEigenvaluePlus (a ^ 2 + ‖c‖ ^ 2) (b ^ 2 + ‖c‖ ^ 2) ((a + b) * c) =
        twoEigenvaluePlus a b c ^ 2 ∧
      twoEigenvalueMinus (a ^ 2 + ‖c‖ ^ 2) (b ^ 2 + ‖c‖ ^ 2) ((a + b) * c) =
        twoEigenvalueMinus a b c ^ 2 := by
  have hn : ‖((a + b : ℝ) : ℂ) * c‖ = (a + b) * ‖c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (add_nonneg ha hb)]
  have hg : twoEigenvalueGap (a ^ 2 + ‖c‖ ^ 2) (b ^ 2 + ‖c‖ ^ 2) ((a + b) * c) =
      (a + b) * twoEigenvalueGap a b c := by
    unfold twoEigenvalueGap
    rw [← Complex.ofReal_add, hn, show (a ^ 2 + ‖c‖ ^ 2 - (b ^ 2 + ‖c‖ ^ 2)) ^ 2 +
        4 * ((a + b) * ‖c‖) ^ 2 = (a + b) ^ 2 * ((a - b) ^ 2 + 4 * ‖c‖ ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (add_nonneg ha hb)]
  have hsq : twoEigenvalueGap a b c ^ 2 = (a - b) ^ 2 + 4 * ‖c‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  constructor
  · unfold twoEigenvaluePlus
    rw [hg]
    nlinarith [hsq]
  · unfold twoEigenvalueMinus
    rw [hg]
    nlinarith [hsq]

theorem hermitianTwo_schattenPower {q a b : ℝ} (hq : 0 < q) (c : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ‖c‖ ^ 2 ≤ a * b) :
    schattenPower q (hermitianTwo a b c) =
      twoEigenvaluePlus a b c ^ q + twoEigenvalueMinus a b c ^ q := by
  obtain ⟨h0, h1, h2⟩ := hermitianTwo_row_data a b c
  obtain ⟨hl, hs⟩ := hermitianTwo_squared_eigenvalues c ha hb
  rw [schattenPower_twoRow hq, h0, h1, h2, hl, hs,
    ← Real.rpow_natCast_mul (twoEigenvaluePlus_nonneg c ha hb) 2 (q / 2),
    ← Real.rpow_natCast_mul (twoEigenvalueMinus_nonneg c ha hb hc) 2 (q / 2)]
  congr 1 <;> congr 1 <;> ring

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem schattenPower_twoRow_gram {q : ℝ} (hq : 0 < q) (W : Matrix (Fin 2) J ℂ) :
    schattenPower q (W * W.conjTranspose) = schattenPower (2 * q) W := by
  rw [twoRow_gram, hermitianTwo_schattenPower hq (rowCross W)
    (rowMass_nonneg W 0) (rowMass_nonneg W 1) (rowCross_sq_le W),
    schattenPower_twoRow (by positivity : 0 < 2 * q)]
  congr 1 <;> congr 1 <;> ring

end

end ResearchMain.DiagonalSchatten
