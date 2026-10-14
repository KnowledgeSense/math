import MainTheorems.DiagonalSchatten.TwoColumnCompression

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

theorem compressionFunctional_two_column_monotone {q : ℝ} (hq : 2 ≤ q)
    (B C : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hBC : ∀ i j, B i j ≤ C i j) : compressionFunctional q B ≤ compressionFunctional q C := by
  have hD : ∀ i j, 0 ≤ (C - B) i j := fun i j => sub_nonneg.mpr (hBC i j)
  have h := two_column_compression_upper hq B (C - B) hB hD
  have he : B + (C - B) = C := by abel
  rw [he] at h
  have hn : 0 ≤ compressionFunctional q (C - B) := schattenPower_nonneg _ _
  linarith

theorem nonnegative_two_column_power_monotone {q : ℝ} (hq : 2 ≤ q)
    (B C : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hBC : ∀ i j, B i j ≤ C i j) :
    schattenPower q (complexifyRows B) ≤ schattenPower q (complexifyRows C) := by
  have hC : ∀ i j, 0 ≤ C i j := fun i j => (hB i j).trans (hBC i j)
  have hBabs : entrywiseAbs (complexifyRows B) = complexifyRows B := by
    ext i j
    simp [entrywiseAbs, complexifyRows, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB i j)]
  have hCabs : entrywiseAbs (complexifyRows C) = complexifyRows C := by
    ext i j
    simp [entrywiseAbs, complexifyRows, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hC i j)]
  have hp : 0 < q := by linarith
  have he := compressionFunctional_two_column_monotone hq
    (entryPowers q (complexifyRows B)) (entryPowers q (complexifyRows C))
    (entryPowers_nonnegative q _) (fun i j => by
      simp only [entryPowers, complexifyRows, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hB i j), abs_of_nonneg (hC i j)]
      exact Real.rpow_le_rpow (hB i j) (hBC i j) hp.le)
  rwa [compressionFunctional_entryPowers hp, compressionFunctional_entryPowers hp, hBabs, hCabs] at he

end

end ResearchMain.DiagonalSchatten
