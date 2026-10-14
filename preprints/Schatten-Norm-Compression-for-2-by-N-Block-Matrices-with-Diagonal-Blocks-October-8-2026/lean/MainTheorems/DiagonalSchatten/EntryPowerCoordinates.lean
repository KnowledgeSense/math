import MainTheorems.DiagonalSchatten.CompressionSecondVariation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def realEntryPower (p : ℝ) (X : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => X i j ^ p

def entryPowerDirection (p : ℝ) (X Y : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => p * X i j ^ (p - 1) * Y i j

omit [Fintype J] in
theorem realEntryRoot_entryPower [Fintype J] {p : ℝ} (hp : p ≠ 0)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    realEntryRoot p (realEntryPower p X) = X := by
  ext i j
  change (X i j ^ p) ^ (1 / p) = X i j
  rw [← Real.rpow_mul (hX i j), show p * (1 / p) = 1 by field_simp [hp], Real.rpow_one]

omit [Fintype J] in
theorem entryRootDirection_entryPower [Fintype J] {p : ℝ} (hp : p ≠ 0)
    (X Y : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 < X i j) :
    entryRootDirection p (realEntryPower p X) (entryPowerDirection p X Y) = Y := by
  ext i j
  change (1 / p) * (X i j ^ p) ^ (1 / p - 1) *
    (p * X i j ^ (p - 1) * Y i j) = Y i j
  rw [← Real.rpow_mul (hX i j).le]
  calc
    _ = ((1 / p) * p) *
        (X i j ^ (p * (1 / p - 1)) * X i j ^ (p - 1)) * Y i j := by ring
    _ = Y i j := by
      rw [← Real.rpow_add (hX i j),
        show p * (1 / p - 1) + (p - 1) = 0 by field_simp [hp]; ring,
        Real.rpow_zero]
      field_simp [hp]

end

end ResearchMain.DiagonalSchatten
