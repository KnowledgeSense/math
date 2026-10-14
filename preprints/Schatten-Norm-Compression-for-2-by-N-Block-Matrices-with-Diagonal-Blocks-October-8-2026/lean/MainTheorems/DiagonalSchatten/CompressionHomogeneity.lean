import MainTheorems.DiagonalSchatten.CompressionRegularity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem gramFirst_smul (X : Matrix (Fin 2) J ℝ) (t : ℝ) :
    gramFirst (t • X) = t ^ 2 * gramFirst X := by
  simp only [gramFirst, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem gramSecond_smul (X : Matrix (Fin 2) J ℝ) (t : ℝ) :
    gramSecond (t • X) = t ^ 2 * gramSecond X := by
  simp only [gramSecond, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem gramCross_smul (X : Matrix (Fin 2) J ℝ) (t : ℝ) :
    gramCross (t • X) = t ^ 2 * gramCross X := by
  simp only [gramCross, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realGram_smul (X : Matrix (Fin 2) J ℝ) (t : ℝ) :
    realGramPlus (t • X) = t ^ 2 * realGramPlus X ∧
      realGramMinus (t • X) = t ^ 2 * realGramMinus X := by
  have hgap : (gramFirst (t • X) - gramSecond (t • X)) ^ 2 +
      4 * gramCross (t • X) ^ 2 =
      (t ^ 2) ^ 2 * ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2) := by
    rw [gramFirst_smul, gramSecond_smul, gramCross_smul]
    ring
  have hs : Real.sqrt ((gramFirst (t • X) - gramSecond (t • X)) ^ 2 +
      4 * gramCross (t • X) ^ 2) =
      t ^ 2 * Real.sqrt ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2) := by
    rw [hgap, Real.sqrt_mul (sq_nonneg (t ^ 2)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg t)]
  constructor <;> simp only [realGramPlus, realGramMinus] <;>
    rw [hs, gramFirst_smul, gramSecond_smul] <;> ring

variable [DecidableEq J]

theorem schattenPower_complexify_smul {p : ℝ} (hp : 0 < p)
    (X : Matrix (Fin 2) J ℝ) (t : ℝ) :
    schattenPower p (complexifyRows (t • X)) =
      (t ^ 2) ^ (p / 2) * schattenPower p (complexifyRows X) := by
  rw [schattenPower_complexify hp, schattenPower_complexify hp,
    (realGram_smul X t).1, (realGram_smul X t).2]
  have hn := realGram_nonneg X
  rw [Real.mul_rpow (sq_nonneg t) hn.1, Real.mul_rpow (sq_nonneg t) hn.2]
  ring

omit [Fintype J] [DecidableEq J] in
theorem realEntryRoot_smul {p t : ℝ} (ht : 0 ≤ t)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    realEntryRoot p (t • B) = t ^ (1 / p) • realEntryRoot p B := by
  ext i j
  change (t * B i j) ^ (1 / p) = t ^ (1 / p) * B i j ^ (1 / p)
  exact Real.mul_rpow ht (hB i j)

theorem compressionFunctional_homogeneous {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    compressionFunctional p (t • B) = t * compressionFunctional p B := by
  rw [compressionFunctional_eq_realEntryRoot, realEntryRoot_smul ht B hB,
    schattenPower_complexify_smul hp, ← compressionFunctional_eq_realEntryRoot]
  have he : ((t ^ (1 / p)) ^ 2) ^ (p / 2) = t := by
    rw [← Real.rpow_natCast_mul (Real.rpow_nonneg ht _) 2,
      ← Real.rpow_mul ht]
    norm_num only [Nat.cast_ofNat]
    have hx : (1 / p) * ((2 : ℝ) * (p / 2)) = 1 := by
      field_simp [hp.ne']
    rw [hx, Real.rpow_one]
  rw [he]

end

end ResearchMain.DiagonalSchatten
