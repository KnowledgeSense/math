import MainTheorems.DiagonalSchatten.DiagonalSpectrum
import MainTheorems.DiagonalSchatten.PhaseRemoval
import MainTheorems.DiagonalSchatten.DirectSum

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

def entryRoot (p : ℝ) (B : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℂ :=
  fun i j => ((B i j) ^ (1 / p) : ℝ)

def entryPowers (p : ℝ) (W : Matrix (Fin 2) J ℂ) : Matrix (Fin 2) J ℝ :=
  fun i j => ‖W i j‖ ^ p

def compressionFunctional (p : ℝ) (B : Matrix (Fin 2) J ℝ) : ℝ :=
  schattenPower p (entryRoot p B)

omit [Fintype D] [DecidableEq D] [Fintype J] [DecidableEq J] in
theorem entryPowers_nonnegative (p : ℝ) (W : Matrix (Fin 2) J ℂ) (i : Fin 2) (j : J) :
    0 ≤ entryPowers p W i j :=
  Real.rpow_nonneg (norm_nonneg _) _

omit [Fintype D] [DecidableEq D] [Fintype J] [DecidableEq J] in
theorem entryRoot_entryPowers {p : ℝ} (hp : 0 < p) (W : Matrix (Fin 2) J ℂ) :
    entryRoot p (entryPowers p W) = entrywiseAbs W := by
  ext i j
  change (((‖W i j‖ ^ p) ^ (1 / p) : ℝ) : ℂ) = (‖W i j‖ : ℂ)
  rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

omit [Fintype D] [DecidableEq D] in
theorem compressionFunctional_entryPowers {p : ℝ} (hp : 0 < p) (W : Matrix (Fin 2) J ℂ) :
    compressionFunctional p (entryPowers p W) = schattenPower p (entrywiseAbs W) := by
  unfold compressionFunctional
  rw [entryRoot_entryPowers hp]

omit [Fintype J] [DecidableEq J] in
theorem compression_eq_entryRoot_sum (p : ℝ) (z : Fin 2 → J → D → ℂ) :
    compression p z = entryRoot p
      (∑ d, entryPowers p (fun i j => z i j d : Matrix (Fin 2) J ℂ)) := by
  ext i j
  change (schattenNorm p (Matrix.diagonal (z i j)) : ℂ) = _
  rw [schattenNorm_diagonal]
  have hs : (∑ d, entryPowers p (fun i j => z i j d : Matrix (Fin 2) J ℂ)) i j =
      ∑ d, ‖z i j d‖ ^ p := by
    change (∑ d, (fun i j => ‖z i j d‖ ^ p : Fin 2 → J → ℝ)) i j = _
    simp only [Finset.sum_apply]
  change _ = ((((∑ d, entryPowers p (fun i j => z i j d : Matrix (Fin 2) J ℂ)) i j) ^
    (1 / p) : ℝ) : ℂ)
  rw [hs]

omit [Fintype D] [DecidableEq D] in
theorem compressionFunctional_zero {p : ℝ} (hp : 0 < p) :
    compressionFunctional p (0 : Matrix (Fin 2) J ℝ) = 0 := by
  have hzero : entryRoot p (0 : Matrix (Fin 2) J ℝ) = 0 := by
    ext i j
    change (((0 : ℝ) ^ (1 / p) : ℝ) : ℂ) = 0
    rw [Real.zero_rpow (one_div_ne_zero hp.ne'), Complex.ofReal_zero]
  rw [compressionFunctional, hzero, schattenPower_zero hp.ne']

end

end ResearchMain.DiagonalSchatten
