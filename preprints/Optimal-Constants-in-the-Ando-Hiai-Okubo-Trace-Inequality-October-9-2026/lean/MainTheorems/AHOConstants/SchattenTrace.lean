import MainTheorems.AHOConstants.PolarDecomposition
import MainTheorems.DiagonalSchatten.GramSpectrum

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_spectralPower {A : Matrix I I ℂ} (hA : A.PosSemidef) (p : ℝ) :
    Matrix.trace (spectralPower A p) = ∑ i, ((hA.isHermitian.eigenvalues i ^ p : ℝ) : ℂ) := by
  change Matrix.trace (A ^ p) = _
  rw [CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.cfc_eq,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

theorem trace_spectralPower_real {A : Matrix I I ℂ} (hA : A.PosSemidef) (p : ℝ) :
    (Matrix.trace (spectralPower A p)).re = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  rw [trace_spectralPower hA p]
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem polarAbsolute_power {X : Matrix I I ℂ} (hX : IsUnit X) (p : ℝ) :
    spectralPower (polarAbsolute X) p = spectralPower (star X * X) (p / 2) := by
  unfold polarAbsolute spectralPower
  change ((star X * X) ^ (1 / 2 : ℝ)) ^ p = (star X * X) ^ (p / 2)
  rw [CFC.rpow_rpow (star X * X) (1 / 2) p (by norm_num) (gram_posDef hX).isStrictlyPositive]
  congr 1
  ring

theorem schattenPower_eq_absolute_trace {X : Matrix I I ℂ} (hX : IsUnit X) (p : ℝ) :
    schattenPower p X = (Matrix.trace (spectralPower (polarAbsolute X) p)).re := by
  let G : Matrix I I ℂ := X.conjTranspose * X
  have hG : G.PosDef := by
    simpa only [Matrix.star_eq_conjTranspose] using gram_posDef hX
  rw [schattenPower_eq_gram_roots, rootPowerSum,
    hG.isHermitian.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_def]
  change (∑ i, (Real.sqrt (hG.isHermitian.eigenvalues i)) ^ p) = _
  rw [polarAbsolute_power hX p]
  change (∑ i, (Real.sqrt (hG.isHermitian.eigenvalues i)) ^ p) =
    (Matrix.trace (spectralPower G (p / 2))).re
  rw [trace_spectralPower_real hG.posSemidef]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hG.eigenvalues_pos i).le]
  congr 1
  ring

end ResearchMain.AHOConstants
