import MainTheorems.DiagonalSchatten.RationalSVDSpectrum
import MainTheorems.DiagonalSchatten.CompressionGradient
import MainTheorems.DiagonalSchatten.SpectralJacobian

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def realEntryPowers {J : Type*} (p : ℝ) (M : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  fun i j => M i j ^ p

theorem realEntryRoot_realEntryPowers {J : Type*} {p : ℝ} (hp : p ≠ 0)
    (M : Matrix (Fin 2) J ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    realEntryRoot p (realEntryPowers p M) = M := by
  ext i j
  change (M i j ^ p) ^ (1 / p) = M i j
  rw [← Real.rpow_mul (hM i j), mul_one_div_cancel hp, Real.rpow_one]

def rationalSVDPowers (p h t w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  realEntryPowers p (rationalSVDCore t w h)

def rationalSVDGradient (p h t w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let d := rationalSVDCore t w h
  let n := rationalSVDCore t w (h ^ (p - 1))
  fun i j => ((1 + t ^ 2) * (1 + w ^ 2)) ^ ((p - 2) / 2) * n i j / d i j ^ (p - 1)

theorem compressionGradient_matrix_product {J : Type*} [Fintype J]
    (p : ℝ) (B : Matrix (Fin 2) J ℝ) (i : Fin 2) (j : J) :
    compressionGradient p B i j =
      (realGramPowerMatrix ((p - 2) / 2) (realEntryRoot p B) * realEntryRoot p B) i j *
        B i j ^ (1 / p - 1) := by
  fin_cases i <;>
    simp [compressionGradient, realGramPowerMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem compressionGradient_rationalSVD {p h t w : ℝ} (hp : p ≠ 0)
    (hh : 0 < h) (hh1 : h < 1)
    (hM : ∀ i j, 0 < rationalSVDCore t w h i j) :
    compressionGradient p (rationalSVDPowers p h t w) = rationalSVDGradient p h t w := by
  have hroot : realEntryRoot p (rationalSVDPowers p h t w) = rationalSVDCore t w h :=
    realEntryRoot_realEntryPowers hp _ (fun i j => (hM i j).le)
  have hprod := rationalSVDCore_power_times_core ((p - 2) / 2) t w hh hh1
  rw [show 2 * ((p - 2) / 2) + 1 = p - 1 by ring] at hprod
  ext i j
  rw [compressionGradient_matrix_product, hroot, hprod]
  change (((1 + t ^ 2) * (1 + w ^ 2)) ^ ((p - 2) / 2) *
    rationalSVDCore t w (h ^ (p - 1)) i j) *
      (rationalSVDCore t w h i j ^ p) ^ (1 / p - 1) = _
  have he : p * (1 / p - 1) = -(p - 1) := by field_simp [hp]; ring
  rw [← Real.rpow_mul (hM i j).le, he, Real.rpow_neg (hM i j).le]
  rfl

theorem rationalSVDPowers_positive {p h t w : ℝ}
    (hM : ∀ i j, 0 < rationalSVDCore t w h i j) :
    ∀ i j, 0 < rationalSVDPowers p h t w i j :=
  fun i j => Real.rpow_pos_of_pos (hM i j) _

theorem fderiv_compressionFunctional_rationalSVD {p h t w : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1)
    (hM : ∀ i j, 0 < rationalSVDCore t w h i j)
    (E : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (compressionFunctional p) (rationalSVDPowers p h t w) E =
      ∑ j, (rationalSVDGradient p h t w 0 j * E 0 j +
        rationalSVDGradient p h t w 1 j * E 1 j) := by
  have hroot : realEntryRoot p (rationalSVDPowers p h t w) = rationalSVDCore t w h :=
    realEntryRoot_realEntryPowers hp.ne' _ (fun i j => (hM i j).le)
  rw [fderiv_compressionFunctional hp _ E (rationalSVDPowers_positive hM)]
  · rw [compressionGradient_rationalSVD hp.ne' hh hh1 hM]
  · rw [hroot, rationalSVDCore_gramDet]
    positivity

end

end ResearchMain.DiagonalSchatten
