import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CongruenceVolume
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.HaarPatch
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.RepeatedSpectrum
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal

instance orthogonalHaar_invInvariant (n : ℕ) : Measure.IsInvInvariant (orthogonalHaar n) where
  inv_eq_self := by
    let : IsProbabilityMeasure (orthogonalHaar n).inv := by
      rw [Measure.inv_def]
      infer_instance
    let : Measure.IsHaarMeasure (orthogonalHaar n).inv :=
      { toIsFiniteMeasureOnCompacts := inferInstance
        toIsMulLeftInvariant := inferInstance
        toIsOpenPosMeasure := inferInstance }
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      (orthogonalHaar n).inv (orthogonalHaar n)

theorem orthogonalCongruence_joint_continuous (n : ℕ) :
    Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (LowerIndex n → ℝ) =>
      orthogonalCongruenceLinearMap p.1 p.2) := by
  change Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (LowerIndex n → ℝ) =>
    symmetricCoordinates (p.1.val * symmetricMatrix p.2 * p.1.val.transpose))
  unfold symmetricCoordinates
  fun_prop

noncomputable def coordinateOrthogonalAverageNN {n : ℕ}
    (G : (LowerIndex n → ℝ) → ℝ≥0∞) (W : LowerIndex n → ℝ) : ℝ≥0∞ :=
  ∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
    G (orthogonalCongruenceLinearMap Q W) ∂orthogonalHaar n

theorem coordinateOrthogonalAverageNN_measurable {n : ℕ}
    {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    Measurable (coordinateOrthogonalAverageNN G) :=
  (hG.comp (orthogonalCongruence_joint_continuous n).measurable).lintegral_prod_left'

theorem coordinateOrthogonalAverageNN_lintegral {n : ℕ}
    {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ W, coordinateOrthogonalAverageNN G W) = ∫⁻ W, G W := by
  unfold coordinateOrthogonalAverageNN
  rw [← lintegral_lintegral_swap (μ := orthogonalHaar n) (ν := volume)
    (f := fun Q W => G (orthogonalCongruenceLinearMap Q W))
    (hG.comp (orthogonalCongruence_joint_continuous n).measurable).aemeasurable]
  simp_rw [orthogonalCongruence_lintegral _ hG]
  simp

theorem coordinateOrthogonalAverageNN_congruence {n : ℕ}
    (G : (LowerIndex n → ℝ) → ℝ≥0∞)
    (V : Matrix.orthogonalGroup (Fin n) ℝ) (W : LowerIndex n → ℝ) :
    coordinateOrthogonalAverageNN G (orthogonalCongruenceLinearMap V W) =
      coordinateOrthogonalAverageNN G W := by
  unfold coordinateOrthogonalAverageNN
  simp_rw [orthogonalCongruenceLinearMap_mul]
  exact lintegral_mul_right_eq_self (μ := orthogonalHaar n)
    (fun Q => G (orthogonalCongruenceLinearMap Q W)) V

theorem angularPatchNNWeight_measurable {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀) :
    Measurable (angularPatchNNWeight lam₀ hlam₀) := by
  have hc : Continuous (symmetricCoordinates (n := n)) := by
    unfold symmetricCoordinates
    fun_prop
  exact (measurable_const.indicator (angularPatch_image_measurable lam₀ hlam₀)).comp hc.measurable

theorem angularPatchNNWeight_coordinateAverage {n : ℕ} {lam₀ : Fin n → ℝ}
    (hlam₀ : StrictMono lam₀) (W : LowerIndex n → ℝ)
    (hW : Function.Injective (sortedEigenvalues n (symmetricMatrix W))) :
    coordinateOrthogonalAverageNN (fun x =>
      angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix x)) W = 1 := by
  let lam := sortedEigenvalues n (symmetricMatrix W)
  have hlam : StrictMono lam := (sortedEigenvalues_monotone _).strictMono_of_injective hW
  obtain ⟨V, hV⟩ := sortedEigenvalues_diagonalization (symmetricMatrix_isHermitian W)
  have hcoord : W = orthogonalCongruenceLinearMap V
      (symmetricCoordinates (Matrix.diagonal lam)) := by
    calc
      W = symmetricCoordinates (symmetricMatrix W) :=
        (symmetricCoordinates_symmetricMatrix W).symm
      _ = symmetricCoordinates (V.val * Matrix.diagonal lam * V.val.transpose) :=
        congrArg symmetricCoordinates hV
      _ = _ := by
        change symmetricCoordinates (V.val * Matrix.diagonal lam * V.val.transpose) =
          symmetricCoordinates (V.val * symmetricMatrix
            (symmetricCoordinates (Matrix.diagonal lam)) * V.val.transpose)
        rw [symmetricMatrix_symmetricCoordinates (Matrix.isHermitian_diagonal lam)]
  rw [hcoord, coordinateOrthogonalAverageNN_congruence]
  unfold coordinateOrthogonalAverageNN
  have hfun (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
      symmetricMatrix (orthogonalCongruenceLinearMap Q
        (symmetricCoordinates (Matrix.diagonal lam))) = orthogonalDiagonal Q lam := by
    change symmetricMatrix (symmetricCoordinates (Q.val *
      symmetricMatrix (symmetricCoordinates (Matrix.diagonal lam)) * Q.val.transpose)) = _
    rw [symmetricMatrix_symmetricCoordinates (Matrix.isHermitian_diagonal lam)]
    exact symmetricMatrix_symmetricCoordinates (orthogonalDiagonal_isHermitian Q lam)
  simp_rw [hfun]
  exact angularPatchNNWeight_orbital_integral hlam₀ hlam

theorem angularPatchNNWeight_coordinateAverage_ae {n : ℕ} {lam₀ : Fin n → ℝ}
    (hlam₀ : StrictMono lam₀) :
    ∀ᵐ W : LowerIndex n → ℝ,
      coordinateOrthogonalAverageNN (fun x =>
        angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix x)) W = 1 := by
  have hsimple : ∀ᵐ W : LowerIndex n → ℝ,
      Function.Injective (sortedEigenvalues n (symmetricMatrix W)) :=
    ae_iff.mpr (repeatedSpectrum_coordinates_volume_zero n)
  filter_upwards [hsimple] with W hW
  exact angularPatchNNWeight_coordinateAverage hlam₀ W hW

end ResearchMain.WishartBlocks.Weyl
