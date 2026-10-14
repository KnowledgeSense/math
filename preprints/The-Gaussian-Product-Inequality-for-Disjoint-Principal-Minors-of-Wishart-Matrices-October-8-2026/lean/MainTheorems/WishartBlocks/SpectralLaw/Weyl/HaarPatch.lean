import MainTheorems.WishartBlocks.SpectralLaw.Weyl.AnglePatch
import MainTheorems.WishartBlocks.SpectralLaw.OrthogonalHaar
import Mathlib.MeasureTheory.Measure.OpenPos

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped Matrix.Norms.Operator ENNReal

def angularOrbitPatch {n : ℕ} (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀)
    (lam : Fin n → ℝ) : Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
  {Q | ∃ z : LowerIndex n → ℝ,
    z ∈ (exponentialSpectralChart lam₀ hlam₀).source ∧ diagonalCoordinates z = 0 ∧
      orthogonalDiagonal Q lam = orthogonalDiagonal (exponentialOrthogonal z) lam}

theorem angularOrbitPatch_eq {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) {lam : Fin n → ℝ} (hlam : Function.Injective lam) :
    angularOrbitPatch lam₀ hlam₀ lam = angularOrbitPatch lam₀ hlam₀ lam₀ := by
  ext Q
  constructor
  · rintro ⟨z, hz, hd, heq⟩
    exact ⟨z, hz, hd, orthogonalDiagonal_eq_transfer _ _ hlam lam₀ heq⟩
  · rintro ⟨z, hz, hd, heq⟩
    exact ⟨z, hz, hd, orthogonalDiagonal_eq_transfer _ _ hlam₀ lam heq⟩

theorem angularOrbitPatch_eq_preimage {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    angularOrbitPatch lam₀ hlam₀ lam =
      (fun Q => symmetricCoordinates (orthogonalDiagonal Q lam)) ⁻¹'
        (jointExponentialCoordinates '' angularPatchDomain lam₀ hlam₀) := by
  ext Q
  constructor
  · rintro ⟨z, hz, hd, heq⟩
    refine ⟨spectralParameters lam z, ?_, ?_⟩
    · exact ⟨by simpa only [diagonalCoordinates_spectralParameters] using hlam,
        by simpa only [angleCoordinates_spectralParameters, angleCoordinates_eq_self hd] using hz⟩
    · change symmetricCoordinates (orthogonalDiagonal
        (exponentialOrthogonal (spectralParameters lam z))
        (diagonalCoordinates (spectralParameters lam z))) = _
      have hQ : exponentialOrthogonal (spectralParameters lam z) = exponentialOrthogonal z := by
        apply Subtype.ext
        change NormedSpace.exp (skewMatrix (spectralParameters lam z)) =
          NormedSpace.exp (skewMatrix z)
        rw [skewMatrix_spectralParameters]
      rw [hQ, diagonalCoordinates_spectralParameters, ← heq]
  · rintro ⟨z, hz, heq⟩
    have hm : orthogonalDiagonal (exponentialOrthogonal z) (diagonalCoordinates z) =
        orthogonalDiagonal Q lam := by
      have h := congrArg symmetricMatrix heq
      simpa only [jointExponentialCoordinates,
        symmetricMatrix_symmetricCoordinates (orthogonalDiagonal_isHermitian _ _)] using h
    have hd : diagonalCoordinates z = lam :=
      ((ordered_orthogonalDiagonal_eq_iff _ _ hz.1 hlam).mp hm).1
    refine ⟨angleCoordinates z, hz.2, diagonalCoordinates_angleCoordinates z, ?_⟩
    rw [exponentialOrthogonal_angleCoordinates]
    simpa only [hd] using hm.symm

theorem angularOrbitPatch_measurable {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    MeasurableSet (angularOrbitPatch lam₀ hlam₀ lam) := by
  rw [angularOrbitPatch_eq_preimage lam₀ hlam₀ hlam]
  have hcont : Continuous (fun Q : Matrix.orthogonalGroup (Fin n) ℝ =>
      symmetricCoordinates (orthogonalDiagonal Q lam)) := by
    unfold symmetricCoordinates orthogonalDiagonal
    fun_prop
  exact (angularPatch_image_measurable lam₀ hlam₀).preimage hcont.measurable

theorem angularOrbitPatch_haar_pos {n : ℕ} {lam₀ : Fin n → ℝ} (hlam₀ : StrictMono lam₀) :
    0 < orthogonalHaar n (angularOrbitPatch lam₀ hlam₀.injective lam₀) := by
  let chart := exponentialSpectralChart lam₀ hlam₀.injective
  let source : Set (LowerIndex n → ℝ) :=
    chart.source ∩ {z | StrictMono (lam₀ + diagonalCoordinates z)}
  have hsource : IsOpen source := by
    have hd : Continuous (fun z : LowerIndex n → ℝ => lam₀ + diagonalCoordinates z) := by
      exact continuous_const.add (continuous_pi fun i => continuous_apply _)
    exact chart.open_source.inter ((isOpen_strictMono_coordinates n).preimage hd)
  have hzero : (0 : LowerIndex n → ℝ) ∈ source := by
    refine ⟨exponentialSpectralChart_zero_mem_source _ _, ?_⟩
    change StrictMono (lam₀ + diagonalCoordinates (0 : LowerIndex n → ℝ))
    have hd0 : diagonalCoordinates (0 : LowerIndex n → ℝ) = 0 := by
      funext i
      rfl
    simpa only [hd0, add_zero] using hlam₀
  have himage : IsOpen (chart '' source) :=
    chart.isOpen_image_of_subset_source hsource inter_subset_left
  let B : Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
    (fun Q => symmetricCoordinates (orthogonalDiagonal Q lam₀)) ⁻¹' (chart '' source)
  have hB : IsOpen B := by
    apply himage.preimage
    unfold symmetricCoordinates orthogonalDiagonal
    fun_prop
  have hone : (1 : Matrix.orthogonalGroup (Fin n) ℝ) ∈ B := by
    refine ⟨0, hzero, ?_⟩
    simp [chart, orthogonalDiagonal, exponentialSpectralCoordinates_zero]
  have hsub : B ⊆ angularOrbitPatch lam₀ hlam₀.injective lam₀ := by
    intro Q hQ
    obtain ⟨z, hz, heq⟩ := hQ
    have hm : orthogonalDiagonal (exponentialOrthogonal z)
        (lam₀ + diagonalCoordinates z) = orthogonalDiagonal Q lam₀ := by
      have heq' : exponentialSpectralCoordinates lam₀ z =
          symmetricCoordinates (orthogonalDiagonal Q lam₀) := by
        simpa only [chart, exponentialSpectralChart_apply] using heq
      rw [exponentialSpectralCoordinates, exponentialSpectralMatrix_eq_congruence] at heq'
      have hcoords : symmetricCoordinates (orthogonalDiagonal (exponentialOrthogonal z)
          (lam₀ + diagonalCoordinates z)) = symmetricCoordinates (orthogonalDiagonal Q lam₀) :=
        heq'
      have h := congrArg symmetricMatrix hcoords
      simpa only [
        symmetricMatrix_symmetricCoordinates (orthogonalDiagonal_isHermitian _ _)] using h
    have hd : diagonalCoordinates z = 0 := by
      have h := ((ordered_orthogonalDiagonal_eq_iff _ _ hz.2 hlam₀).mp hm).1
      funext i
      have hi := congrFun h i
      simp only [Pi.add_apply] at hi
      change diagonalCoordinates z i = 0
      linarith
    refine ⟨z, hz.1, hd, ?_⟩
    simpa only [hd, add_zero] using hm.symm
  exact (hB.measure_pos (orthogonalHaar n) ⟨1, hone⟩).trans_le (measure_mono hsub)

noncomputable def angularPatchHaarMass {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀) : ℝ :=
  (orthogonalHaar n (angularOrbitPatch lam₀ hlam₀ lam₀)).toReal

theorem angularPatchHaarMass_pos {n : ℕ} {lam₀ : Fin n → ℝ} (hlam₀ : StrictMono lam₀) :
    0 < angularPatchHaarMass lam₀ hlam₀.injective :=
  ENNReal.toReal_pos (ne_of_gt (angularOrbitPatch_haar_pos hlam₀))
    (measure_ne_top _ _)

noncomputable def angularPatchNNWeight {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  (jointExponentialCoordinates '' angularPatchDomain lam₀ hlam₀).indicator
    (fun _ => (orthogonalHaar n (angularOrbitPatch lam₀ hlam₀ lam₀))⁻¹)
    (symmetricCoordinates W)

theorem angularPatchNNWeight_orbital_integral {n : ℕ} {lam₀ lam : Fin n → ℝ}
    (hlam₀ : StrictMono lam₀) (hlam : StrictMono lam) :
    (∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      angularPatchNNWeight lam₀ hlam₀.injective (orthogonalDiagonal Q lam)
        ∂orthogonalHaar n) = 1 := by
  have hfun : (fun Q : Matrix.orthogonalGroup (Fin n) ℝ =>
      angularPatchNNWeight lam₀ hlam₀.injective (orthogonalDiagonal Q lam)) =
      (angularOrbitPatch lam₀ hlam₀.injective lam).indicator
        (fun _ => (orthogonalHaar n (angularOrbitPatch lam₀ hlam₀.injective lam₀))⁻¹) := by
    funext Q
    have hmem : Q ∈ angularOrbitPatch lam₀ hlam₀.injective lam ↔
        symmetricCoordinates (orthogonalDiagonal Q lam) ∈
          jointExponentialCoordinates '' angularPatchDomain lam₀ hlam₀.injective := by
      rw [angularOrbitPatch_eq_preimage lam₀ hlam₀.injective hlam]
      rfl
    by_cases hQ : Q ∈ angularOrbitPatch lam₀ hlam₀.injective lam
    · have hW := hmem.mp hQ
      simp only [angularPatchNNWeight, Set.indicator_of_mem hW, Set.indicator_of_mem hQ]
    · have hW : symmetricCoordinates (orthogonalDiagonal Q lam) ∉
          jointExponentialCoordinates '' angularPatchDomain lam₀ hlam₀.injective :=
        fun h => hQ (hmem.mpr h)
      simp only [angularPatchNNWeight, Set.indicator_of_notMem hW, Set.indicator_of_notMem hQ]
  rw [hfun, lintegral_indicator_const
    (angularOrbitPatch_measurable lam₀ hlam₀.injective hlam),
    angularOrbitPatch_eq lam₀ hlam₀.injective hlam.injective]
  exact ENNReal.inv_mul_cancel (ne_of_gt (angularOrbitPatch_haar_pos hlam₀))
    (measure_ne_top _ _)

end ResearchMain.WishartBlocks.Weyl
