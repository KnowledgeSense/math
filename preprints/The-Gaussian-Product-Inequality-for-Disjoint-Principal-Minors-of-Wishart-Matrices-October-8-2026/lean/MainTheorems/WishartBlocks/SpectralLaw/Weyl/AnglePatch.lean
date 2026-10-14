import MainTheorems.WishartBlocks.SpectralLaw.Weyl.OrbitGeometry
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.LocalChange
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace ResearchMain.WishartBlocks.Weyl

open Set
open scoped Matrix.Norms.Operator

noncomputable def angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) : LowerIndex n → ℝ :=
  spectralParameters 0 z

noncomputable def angleContinuousLinearMap (n : ℕ) :
    (LowerIndex n → ℝ) →L[ℝ] (LowerIndex n → ℝ) :=
  ({ toFun := angleCoordinates
     map_add' := by
       intro z w
       funext e
       simp only [angleCoordinates, spectralParameters, Pi.zero_apply, Pi.add_apply]
       split_ifs <;> simp
     map_smul' := by
       intro c z
       funext e
       simp only [angleCoordinates, spectralParameters, Pi.zero_apply, Pi.smul_apply]
       split_ifs <;> simp } :
    (LowerIndex n → ℝ) →ₗ[ℝ] (LowerIndex n → ℝ)).toContinuousLinearMap

@[simp] theorem diagonalCoordinates_angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    diagonalCoordinates (angleCoordinates z) = 0 :=
  diagonalCoordinates_spectralParameters _ _

@[simp] theorem skewMatrix_angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    skewMatrix (angleCoordinates z) = skewMatrix z :=
  skewMatrix_spectralParameters _ _

theorem spectralParameters_coordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    spectralParameters (diagonalCoordinates z) (angleCoordinates z) = z := by
  funext e
  by_cases he : e.val.1 = e.val.2
  · have hindex : (⟨toLex (e.val.2, e.val.2), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext he.symm rfl)
    simp [spectralParameters, diagonalCoordinates, he, hindex]
  · simp [spectralParameters, angleCoordinates, he]

theorem angleCoordinates_eq_self {n : ℕ} {z : LowerIndex n → ℝ}
    (hz : diagonalCoordinates z = 0) : angleCoordinates z = z := by
  funext e
  by_cases he : e.val.1 = e.val.2
  · have hindex : (⟨toLex (e.val.1, e.val.1), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext rfl he)
    have hv := congrFun hz e.val.1
    simp only [diagonalCoordinates, Pi.zero_apply, hindex] at hv
    simp [angleCoordinates, spectralParameters, he, hv]
  · simp [angleCoordinates, spectralParameters, he]

@[simp] theorem angleCoordinates_spectralParameters {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    angleCoordinates (spectralParameters lam z) = angleCoordinates z := by
  funext e
  simp only [angleCoordinates, spectralParameters, Pi.zero_apply]
  split_ifs <;> rfl

noncomputable def exponentialOrthogonal {n : ℕ} (z : LowerIndex n → ℝ) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨exponentialOrthogonalMatrix z, exponentialOrthogonalMatrix_mem z⟩

@[simp] theorem exponentialOrthogonal_angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    exponentialOrthogonal (angleCoordinates z) = exponentialOrthogonal z := by
  apply Subtype.ext
  change NormedSpace.exp (skewMatrix (angleCoordinates z)) = NormedSpace.exp (skewMatrix z)
  rw [skewMatrix_angleCoordinates]

theorem exponentialSpectralCoordinates_angleCoordinates {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    exponentialSpectralCoordinates lam (angleCoordinates z) =
      symmetricCoordinates (orthogonalDiagonal (exponentialOrthogonal z) lam) := by
  rw [exponentialSpectralCoordinates, exponentialSpectralMatrix_eq_congruence,
    diagonalCoordinates_angleCoordinates, add_zero]
  change symmetricCoordinates (orthogonalDiagonal
    (exponentialOrthogonal (angleCoordinates z)) lam) = _
  rw [exponentialOrthogonal_angleCoordinates]

noncomputable def jointExponentialCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    LowerIndex n → ℝ :=
  symmetricCoordinates (orthogonalDiagonal (exponentialOrthogonal z) (diagonalCoordinates z))

set_option backward.isDefEq.respectTransparency false in
theorem jointExponentialCoordinates_differentiable (n : ℕ) :
    Differentiable ℝ (jointExponentialCoordinates (n := n)) := by
  have hQ : Differentiable ℝ (exponentialOrthogonalMatrix (n := n)) :=
    (exponentialMatrix_differentiable n).comp (skewContinuousLinearMap n).differentiable
  have hQT : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      NormedSpace.exp (-skewMatrix z)) :=
    (exponentialMatrix_differentiable n).comp (-skewContinuousLinearMap n).differentiable
  have h := (lowerContinuousLinearMap n).differentiable.comp
    ((hQ.mul (diagonalContinuousLinearMap n).differentiable).mul hQT)
  convert h using 1
  funext z
  change symmetricCoordinates (exponentialOrthogonalMatrix z *
      Matrix.diagonal (diagonalCoordinates z) * (exponentialOrthogonalMatrix z).transpose) =
    symmetricCoordinates (exponentialOrthogonalMatrix z *
      Matrix.diagonal (diagonalCoordinates z) * NormedSpace.exp (-skewMatrix z))
  rw [exponentialOrthogonalMatrix_transpose]

theorem isOpen_strictMono_coordinates (n : ℕ) :
    IsOpen {lam : Fin n → ℝ | StrictMono lam} := by
  have hset : {lam : Fin n → ℝ | StrictMono lam} =
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {lam : Fin n → ℝ | lam i < lam j} := by
    ext lam
    simp only [mem_ofPred_eq, mem_iInter]
    rfl
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)

def angularPatchDomain {n : ℕ} (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀) :
    Set (LowerIndex n → ℝ) :=
  {z | StrictMono (diagonalCoordinates z) ∧
    angleCoordinates z ∈ (exponentialSpectralChart lam₀ hlam₀).source}

theorem angularPatchDomain_isOpen {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) : IsOpen (angularPatchDomain lam₀ hlam₀) := by
  have hd : Continuous (diagonalCoordinates (n := n)) := by
    exact continuous_pi fun i => continuous_apply _
  exact ((isOpen_strictMono_coordinates n).preimage hd).inter
    ((exponentialSpectralChart lam₀ hlam₀).open_source.preimage
      (angleContinuousLinearMap n).continuous)

theorem angularPatchDomain_injOn {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) :
    InjOn jointExponentialCoordinates (angularPatchDomain lam₀ hlam₀) := by
  intro z hz w hw hzw
  have hmatrix : orthogonalDiagonal (exponentialOrthogonal z) (diagonalCoordinates z) =
      orthogonalDiagonal (exponentialOrthogonal w) (diagonalCoordinates w) := by
    have h := congrArg symmetricMatrix hzw
    simpa only [jointExponentialCoordinates,
      symmetricMatrix_symmetricCoordinates (orthogonalDiagonal_isHermitian _ _)] using h
  obtain ⟨hdiag, hsign⟩ :=
    (ordered_orthogonalDiagonal_eq_iff _ _ hz.1 hw.1).mp hmatrix
  have hfixed : orthogonalDiagonal (exponentialOrthogonal z) lam₀ =
      orthogonalDiagonal (exponentialOrthogonal w) lam₀ := by
    obtain ⟨s, hs⟩ := hsign
    rw [hs]
    exact signedOrthogonal_congruence_diagonal _ s lam₀
  have hangle : angleCoordinates z = angleCoordinates w := by
    apply (exponentialSpectralChart lam₀ hlam₀).injOn hz.2 hw.2
    simp only [exponentialSpectralChart_apply, exponentialSpectralCoordinates_angleCoordinates]
    exact congrArg symmetricCoordinates hfixed
  rw [← spectralParameters_coordinates z, ← spectralParameters_coordinates w, hdiag, hangle]

theorem angularPatch_image_measurable {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) :
    MeasurableSet (jointExponentialCoordinates '' angularPatchDomain lam₀ hlam₀) :=
  (angularPatchDomain_isOpen lam₀ hlam₀).measurableSet.image_of_continuousOn_injOn
    (jointExponentialCoordinates_differentiable n).continuous.continuousOn
    (angularPatchDomain_injOn lam₀ hlam₀)

end ResearchMain.WishartBlocks.Weyl
