import EmbeddingDimensionStrata.DivisionCoordinates
import Mathlib.RingTheory.Ideal.Cotangent

/-! # The genuine maximal ideal and cotangent module -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- The actual constant-coefficient augmentation on the finite quotient. -/
def jetAugmentation : Jet K 60 →ₐ[K] K where
  toFun := jetCoeff 60 0
  map_zero' := (jetCoeff 60 (0 : Fin 60)).map_zero
  map_one' := by
    change PowerSeries.coeff 0 (1 : PowerSeries K) = 1
    exact PowerSeries.coeff_zero_one
  map_add' := (jetCoeff 60 (0 : Fin 60)).map_add
  map_mul' := by
    intro x y
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    obtain ⟨g,rfl⟩ := jetMap_surjective 60 y
    rw [← map_mul]
    change PowerSeries.coeff 0 (f*g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  commutes' := by
    intro a
    rw [← (jetMap K 60).commutes a]
    change PowerSeries.coeff 0 (algebraMap K (PowerSeries K) a) = a
    simp

/-- The augmentation on the actual generated algebra. -/
def parameterAugmentation (p : NormalCoordinate → K) : parameterJetAlgebra p →ₐ[K] K :=
  jetAugmentation.comp (parameterJetAlgebra p).val

/-- The maximal ideal consists of precisely the elements with zero constant
coefficient, inside the actual algebra. -/
def augmentationIdeal (p : NormalCoordinate → K) : Ideal (parameterJetAlgebra p) :=
  RingHom.ker (parameterAugmentation p).toRingHom

theorem parameterAugmentation_surjective (p : NormalCoordinate → K) :
    Function.Surjective (parameterAugmentation p) := by
  intro a
  exact ⟨algebraMap K (parameterJetAlgebra p) a, (parameterAugmentation p).commutes a⟩

theorem augmentationIdeal_isMaximal (p : NormalCoordinate → K) :
    (augmentationIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (parameterAugmentation p).toRingHom
    (parameterAugmentation_surjective p)

/-- Embedding dimension is the dimension of the genuine ideal cotangent module
m/m². No matrix rank or coefficient model occurs in this definition. -/
def embeddingDimension (p : ParameterSpace (K := K)) : ℕ :=
  Module.finrank K (augmentationIdeal p.val).Cotangent

/-- The square-of-the-ideal test is the standard ideal-square test. -/
theorem augmentationCotangent_zero_iff (p : NormalCoordinate → K)
    (x : augmentationIdeal p) :
    (augmentationIdeal p).toCotangent x = 0 ↔
      (x : parameterJetAlgebra p) ∈ augmentationIdeal p ^ 2 :=
  (augmentationIdeal p).toCotangent_eq_zero x

end EmbeddingDimensionStrata
