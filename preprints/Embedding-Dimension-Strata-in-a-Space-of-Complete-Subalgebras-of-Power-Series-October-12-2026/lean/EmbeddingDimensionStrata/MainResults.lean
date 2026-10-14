import EmbeddingDimensionStrata.ReductionDetection
import EmbeddingDimensionStrata.ClassicalCoordinates
import EmbeddingDimensionStrata.RegularOpenObstructions
import EmbeddingDimensionStrata.ExactAffineGraph
import EmbeddingDimensionStrata.RegularConstants

/-!
# Embedding-dimension strata for Γ = ⟨10,11,34,46,58⟩

Public theorem assembly for the October 12, 2026 paper. The parameter type is
the genuine semigroup locus of embedded jet subalgebras; its correspondence
with actual closed power-series subalgebras is proved in ParameterSpace.
-/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
open AlgebraicGeometry CategoryTheory

theorem affineCoordinate_card : Fintype.card AffineCoordinate = 57 := by decide

/-- Theorem affine: the original five-equation affine scheme is A57. -/
def affineSchemeIso (K : Type*) [CommRing K] :
    parameterScheme K ≅ Spec (CommRingCat.of (MvPolynomial (Fin 57) K)) :=
  Scheme.Spec.mapIso ((parameterCoordinateRingEquiv K).trans
    (MvPolynomial.renameEquiv K (Fintype.equivFinOfCardEq affineCoordinate_card))).toRingEquiv.symm.toCommRingCatIso.op

/-- The retained q coordinates are exactly all X/H coefficients and the six
listed Z/W/U coefficients of Theorem coords. -/
theorem remainingCoordinate_description (j : NormalCoordinate) :
    (¬∃ i : Fin 8, globalPivot i = j) ↔
      j.val.1 = 0 ∨ j.val.1 = 1 ∨
      (j.val.1 = 2 ∧ j.val.2.val ∈ ({35,47,59} : Finset ℕ)) ∨
      (j.val.1 = 3 ∧ j.val.2.val ∈ ({47,59} : Finset ℕ)) ∨
      (j.val.1 = 4 ∧ j.val.2.val = 59) := by
  have hh : ∀ j : NormalCoordinate, (¬∃ i : Fin 8, globalPivot i = j) ↔
      j.val.1 = 0 ∨ j.val.1 = 1 ∨
      (j.val.1 = 2 ∧ j.val.2.val ∈ ({35,47,59} : Finset ℕ)) ∨
      (j.val.1 = 3 ∧ j.val.2.val ∈ ({47,59} : Finset ℕ)) ∨
      (j.val.1 = 4 ∧ j.val.2.val = 59) := by decide
  exact hh j

section Field
variable {K : Type*} [Field K]

/-- Theorem main, pointwise cotangent formula and actual algebra-generator minimum. -/
theorem main_rank_and_generators (p : ParameterSpace (K := K)) :
    embeddingDimension p = 5 - (relationMatrix p.val).rank ∧
    IsLeast (NilpotentGenerators.generatorNumbers (K := K) (A := parameterJetAlgebra p.val))
      (5 - (relationMatrix p.val).rank) := by
  refine ⟨embeddingDimension_matrix_rank p,?_⟩
  rw [← embeddingDimension_matrix_rank]
  exact parameter_isLeast_generatorNumbers p

/-- The scheme open is exactly the actual four-generator locus on parameter points. -/
theorem four_generator_scheme_membership (p : ParameterSpace (K := K)) :
    parameterPrime K p ∈ parameterFourStratumOpen K ↔ p ∈ generatorStratum 4 :=
  (parameterFourStratumOpen_parameterPrime K p).trans (generatorStratum_four_iff p).symm

/-- Exact coordinate description of all nonempty embedding-dimension strata. -/
theorem exact_strata (p : ParameterSpace (K := K)) :
    (embeddingDimension p = 3 ↔ relationCoordinate p.val 0 * relationCoordinate p.val 1 ≠ 0) ∧
    (embeddingDimension p = 4 ↔ relationCoordinate p.val 0 * relationCoordinate p.val 1 = 0 ∧
      ¬ (relationCoordinate p.val 0 = 0 ∧ relationCoordinate p.val 1 = 0 ∧ relationCoordinate p.val 2 = 0)) ∧
    (embeddingDimension p = 5 ↔ relationCoordinate p.val 0 = 0 ∧
      relationCoordinate p.val 1 = 0 ∧ relationCoordinate p.val 2 = 0) :=
  ⟨embeddingDimension_eq_three p,embeddingDimension_eq_four p,embeddingDimension_eq_five p⟩

end Field
section FormalTopology
variable {K : Type*} [Field K] [TopologicalSpace K] [DiscreteTopology K]
open scoped PowerSeries.WithPiTopology

/-- The same rank computes the own cotangent space and the minimum number
of topological generators of every actual complete embedded subalgebra. -/
theorem main_complete_rank_and_generators (S : CompleteGammaSubalgebra (K := K)) :
    Module.finrank K (completeAugmentationIdeal S).Cotangent =
      5 - (relationMatrix (normalCoordinates S)).rank ∧
    IsLeast (topologicalGeneratorNumbers S) (5 - (relationMatrix (normalCoordinates S)).rank) := by
  have hr := embeddingDimension_matrix_rank (toParameterSpace S)
  change embeddingDimension (toParameterSpace S) = 5 - (relationMatrix (normalCoordinates S)).rank at hr
  refine ⟨(completeCotangent_finrank S).trans hr,?_⟩
  rw [← hr]
  exact complete_isLeast_topologicalGeneratorNumbers S

end FormalTopology

/-- Theorem q47: neither a fixed generator-polynomial reduction test nor
one or two polynomial principal opens describe the actual four-generator locus. -/
theorem question47 (f : MvPolynomial (Fin 5) ℂ)
    (h h₁ h₂ : ParameterCoordinateRing ℂ) :
    (¬ ∀ p : ParameterSpace (K := ℂ), p ∈ generatorStratum 4 ↔
      HasOrder (partialReduceSeries p.val 60 (generatorEvaluation (RingHom.id ℂ) p.val f)) 58) ∧
    generatorStratum 4 ≠ parameterRegularPrincipalOpen h ∧
    generatorStratum 4 ≠ parameterRegularPrincipalOpen h₁ ∪ parameterRegularPrincipalOpen h₂ :=
  ⟨no_fixed_polynomial_reduction_detector f, generatorStratum_four_not_regular_principal h,
    generatorStratum_four_not_two_regular_principals h₁ h₂⟩

/-- Theorem q48: the actual four-generator scheme is nonaffine and not the
proposed product, and its classical point space is simply connected and not
homeomorphic to that product. -/
theorem question48 :
    (¬ IsAffine (parameterFourStratumOpen ℂ).toScheme) ∧
    IsEmpty ((parameterFourStratumOpen ℂ).toScheme ≅ GeometryObstructions.predictedFourStratumScheme ℂ) ∧
    SimplyConnectedSpace (generatorStratum (K := ℂ) 4) ∧
    IsEmpty (generatorStratum (K := ℂ) 4 ≃ₜ TopologyObstructions.ClassicalPredictedProduct 56) :=
  ⟨parameterFourStratumScheme_not_affine ℂ, parameterFourStratum_not_iso_predicted ℂ,
    generatorStratum_four_simplyConnected, generatorStratum_four_not_homeomorphic_predicted⟩

/-- The remaining units assertion of Theorem q48, using the canonical
constant sections on the original scheme open. -/
theorem question48_units
    (s : Γ(parameterScheme ℂ, parameterFourStratumOpen ℂ)) :
    IsUnit s ↔ ∃ c : ℂ, c ≠ 0 ∧
      algebraMap (ParameterCoordinateRing ℂ) Γ(parameterScheme ℂ, parameterFourStratumOpen ℂ)
        (algebraMap ℂ (ParameterCoordinateRing ℂ) c) = s :=
  parameterFour_units_are_constant_sections ℂ s

end EmbeddingDimensionStrata
