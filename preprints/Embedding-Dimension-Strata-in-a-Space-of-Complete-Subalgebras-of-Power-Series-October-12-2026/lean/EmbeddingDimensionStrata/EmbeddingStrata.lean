import EmbeddingDimensionStrata.RelationMatrix
import EmbeddingDimensionStrata.GlobalPolynomialMaps
import EmbeddingDimensionStrata.CompleteCotangent

/-! # Exact and at-most generator strata of the actual subalgebra variety -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

def embeddingStratum (d : ℕ) : Set (ParameterSpace (K := K)) := {p | embeddingDimension p = d}

def generatorStratum (d : ℕ) : Set (ParameterSpace (K := K)) :=
  {p | ∃ g : Fin d → parameterJetAlgebra p.val, Algebra.adjoin K (Set.range g) = ⊤}

theorem mem_generatorStratum (p : ParameterSpace (K := K)) (d : ℕ) :
    p ∈ generatorStratum d ↔ embeddingDimension p ≤ d := parameter_exists_n_generators_iff p d

theorem embeddingDimension_bounds (p : ParameterSpace (K := K)) :
    3 ≤ embeddingDimension p ∧ embeddingDimension p ≤ 5 := by
  have hh := triangularRelationMatrix_rank_le_two
    (relationCoordinate p.val 0) (relationCoordinate p.val 1) (relationCoordinate p.val 2)
  rw [embeddingDimension_matrix_rank]
  change 3 ≤ 5 - (triangularRelationMatrix _ _ _).rank ∧
    5 - (triangularRelationMatrix _ _ _).rank ≤ 5
  omega

theorem embeddingDimension_eq_three (p : ParameterSpace (K := K)) :
    embeddingDimension p = 3 ↔ relationCoordinate p.val 0 * relationCoordinate p.val 1 ≠ 0 := by
  have hr := triangularRelationMatrix_rank_two_iff
    (relationCoordinate p.val 0) (relationCoordinate p.val 1) (relationCoordinate p.val 2)
  have hb := triangularRelationMatrix_rank_le_two
    (relationCoordinate p.val 0) (relationCoordinate p.val 1) (relationCoordinate p.val 2)
  rw [embeddingDimension_matrix_rank]
  change 5 - (triangularRelationMatrix _ _ _).rank = 3 ↔ _
  rw [← hr]
  omega

theorem embeddingDimension_eq_five (p : ParameterSpace (K := K)) :
    embeddingDimension p = 5 ↔
      relationCoordinate p.val 0 = 0 ∧ relationCoordinate p.val 1 = 0 ∧ relationCoordinate p.val 2 = 0 := by
  have hr := triangularRelationMatrix_rank_zero_iff
    (relationCoordinate p.val 0) (relationCoordinate p.val 1) (relationCoordinate p.val 2)
  rw [embeddingDimension_matrix_rank]
  change 5 - (triangularRelationMatrix _ _ _).rank = 5 ↔ _
  rw [← hr]
  omega

theorem embeddingDimension_eq_four (p : ParameterSpace (K := K)) :
    embeddingDimension p = 4 ↔
      relationCoordinate p.val 0 * relationCoordinate p.val 1 = 0 ∧
      ¬ (relationCoordinate p.val 0 = 0 ∧ relationCoordinate p.val 1 = 0 ∧ relationCoordinate p.val 2 = 0) := by
  have hr := triangularRelationMatrix_rank_one_iff
    (relationCoordinate p.val 0) (relationCoordinate p.val 1) (relationCoordinate p.val 2)
  rw [embeddingDimension_matrix_rank]
  change 5 - (triangularRelationMatrix _ _ _).rank = 4 ↔ _
  rw [← hr]
  omega

theorem generatorStratum_two_eq_empty : generatorStratum (K := K) 2 = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false, mem_generatorStratum]
  have hh := (embeddingDimension_bounds p).1
  omega

theorem generatorStratum_three_eq_exact : generatorStratum (K := K) 3 = embeddingStratum 3 := by
  ext p
  rw [mem_generatorStratum]
  change embeddingDimension p ≤ 3 ↔ embeddingDimension p = 3
  have hh := (embeddingDimension_bounds p).1
  omega

theorem generatorStratum_five_eq_univ : generatorStratum (K := K) 5 = Set.univ := by
  ext p
  simp only [Set.mem_univ, iff_true, mem_generatorStratum]
  exact (embeddingDimension_bounds p).2

private theorem forall_fin_three (P : Fin 3 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0,h 1,h 2⟩
  · rintro ⟨h0,h1,h2⟩ i; fin_cases i <;> assumption

theorem generatorStratum_four_iff (p : ParameterSpace (K := K)) :
    p ∈ generatorStratum 4 ↔ ∃ i : Fin 3, relationCoordinate p.val i ≠ 0 := by
  rw [mem_generatorStratum]
  have hb := embeddingDimension_bounds p
  have h5 := embeddingDimension_eq_five p
  have hz : (∀ i : Fin 3, relationCoordinate p.val i = 0) ↔
      relationCoordinate p.val 0 = 0 ∧ relationCoordinate p.val 1 = 0 ∧ relationCoordinate p.val 2 = 0 :=
    forall_fin_three (fun i => relationCoordinate p.val i = 0)
  rw [← not_forall]
  rw [hz, ← h5]
  omega

/-- The at-most-four locus is the punctured three-coordinate product, under
an explicit polynomial isomorphism of the actual semantic parameter space. -/
theorem generatorStratum_four_coordinates (p : ParameterSpace (K := K)) :
    p ∈ generatorStratum 4 ↔ ∃ i : Fin 3, parameterAffineEquiv p (Sum.inr i) ≠ 0 := by
  rw [generatorStratum_four_iff]
  simp only [parameterAffineEquiv_ABC]

theorem generatorStratum_three_coordinates (p : ParameterSpace (K := K)) :
    p ∈ generatorStratum 3 ↔
      parameterAffineEquiv p (Sum.inr 0) * parameterAffineEquiv p (Sum.inr 1) ≠ 0 := by
  rw [generatorStratum_three_eq_exact, parameterAffineEquiv_ABC, parameterAffineEquiv_ABC]
  exact embeddingDimension_eq_three p

def generatorStratumFourEquiv : generatorStratum (K := K) 4 ≃
    {x : AffineCoordinate → K // ∃ i : Fin 3, x (Sum.inr i) ≠ 0} where
  toFun p := ⟨parameterAffineEquiv p.val,(generatorStratum_four_coordinates p.val).mp p.property⟩
  invFun x := ⟨parameterAffineEquiv.symm x.val,
    (generatorStratum_four_coordinates _).mpr (by simpa using x.property)⟩
  left_inv p := Subtype.ext (parameterAffineEquiv.symm_apply_apply p.val)
  right_inv x := Subtype.ext (parameterAffineEquiv.apply_symm_apply x.val)

end EmbeddingDimensionStrata
