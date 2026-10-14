import EmbeddingDimensionStrata.CotangentDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The displayed 2×2 relation matrix and its exact ranks -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- The relation matrix, with rows corresponding to H⁴−XZ and H²Z−XW. -/
def triangularRelationMatrix (a b c : K) : Matrix (Fin 2) (Fin 2) K := !![a,c;0,b]

def relationMatrix (p : NormalCoordinate → K) : Matrix (Fin 2) (Fin 2) K :=
  triangularRelationMatrix (relationCoordinate p 0) (relationCoordinate p 1) (relationCoordinate p 2)

/-- Inclusion of the last two generator coordinates. -/
def lastTwo : (Fin 2 → K) →ₗ[K] (Fin 5 → K) where
  toFun x := ![0,0,0,x 0,x 1]
  map_add' := by intro x y; funext i; fin_cases i <;> simp
  map_smul' := by intro a x; funext i; fin_cases i <;> simp

theorem lastTwo_injective : Function.Injective (lastTwo (K := K)) := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h 3
  · exact congrFun h 4

theorem relationVectorSpace_image (p : NormalCoordinate → K) :
    (Submodule.span K (Set.range (relationMatrix p).row)).map lastTwo = relationVectorSpace p := by
  rw [Submodule.map_span]
  apply congrArg (Submodule.span K)
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    fin_cases i
    · exact Set.mem_insert_iff.mpr (Or.inl (linearTerms_relationF p).symm)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (linearTerms_relationG p).symm))
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨(relationMatrix p).row 0,⟨0,rfl⟩,(linearTerms_relationF p).symm⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨(relationMatrix p).row 1,⟨1,rfl⟩,(linearTerms_relationG p).symm⟩

theorem relationVectorSpace_finrank (p : NormalCoordinate → K) :
    Module.finrank K (relationVectorSpace p) = (relationMatrix p).rank := by
  rw [Matrix.rank_eq_finrank_span_row, ← relationVectorSpace_image p]
  exact (Submodule.equivMapOfInjective lastTwo lastTwo_injective _).finrank_eq.symm

/-- The paper's matrix formula for the true cotangent embedding dimension. -/
theorem embeddingDimension_matrix_rank (p : ParameterSpace (K := K)) :
    embeddingDimension p = 5 - (relationMatrix p.val).rank := by
  rw [embeddingDimension_relation_rank, relationVectorSpace_finrank]

theorem triangularRelationMatrix_rank_le_two (a b c : K) :
    (triangularRelationMatrix a b c).rank ≤ 2 := Matrix.rank_le_width _

theorem triangularRelationMatrix_rank_le_one (a b c : K) (hab : a*b = 0) :
    (triangularRelationMatrix a b c).rank ≤ 1 := by
  rcases mul_eq_zero.mp hab with rfl | rfl
  · have heq : triangularRelationMatrix (0 : K) b c = Matrix.vecMulVec ![c,b] ![0,1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [triangularRelationMatrix, Matrix.vecMulVec]
    rw [heq]
    exact Matrix.rank_vecMulVec_le _ _
  · have heq : triangularRelationMatrix a (0 : K) c = Matrix.vecMulVec ![1,0] ![a,c] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [triangularRelationMatrix, Matrix.vecMulVec]
    rw [heq]
    exact Matrix.rank_vecMulVec_le _ _

theorem triangularRelationMatrix_rank_two_iff (a b c : K) :
    (triangularRelationMatrix a b c).rank = 2 ↔ a*b ≠ 0 := by
  constructor
  · intro hr hab
    have hh := triangularRelationMatrix_rank_le_one a b c hab
    omega
  · intro hab
    have hd : (triangularRelationMatrix a b c).det ≠ 0 := by
      simpa [triangularRelationMatrix, Matrix.det_fin_two] using hab
    exact Matrix.rank_of_det_ne_zero hd

theorem triangularRelationMatrix_rank_zero_iff (a b c : K) :
    (triangularRelationMatrix a b c).rank = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hr
    have hs : Submodule.span K (Set.range (triangularRelationMatrix a b c).row) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      exact (Matrix.rank_eq_finrank_span_row _).symm.trans hr
    have hrow (i : Fin 2) : (triangularRelationMatrix a b c).row i = 0 := by
      have hh : (triangularRelationMatrix a b c).row i ∈
          Submodule.span K (Set.range (triangularRelationMatrix a b c).row) :=
        Submodule.subset_span (Set.mem_range_self i)
      rw [hs] at hh
      exact hh
    exact ⟨congrFun (hrow 0) 0,congrFun (hrow 1) 1,congrFun (hrow 0) 1⟩
  · rintro ⟨rfl,rfl,rfl⟩
    have hz : triangularRelationMatrix (0 : K) 0 0 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hz,Matrix.rank_zero]

theorem triangularRelationMatrix_rank_one_iff (a b c : K) :
    (triangularRelationMatrix a b c).rank = 1 ↔
      a*b = 0 ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) := by
  have h0 := triangularRelationMatrix_rank_zero_iff a b c
  have h2 := triangularRelationMatrix_rank_two_iff a b c
  have hle := triangularRelationMatrix_rank_le_two a b c
  constructor
  · intro h
    exact ⟨by by_contra hh; have := h2.mpr hh; omega,by intro hh; have := h0.mpr hh; omega⟩
  · rintro ⟨hab,hn⟩
    have hr0 : (triangularRelationMatrix a b c).rank ≠ 0 := by intro h; exact hn (h0.mp h)
    have hr2 : (triangularRelationMatrix a b c).rank ≠ 2 := by intro h; exact h2.mp h hab
    omega

end EmbeddingDimensionStrata
