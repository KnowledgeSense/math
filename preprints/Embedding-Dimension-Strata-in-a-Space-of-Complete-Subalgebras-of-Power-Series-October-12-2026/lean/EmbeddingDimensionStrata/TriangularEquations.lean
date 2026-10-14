import EmbeddingDimensionStrata.EliminatedCoordinates
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # A proved triangular system for the genuine five equations -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

/-- Solving in increasing weight swaps only the second and third equations.
The eliminated coordinates and the 57 free coordinates are unchanged. -/
def solvingOrder : Fin 5 ≃ Fin 5 := Equiv.swap 1 2

def solvedCoordinate (i : Fin 5) : NormalCoordinate := eliminatedCoordinate (solvingOrder i)
def solvedPolynomial (i : Fin 5) : CoordinatePolynomial := definingPolynomial (solvingOrder i)
def solutionRemainder (i : Fin 5) : CoordinatePolynomial :=
  removeLinearTerm (solvedPolynomial i) (solvedCoordinate i)

theorem solvedCoordinate_injective : Function.Injective solvedCoordinate :=
  eliminatedCoordinate_injective.comp solvingOrder.injective

theorem solvedPolynomial_weighted (i : Fin 5) :
    (solvedPolynomial i).IsWeightedHomogeneous coordinateWeight (coordinateWeight (solvedCoordinate i)) := by
  rw [solvedCoordinate, eliminatedCoordinate_weight]
  exact definingPolynomial_weighted (solvingOrder i)

theorem solutionRemainder_weighted (i : Fin 5) :
    (solutionRemainder i).IsWeightedHomogeneous coordinateWeight (coordinateWeight (solvedCoordinate i)) :=
  removeLinearTerm_weighted _ (solvedPolynomial_weighted i)

/-- Each equation is minus its solved coordinate plus a polynomial in earlier
coordinates. The latter dependency is proved below. -/
theorem solvedPolynomial_eq (i : Fin 5) :
    solvedPolynomial i = -MvPolynomial.X (solvedCoordinate i) + solutionRemainder i := by
  rw [polynomial_linear_decomposition (solvedPolynomial i) (solvedCoordinate i)]
  change MvPolynomial.C ((definingPolynomial (solvingOrder i)).coeff
    (Finsupp.single (eliminatedCoordinate (solvingOrder i)) 1)) *
    MvPolynomial.X (solvedCoordinate i) + solutionRemainder i = _
  rw [definingPolynomial_linear_coefficient]
  simp only [map_neg, map_one, neg_one_mul]

theorem firstPolynomial_W_linear_coefficient :
    (definingPolynomial 0).coeff (Finsupp.single (eliminatedCoordinate 2) 1) = 0 := by
  have hweight : (definingPolynomial 0).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (eliminatedCoordinate 2)) := definingPolynomial_weighted 0
  rw [← weighted_linear_coefficient _ hweight]
  have hev : MvPolynomial.eval (coordinateUnitPoint (eliminatedCoordinate 2))
      (definingPolynomial 0) = definingEquation (coordinateUnitPoint (eliminatedCoordinate 2)) 0 :=
    eval_definingPolynomial _ 0
  rw [hev]
  change PowerSeries.coeff 47 (reduceSeries _ 60 (relationF _)) = 0
  rw [relationF_unit_W _ (by rfl), map_zero, map_zero]

theorem firstPolynomial_W_not_mem_vars : eliminatedCoordinate 2 ∉ (definingPolynomial 0).vars := by
  have hweight : (definingPolynomial 0).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (eliminatedCoordinate 2)) := definingPolynomial_weighted 0
  have hh := removeLinearTerm_not_mem_vars (eliminatedCoordinate 2) hweight
  simpa only [removeLinearTerm, firstPolynomial_W_linear_coefficient,
    MvPolynomial.monomial_zero, sub_zero] using hh

theorem firstRemainder_W_not_mem_vars : solvedCoordinate 1 ∉ (solutionRemainder 0).vars := by
  classical
  intro hh
  change eliminatedCoordinate 2 ∈ (removeLinearTerm (definingPolynomial 0) (eliminatedCoordinate 0)).vars at hh
  have hsub := MvPolynomial.vars_sub_subset (p := definingPolynomial 0)
    (q := MvPolynomial.monomial (Finsupp.single (eliminatedCoordinate 0) 1)
      ((definingPolynomial 0).coeff (Finsupp.single (eliminatedCoordinate 0) 1))) hh
  rcases Finset.mem_union.mp hsub with hfirst | hsecond
  · exact firstPolynomial_W_not_mem_vars hfirst
  · rw [definingPolynomial_linear_coefficient,
      MvPolynomial.vars_monomial_single _ (by decide) (by decide)] at hsecond
    have heq := Finset.mem_singleton.mp hsecond
    have hij := eliminatedCoordinate_injective heq
    exact (by decide : (2 : Fin 5) ≠ 0) hij

/-- The remainder in equation i contains no solved variable at stage i or any
later stage. This establishes triangularity without expanding the large r59. -/
theorem solutionRemainder_not_mem_later (i j : Fin 5) (hij : i ≤ j) :
    solvedCoordinate j ∉ (solutionRemainder i).vars := by
  have hall : ∀ i j : Fin 5, i ≤ j →
      i = j ∨ coordinateWeight (solvedCoordinate i) < coordinateWeight (solvedCoordinate j) ∨
      (i = 0 ∧ j = 1) := by decide
  rcases hall i j hij with rfl | hweight | ⟨rfl,rfl⟩
  · exact removeLinearTerm_not_mem_vars _ (solvedPolynomial_weighted _)
  · exact weighted_not_mem_vars (solutionRemainder_weighted i) _ hweight
  · exact firstRemainder_W_not_mem_vars

/-- All deleted coordinates occur once in the solving order. -/
theorem mem_eliminatedCoordinates_iff (j : NormalCoordinate) :
    j ∈ eliminatedCoordinates ↔ ∃ i : Fin 5, solvedCoordinate i = j := by
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨solvingOrder.symm i, congrArg eliminatedCoordinate (solvingOrder.apply_symm_apply i)⟩
  · rintro ⟨i,rfl⟩
    exact Finset.mem_image.mpr ⟨solvingOrder i,Finset.mem_univ _,rfl⟩

end EmbeddingDimensionStrata
