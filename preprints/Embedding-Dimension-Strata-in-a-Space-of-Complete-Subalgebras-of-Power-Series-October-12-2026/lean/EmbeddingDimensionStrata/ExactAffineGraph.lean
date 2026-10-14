import EmbeddingDimensionStrata.CoefficientDependence

/-! # The exact original-order homogeneous graph statement of Theorem affine -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

/-- The remaining original-order triangularity exception, r48 independent ofw49. -/
theorem secondPolynomial_W_not_mem_vars : eliminatedCoordinate 2 ∉ (definingPolynomial 1).vars := by
  classical
  let q := Function.update (MvPolynomial.X : NormalCoordinate → CoordinatePolynomial) (eliminatedCoordinate 2) 0
  have he : MvPolynomial.bind₁ q (definingPolynomial 1) = definingPolynomial 1 := by
    rw [← integral_evaluation_eq_bind]
    change MvPolynomial.eval₂ (Int.castRingHom CoordinatePolynomial) q (definingPolynomial 1) = _
    rw [eval_definingPolynomial]
    exact secondPolynomial_W_update_invariant MvPolynomial.X 0
  intro hh
  rw [← he] at hh
  obtain ⟨j,_,hj⟩ := MvPolynomial.mem_vars_bind₁ q (definingPolynomial 1) hh
  by_cases hje : j = eliminatedCoordinate 2
  · subst j
    simp [q] at hj
  · change eliminatedCoordinate 2 ∈ (Function.update MvPolynomial.X (eliminatedCoordinate 2) 0 j).vars at hj
    rw [Function.update_of_ne hje,MvPolynomial.vars_X] at hj
    exact hje (Finset.mem_singleton.mp hj).symm

def originalEquationRemainder (i : Fin 5) : CoordinatePolynomial :=
  removeLinearTerm (definingPolynomial i) (eliminatedCoordinate i)

theorem definingPolynomial_original_weighted (i : Fin 5) :
    (definingPolynomial i).IsWeightedHomogeneous coordinateWeight (coordinateWeight (eliminatedCoordinate i)) :=
  Eq.mpr (congrArg (fun d => (definingPolynomial i).IsWeightedHomogeneous coordinateWeight d)
    (eliminatedCoordinate_weight i)) (definingPolynomial_weighted i)

theorem originalEquationRemainder_weighted (i : Fin 5) :
    (originalEquationRemainder i).IsWeightedHomogeneous coordinateWeight (coordinateWeight (eliminatedCoordinate i)) :=
  removeLinearTerm_weighted _ (definingPolynomial_original_weighted i)

theorem original_equation_decomposition (i : Fin 5) :
    definingPolynomial i = -MvPolynomial.X (eliminatedCoordinate i) + originalEquationRemainder i := by
  conv_lhs => rw [polynomial_linear_decomposition (definingPolynomial i) (eliminatedCoordinate i)]
  rw [definingPolynomial_linear_coefficient]
  simp only [map_neg,map_one,neg_one_mul,originalEquationRemainder]

theorem original_remainder_ignores {i j : Fin 5}
    (hne : j ≠ i) (hh : eliminatedCoordinate j ∉ (definingPolynomial i).vars) :
    eliminatedCoordinate j ∉ (originalEquationRemainder i).vars := by
  classical
  intro h
  have hs := MvPolynomial.vars_sub_subset (p := definingPolynomial i)
    (q := MvPolynomial.monomial (Finsupp.single (eliminatedCoordinate i) 1)
      ((definingPolynomial i).coeff (Finsupp.single (eliminatedCoordinate i) 1))) h
  rcases Finset.mem_union.mp hs with hfirst | hsecond
  · exact hh hfirst
  · rw [definingPolynomial_linear_coefficient,
      MvPolynomial.vars_monomial_single _ (by decide) (by decide)] at hsecond
    exact hne (eliminatedCoordinate_injective (Finset.mem_singleton.mp hsecond))

/-- The paper's original order r47,r48,q59,r49,r59 is triangular, including
the lower-weight w49 exception in r48. -/
theorem originalEquationRemainder_triangular (i j : Fin 5) (hij : i ≤ j) :
    eliminatedCoordinate j ∉ (originalEquationRemainder i).vars := by
  have hall : ∀ i j : Fin 5, i ≤ j → i = j ∨
      coordinateWeight (eliminatedCoordinate i) < coordinateWeight (eliminatedCoordinate j) ∨
      (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by decide
  rcases hall i j hij with rfl | hlt | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact removeLinearTerm_not_mem_vars _ (definingPolynomial_original_weighted _)
  · exact weighted_not_mem_vars (originalEquationRemainder_weighted i) _ hlt
  · exact original_remainder_ignores (by decide) firstPolynomial_W_not_mem_vars
  · exact original_remainder_ignores (by decide) secondPolynomial_W_not_mem_vars

section Ring
variable {A : Type*} [CommRing A]

/-- The five equations cut out exactly the graph of the five homogeneous
solved polynomials, in the original order of the paper. -/
theorem definingEquations_iff_polynomial_graph (p : NormalCoordinate → A) :
    (∀ i : Fin 5, definingEquation p i = 0) ↔
      ∀ i : Fin 5, p (eliminatedCoordinate i) = MvPolynomial.eval₂ (Int.castRingHom A)
        (fun j : FreeCoordinate => p j.val) (freeParameterPolynomial (eliminatedCoordinate i)) := by
  classical
  constructor
  · intro he i
    have hh := congrFun (solveFreePoint_unique p ((definingEquations_iff_fixed p).mp he))
      (eliminatedCoordinate i)
    rw [← eval_freeParameterPolynomial] at hh
    exact hh.symm
  · intro he
    have hp : solveFreePoint (fun j : FreeCoordinate => p j.val) 5 = p := by
      funext j
      by_cases hj : j ∉ eliminatedCoordinates
      · exact solveFreePoint_free _ 5 ⟨j,hj⟩
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (not_not.mp hj)
        exact (eval_freeParameterPolynomial _ _).symm.trans (he i).symm
    have hh : ∀ i : Fin 5,
        definingEquation (solveFreePoint (fun j : FreeCoordinate => p j.val) 5) i = 0 := by
      apply (definingEquations_iff_fixed _).mpr
      intro i
      exact solveFreePoint_equations _ 5 i i.isLt
    rwa [hp] at hh

end Ring
section Field
variable {K : Type*} [Field K]

/-- The homogeneous graph is the genuine semigroup-defined subalgebra locus. -/
theorem parameter_condition_iff_polynomial_graph (p : NormalCoordinate → K) :
    (∀ n, JetHasValue (parameterJetAlgebra p) n ↔ Gamma n) ↔
      ∀ i : Fin 5, p (eliminatedCoordinate i) = MvPolynomial.eval₂ (Int.castRingHom K)
        (fun j : FreeCoordinate => p j.val) (freeParameterPolynomial (eliminatedCoordinate i)) :=
  (parameter_condition_iff_equations p).trans (definingEquations_iff_polynomial_graph p)

end Field
end EmbeddingDimensionStrata
