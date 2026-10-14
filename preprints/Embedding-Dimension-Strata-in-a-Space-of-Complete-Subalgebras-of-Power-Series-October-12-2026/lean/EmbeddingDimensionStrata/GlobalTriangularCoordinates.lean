import EmbeddingDimensionStrata.TriangularAutomorphism

/-! # The simultaneous polynomial change to (q,A,B,C) -/
noncomputable section
namespace EmbeddingDimensionStrata
attribute [local irreducible] definingPolynomial relationCoordinatePolynomial

private def selectEight {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) (i : Fin 8) : α :=
  match i.val with
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
  | 4 => a4 | 5 => a5 | 6 => a6 | _ => a7

private theorem selectEight_rel {α β : Type*} (R : α → β → Prop)
    (a0 a1 a2 a3 a4 a5 a6 a7 : α) (b0 b1 b2 b3 b4 b5 b6 b7 : β)
    (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2) (h3 : R a3 b3)
    (h4 : R a4 b4) (h5 : R a5 b5) (h6 : R a6 b6) (h7 : R a7 b7) (i : Fin 8) :
    R (selectEight a0 a1 a2 a3 a4 a5 a6 a7 i) (selectEight b0 b1 b2 b3 b4 b5 b6 b7 i) := by
  fin_cases i <;> assumption

private theorem selectEight_at0 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 0 = a0 := rfl

private theorem selectEight_at1 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 1 = a1 := rfl

private theorem selectEight_at2 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 2 = a2 := rfl

private theorem selectEight_at3 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 3 = a3 := rfl

private theorem selectEight_at4 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 4 = a4 := rfl

private theorem selectEight_at5 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 5 = a5 := rfl

private theorem selectEight_at6 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 6 = a6 := rfl

private theorem selectEight_at7 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    selectEight a0 a1 a2 a3 a4 a5 a6 a7 7 = a7 := rfl

def globalPivot (i : Fin 8) : NormalCoordinate :=
  selectEight (coordinatePivot 0) (coordinatePivot 1) (eliminatedCoordinate 0)
    (eliminatedCoordinate 2) (eliminatedCoordinate 1) (eliminatedCoordinate 3)
    (coordinatePivot 2) (eliminatedCoordinate 4) i

def globalPolynomial (i : Fin 8) : CoordinatePolynomial :=
  selectEight (relationCoordinatePolynomial 0) (relationCoordinatePolynomial 1)
    (definingPolynomial 0) (definingPolynomial 2) (definingPolynomial 1)
    (definingPolynomial 3) (relationCoordinatePolynomial 2) (definingPolynomial 4) i

theorem globalPolynomial_at0 : globalPolynomial 0 = relationCoordinatePolynomial 0 :=
  selectEight_at0 _ _ _ _ _ _ _ _
theorem globalPivot_at0 : globalPivot 0 = coordinatePivot 0 :=
  selectEight_at0 _ _ _ _ _ _ _ _

theorem globalPolynomial_at1 : globalPolynomial 1 = relationCoordinatePolynomial 1 :=
  selectEight_at1 _ _ _ _ _ _ _ _
theorem globalPivot_at1 : globalPivot 1 = coordinatePivot 1 :=
  selectEight_at1 _ _ _ _ _ _ _ _

theorem globalPolynomial_at2 : globalPolynomial 2 = definingPolynomial 0 :=
  selectEight_at2 _ _ _ _ _ _ _ _
theorem globalPivot_at2 : globalPivot 2 = eliminatedCoordinate 0 :=
  selectEight_at2 _ _ _ _ _ _ _ _

theorem globalPolynomial_at3 : globalPolynomial 3 = definingPolynomial 2 :=
  selectEight_at3 _ _ _ _ _ _ _ _
theorem globalPivot_at3 : globalPivot 3 = eliminatedCoordinate 2 :=
  selectEight_at3 _ _ _ _ _ _ _ _

theorem globalPolynomial_at4 : globalPolynomial 4 = definingPolynomial 1 :=
  selectEight_at4 _ _ _ _ _ _ _ _
theorem globalPivot_at4 : globalPivot 4 = eliminatedCoordinate 1 :=
  selectEight_at4 _ _ _ _ _ _ _ _

theorem globalPolynomial_at5 : globalPolynomial 5 = definingPolynomial 3 :=
  selectEight_at5 _ _ _ _ _ _ _ _
theorem globalPivot_at5 : globalPivot 5 = eliminatedCoordinate 3 :=
  selectEight_at5 _ _ _ _ _ _ _ _

theorem globalPolynomial_at6 : globalPolynomial 6 = relationCoordinatePolynomial 2 :=
  selectEight_at6 _ _ _ _ _ _ _ _
theorem globalPivot_at6 : globalPivot 6 = coordinatePivot 2 :=
  selectEight_at6 _ _ _ _ _ _ _ _

theorem globalPolynomial_at7 : globalPolynomial 7 = definingPolynomial 4 :=
  selectEight_at7 _ _ _ _ _ _ _ _
theorem globalPivot_at7 : globalPivot 7 = eliminatedCoordinate 4 :=
  selectEight_at7 _ _ _ _ _ _ _ _

def globalRemainder (i : Fin 8) : CoordinatePolynomial :=
  removeLinearTerm (globalPolynomial i) (globalPivot i)

theorem globalPivot_injective : Function.Injective globalPivot := by decide

theorem globalPolynomial_weighted (i : Fin 8) :
    (globalPolynomial i).IsWeightedHomogeneous coordinateWeight (coordinateWeight (globalPivot i)) := by
  have hE (j : Fin 5) : (definingPolynomial j).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (eliminatedCoordinate j)) :=
    Eq.mpr (congrArg (fun d => (definingPolynomial j).IsWeightedHomogeneous coordinateWeight d)
      (eliminatedCoordinate_weight j)) (definingPolynomial_weighted j)
  exact selectEight_rel (fun (Q : CoordinatePolynomial) j => Q.IsWeightedHomogeneous coordinateWeight (coordinateWeight j))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (relationCoordinate_weighted 0) (relationCoordinate_weighted 1)
    (hE 0) (hE 2) (hE 1) (hE 3) (relationCoordinate_weighted 2) (hE 4) i

theorem globalPolynomial_linear_coefficient (i : Fin 8) :
    (globalPolynomial i).coeff (Finsupp.single (globalPivot i) 1) = -1 :=
  selectEight_rel (fun (Q : CoordinatePolynomial) j => Q.coeff (Finsupp.single j 1) = -1)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (relationCoordinate_linear_coefficient 0) (relationCoordinate_linear_coefficient 1)
    (definingPolynomial_linear_coefficient 0) (definingPolynomial_linear_coefficient 2)
    (definingPolynomial_linear_coefficient 1) (definingPolynomial_linear_coefficient 3)
    (relationCoordinate_linear_coefficient 2) (definingPolynomial_linear_coefficient 4) i

theorem globalPolynomial_eq (i : Fin 8) :
    globalPolynomial i = -MvPolynomial.X (globalPivot i) + globalRemainder i := by
  conv_lhs => rw [polynomial_linear_decomposition (globalPolynomial i) (globalPivot i)]
  rw [globalPolynomial_linear_coefficient i]
  simp only [map_neg, map_one, neg_one_mul, globalRemainder]

theorem coordinateA_W_not_mem_vars : coordinatePivot 1 ∉ (relationCoordinatePolynomial 0).vars := by
  have hh : (relationCoordinatePolynomial 0).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (coordinatePivot 1)) := relationCoordinate_weighted 0
  have h := removeLinearTerm_not_mem_vars (coordinatePivot 1) hh
  simpa only [removeLinearTerm, coordinateA_W_linear_coefficient,
    MvPolynomial.monomial_zero, sub_zero] using h

theorem globalRemainder_zero_one : globalPivot 1 ∉ (globalRemainder 0).vars := by
  classical
  intro hh
  rw [globalPivot_at1, globalRemainder, globalPolynomial_at0, globalPivot_at0] at hh
  have hsub := MvPolynomial.vars_sub_subset (p := relationCoordinatePolynomial 0)
    (q := MvPolynomial.monomial (Finsupp.single (coordinatePivot 0) 1)
      ((relationCoordinatePolynomial 0).coeff (Finsupp.single (coordinatePivot 0) 1))) hh
  rcases Finset.mem_union.mp hsub with hfirst | hsecond
  · exact coordinateA_W_not_mem_vars hfirst
  · rw [relationCoordinate_linear_coefficient,
      MvPolynomial.vars_monomial_single _ (by decide) (by decide)] at hsecond
    exact (by decide : coordinatePivot 1 ≠ coordinatePivot 0) (Finset.mem_singleton.mp hsecond)

theorem globalRemainder_triangular (i j : Fin 8) (hij : i ≤ j) :
    globalPivot j ∉ (globalRemainder i).vars := by
  have hall : ∀ i j : Fin 8, i ≤ j → i = j ∨
      coordinateWeight (globalPivot i) < coordinateWeight (globalPivot j) ∨
      (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) := by decide
  rcases hall i j hij with rfl | hlt | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact removeLinearTerm_not_mem_vars _ (globalPolynomial_weighted _)
  · exact weighted_not_mem_vars (removeLinearTerm_weighted _ (globalPolynomial_weighted i)) _ hlt
  · exact globalRemainder_zero_one
  · rw [globalPivot_at3, globalRemainder, globalPolynomial_at2, globalPivot_at2]
    exact firstRemainder_W_not_mem_vars

/-- A genuine polynomial automorphism of the whole 62-coordinate ambient
space; it records minus the five equations and minus A,B,C at eight pivots. -/
def globalTriangularData : PolynomialTriangular.Data NormalCoordinate 8 where
  pivot := globalPivot
  injective := globalPivot_injective
  remainder := globalRemainder
  triangular := globalRemainder_triangular

variable {K : Type*} [CommRing K]

def globalAmbientEquiv : (NormalCoordinate → K) ≃ (NormalCoordinate → K) :=
  PolynomialTriangular.equiv globalTriangularData

theorem globalAmbientEquiv_pivot (p : NormalCoordinate → K) (i : Fin 8) :
    globalAmbientEquiv p (globalPivot i) =
      -MvPolynomial.eval₂ (Int.castRingHom K) p (globalPolynomial i) := by
  change PolynomialTriangular.forward globalTriangularData p (globalTriangularData.pivot i) = _
  rw [PolynomialTriangular.forward_pivot, globalPolynomial_eq i]
  change p (globalPivot i) - PolynomialTriangular.ev p (globalRemainder i) =
    -PolynomialTriangular.ev p (-MvPolynomial.X (globalPivot i) + globalRemainder i)
  rw [map_add, map_neg]
  simp only [PolynomialTriangular.ev, MvPolynomial.eval₂Hom_X']
  ring

def equationGlobalIndex (i : Fin 5) : Fin 8 :=
  match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 5 | _ => 7

def coordinateGlobalIndex (i : Fin 3) : Fin 8 :=
  match i.val with | 0 => 0 | 1 => 1 | _ => 6

theorem globalAmbientEquiv_equation (p : NormalCoordinate → K) (i : Fin 5) :
    globalAmbientEquiv p (eliminatedCoordinate i) = -definingEquation p i := by
  have hp : globalPivot (equationGlobalIndex i) = eliminatedCoordinate i := by
    have h : ∀ i : Fin 5, globalPivot (equationGlobalIndex i) = eliminatedCoordinate i := by decide
    exact h i
  have hQ : globalPolynomial (equationGlobalIndex i) = definingPolynomial i := by
    fin_cases i
    · exact globalPolynomial_at2
    · exact globalPolynomial_at4
    · exact globalPolynomial_at3
    · exact globalPolynomial_at5
    · exact globalPolynomial_at7
  rw [← hp, globalAmbientEquiv_pivot, hQ, eval_definingPolynomial]

theorem globalAmbientEquiv_coordinate (p : NormalCoordinate → K) (i : Fin 3) :
    globalAmbientEquiv p (coordinatePivot i) = -relationCoordinate p i := by
  have hp : globalPivot (coordinateGlobalIndex i) = coordinatePivot i := by
    have h : ∀ i : Fin 3, globalPivot (coordinateGlobalIndex i) = coordinatePivot i := by decide
    exact h i
  have hQ : globalPolynomial (coordinateGlobalIndex i) = relationCoordinatePolynomial i := by
    fin_cases i
    · exact globalPolynomial_at0
    · exact globalPolynomial_at1
    · exact globalPolynomial_at6
  rw [← hp, globalAmbientEquiv_pivot, hQ, eval_relationCoordinatePolynomial]

end EmbeddingDimensionStrata
