import EmbeddingDimensionStrata.GlobalTriangularCoordinates

/-! # Actual complete subalgebras in the global coordinates (q,A,B,C) -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

/-- The 54 retained normal-form coefficients. -/
abbrev RemainingCoordinate := {j : NormalCoordinate // ¬∃ i : Fin 8, globalPivot i = j}

theorem remainingCoordinate_card : Fintype.card RemainingCoordinate = 54 := by decide

theorem coordinatePivot_injective : Function.Injective coordinatePivot := by decide

theorem globalPivot_partition (i : Fin 8) :
    (∃ c : Fin 3, globalPivot i = coordinatePivot c) ∨
    (∃ e : Fin 5, globalPivot i = eliminatedCoordinate e) := by
  have h : ∀ i : Fin 8, (∃ c : Fin 3, globalPivot i = coordinatePivot c) ∨
    (∃ e : Fin 5, globalPivot i = eliminatedCoordinate e) := by decide
  exact h i

theorem coordinatePivot_not_eliminated (i : Fin 3) (j : Fin 5) :
    coordinatePivot i ≠ eliminatedCoordinate j := by
  have h : ∀ i : Fin 3, ∀ j : Fin 5, coordinatePivot i ≠ eliminatedCoordinate j := by decide
  exact h i j

theorem coordinatePivot_in_global (i : Fin 3) : ∃ k : Fin 8, globalPivot k = coordinatePivot i := by
  have h : ∀ i : Fin 3, ∃ k : Fin 8, globalPivot k = coordinatePivot i := by decide
  exact h i

theorem eliminatedCoordinate_in_global (i : Fin 5) : ∃ k : Fin 8, globalPivot k = eliminatedCoordinate i := by
  have h : ∀ i : Fin 5, ∃ k : Fin 8, globalPivot k = eliminatedCoordinate i := by decide
  exact h i

section Ring
variable {K : Type*} [CommRing K]

def ZeroEquationSlice := {u : NormalCoordinate → K // ∀ i : Fin 5, u (eliminatedCoordinate i) = 0}

def embedGlobalCoordinates (q : RemainingCoordinate → K) (a : Fin 3 → K)
    (j : NormalCoordinate) : K :=
  if hfree : ¬∃ i : Fin 8, globalPivot i = j then q ⟨j,hfree⟩
  else if hcoord : ∃ i : Fin 3, coordinatePivot i = j then -a (Classical.choose hcoord) else 0

theorem embedGlobalCoordinates_free (q : RemainingCoordinate → K) (a : Fin 3 → K)
    (j : RemainingCoordinate) : embedGlobalCoordinates q a j.val = q j := by
  rw [embedGlobalCoordinates, dite_eq_left j.property]

theorem embedGlobalCoordinates_coordinate (q : RemainingCoordinate → K) (a : Fin 3 → K) (i : Fin 3) :
    embedGlobalCoordinates q a (coordinatePivot i) = -a i := by
  rw [embedGlobalCoordinates, dite_eq_right (not_not.mpr (coordinatePivot_in_global i)),
    dite_eq_left ⟨i,rfl⟩]
  have heq := coordinatePivot_injective
    (Classical.choose_spec (show ∃ j, coordinatePivot j = coordinatePivot i from ⟨i,rfl⟩))
  rw [heq]

theorem embedGlobalCoordinates_equation (q : RemainingCoordinate → K) (a : Fin 3 → K) (i : Fin 5) :
    embedGlobalCoordinates q a (eliminatedCoordinate i) = 0 := by
  rw [embedGlobalCoordinates, dite_eq_right (not_not.mpr (eliminatedCoordinate_in_global i))]
  apply dite_eq_right
  rintro ⟨j,hj⟩
  exact coordinatePivot_not_eliminated j i hj

theorem embedGlobalCoordinates_unique (u : ZeroEquationSlice (K := K)) :
    embedGlobalCoordinates (fun j : RemainingCoordinate => u.val j.val)
      (fun i : Fin 3 => -u.val (coordinatePivot i)) = u.val := by
  funext j
  by_cases hj : ¬∃ i : Fin 8, globalPivot i = j
  · exact embedGlobalCoordinates_free _ _ ⟨j,hj⟩
  · obtain ⟨i,rfl⟩ := not_not.mp hj
    rcases globalPivot_partition i with ⟨c,hc⟩ | ⟨e,he⟩
    · rw [hc, embedGlobalCoordinates_coordinate, neg_neg]
    · rw [he, embedGlobalCoordinates_equation, u.property e]

/-- The linear coordinate slice is exactly A54 × A3, with signs arranged so
the last three coordinates are A,B,C rather than their negatives. -/
def zeroEquationSliceEquiv : ZeroEquationSlice (K := K) ≃
    ((RemainingCoordinate → K) × (Fin 3 → K)) where
  toFun u := (fun j => u.val j.val, fun i => -u.val (coordinatePivot i))
  invFun x := ⟨embedGlobalCoordinates x.1 x.2, embedGlobalCoordinates_equation x.1 x.2⟩
  left_inv u := Subtype.ext (embedGlobalCoordinates_unique u)
  right_inv x := by
    apply Prod.ext
    · funext j
      exact embedGlobalCoordinates_free x.1 x.2 j
    · funext i
      change -embedGlobalCoordinates x.1 x.2 (coordinatePivot i) = x.2 i
      rw [embedGlobalCoordinates_coordinate, neg_neg]

end Ring
section Field
variable {K : Type*} [Field K]

/-- Restriction of the proved ambient polynomial automorphism to the genuine
semigroup-defined normal-form variety. -/
def parameterZeroSliceEquiv : ParameterSpace (K := K) ≃ ZeroEquationSlice (K := K) where
  toFun p := ⟨globalAmbientEquiv p.val, by
    intro i
    rw [globalAmbientEquiv_equation, parameterSpace_definingEquations p i, neg_zero]⟩
  invFun u := ⟨globalAmbientEquiv.symm u.val, by
    apply (parameter_condition_iff_equations _).mpr
    intro i
    have h := globalAmbientEquiv_equation (globalAmbientEquiv.symm u.val) i
    rw [Equiv.apply_symm_apply, u.property i] at h
    exact neg_eq_zero.mp h.symm⟩
  left_inv p := Subtype.ext (globalAmbientEquiv.symm_apply_apply p.val)
  right_inv u := Subtype.ext (globalAmbientEquiv.apply_symm_apply u.val)

/-- The genuine global affine coordinate equivalence. -/
def parameterGlobalEquiv : ParameterSpace (K := K) ≃
    ((RemainingCoordinate → K) × (Fin 3 → K)) :=
  parameterZeroSliceEquiv.trans zeroEquationSliceEquiv

theorem parameterGlobalEquiv_q (p : ParameterSpace (K := K)) (j : RemainingCoordinate) :
    (parameterGlobalEquiv p).1 j = p.val j.val :=
  PolynomialTriangular.forward_free globalTriangularData p.val j.val j.property

theorem parameterGlobalEquiv_ABC (p : ParameterSpace (K := K)) (i : Fin 3) :
    (parameterGlobalEquiv p).2 i = relationCoordinate p.val i := by
  change -globalAmbientEquiv p.val (coordinatePivot i) = _
  rw [globalAmbientEquiv_coordinate, neg_neg]

open scoped PowerSeries.WithPiTopology
variable [TopologicalSpace K] [DiscreteTopology K]

/-- In particular the global coordinates classify actual complete embedded
subalgebras of the power-series ring. -/
def completeGammaGlobalEquiv : CompleteGammaSubalgebra (K := K) ≃
    ((RemainingCoordinate → K) × (Fin 3 → K)) :=
  completeGammaParameterEquiv.trans parameterGlobalEquiv

end Field
end EmbeddingDimensionStrata
