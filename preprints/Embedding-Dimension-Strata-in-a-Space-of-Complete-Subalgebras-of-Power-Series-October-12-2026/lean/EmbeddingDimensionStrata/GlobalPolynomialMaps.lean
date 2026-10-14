import EmbeddingDimensionStrata.GlobalParameters

/-! # Polynomial coordinates and polynomial inverse on the actual variety -/
noncomputable section
namespace EmbeddingDimensionStrata

def remainingCoordinateEquiv : RemainingCoordinate ≃ Fin 54 :=
  Fintype.equivFinOfCardEq remainingCoordinate_card

abbrev AffineCoordinate := Fin 54 ⊕ Fin 3

section Ring
variable {K : Type*} [CommRing K]

def affinePoint (q : RemainingCoordinate → K) (a : Fin 3 → K) : AffineCoordinate → K :=
  Sum.elim (fun i => q (remainingCoordinateEquiv.symm i)) a

def affineEmbed (x : AffineCoordinate → K) : NormalCoordinate → K :=
  embedGlobalCoordinates (fun j => x (Sum.inl (remainingCoordinateEquiv j))) (fun i => x (Sum.inr i))

def affineInversePoint (x : AffineCoordinate → K) : NormalCoordinate → K :=
  globalAmbientEquiv.symm (affineEmbed x)

theorem map_embedGlobalCoordinates {L : Type*} [CommRing L] (φ : K →+* L)
    (q : RemainingCoordinate → K) (a : Fin 3 → K) (j : NormalCoordinate) :
    φ (embedGlobalCoordinates q a j) =
      embedGlobalCoordinates (fun k => φ (q k)) (fun i => φ (a i)) j := by
  unfold embedGlobalCoordinates
  split_ifs <;> simp only [map_neg, map_zero]

theorem map_affineInversePoint {L : Type*} [CommRing L] (φ : K →+* L)
    (x : AffineCoordinate → K) (j : NormalCoordinate) :
    φ (affineInversePoint x j) = affineInversePoint (fun i => φ (x i)) j := by
  change φ (PolynomialTriangular.stage globalTriangularData (affineEmbed x) 8 j) = _
  have hh := congrFun (PolynomialTriangular.map_stage globalTriangularData φ (affineEmbed x) 8) j
  have he : (fun k => φ (affineEmbed x k)) = affineEmbed (fun i => φ (x i)) := by
    funext k
    exact map_embedGlobalCoordinates φ _ _ k
  rw [he] at hh
  exact hh

def affineForwardPolynomial (i : AffineCoordinate) : CoordinatePolynomial :=
  match i with
  | Sum.inl j => MvPolynomial.X (remainingCoordinateEquiv.symm j).val
  | Sum.inr j => relationCoordinatePolynomial j

def affineInversePolynomial (j : NormalCoordinate) : MvPolynomial AffineCoordinate ℤ :=
  affineInversePoint MvPolynomial.X j

theorem eval_affineInversePolynomial (x : AffineCoordinate → K) (j : NormalCoordinate) :
    MvPolynomial.eval₂ (Int.castRingHom K) x (affineInversePolynomial j) = affineInversePoint x j := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom K) x
  have hh := map_affineInversePoint φ (MvPolynomial.X : AffineCoordinate → MvPolynomial AffineCoordinate ℤ) j
  have he : (fun i => φ (MvPolynomial.X i)) = x := by funext i; exact MvPolynomial.eval₂_X _ _ i
  rw [he] at hh
  exact hh


def globalAffineEquiv : ((RemainingCoordinate → K) × (Fin 3 → K)) ≃ (AffineCoordinate → K) where
  toFun x := affinePoint x.1 x.2
  invFun x := (fun j => x (Sum.inl (remainingCoordinateEquiv j)),fun i => x (Sum.inr i))
  left_inv x := by
    apply Prod.ext
    · funext j
      exact congrArg x.1 (remainingCoordinateEquiv.symm_apply_apply j)
    · rfl
  right_inv x := by
    funext i
    cases i with
    | inl j => exact congrArg (fun k => x (Sum.inl k)) (remainingCoordinateEquiv.apply_symm_apply j)
    | inr j => rfl

def affineForwardPoint (p : NormalCoordinate → K) : AffineCoordinate → K :=
  affinePoint (fun j => p j.val) (relationCoordinate p)

theorem affineEmbed_affinePoint (q : RemainingCoordinate → K) (a : Fin 3 → K) :
    affineEmbed (affinePoint q a) = embedGlobalCoordinates q a := by
  unfold affineEmbed affinePoint
  simp only [Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]

theorem affineEmbed_forward (p : NormalCoordinate → K)
    (he : ∀ i : Fin 5, definingEquation p i = 0) :
    affineEmbed (affineForwardPoint p) = globalAmbientEquiv p := by
  let u : ZeroEquationSlice (K := K) := ⟨globalAmbientEquiv p,by
    intro i; rw [globalAmbientEquiv_equation, he i, neg_zero]⟩
  have hq : (fun j : RemainingCoordinate => u.val j.val) = (fun j => p j.val) := by
    funext j
    exact PolynomialTriangular.forward_free globalTriangularData p j.val j.property
  have ha : (fun i : Fin 3 => -u.val (coordinatePivot i)) = relationCoordinate p := by
    funext i
    change -globalAmbientEquiv p (coordinatePivot i) = _
    rw [globalAmbientEquiv_coordinate, neg_neg]
  have hh := embedGlobalCoordinates_unique u
  rw [hq,ha] at hh
  rw [affineForwardPoint,affineEmbed_affinePoint]
  exact hh

theorem affineInverse_forward (p : NormalCoordinate → K)
    (he : ∀ i : Fin 5, definingEquation p i = 0) :
    affineInversePoint (affineForwardPoint p) = p := by
  rw [affineInversePoint,affineEmbed_forward p he, Equiv.symm_apply_apply]

theorem affineInverse_equations (x : AffineCoordinate → K) (i : Fin 5) :
    definingEquation (affineInversePoint x) i = 0 := by
  have hh := globalAmbientEquiv_equation (affineInversePoint x) i
  change globalAmbientEquiv (globalAmbientEquiv.symm (affineEmbed x)) (eliminatedCoordinate i) = _ at hh
  rw [Equiv.apply_symm_apply] at hh
  change embedGlobalCoordinates _ _ (eliminatedCoordinate i) = _ at hh
  rw [embedGlobalCoordinates_equation] at hh
  exact neg_eq_zero.mp hh.symm

theorem affineForward_inverse (x : AffineCoordinate → K) :
    affineForwardPoint (affineInversePoint x) = x := by
  funext i
  cases i with
  | inl j =>
    have hh := PolynomialTriangular.forward_free globalTriangularData (affineInversePoint x)
      (remainingCoordinateEquiv.symm j).val (remainingCoordinateEquiv.symm j).property
    change globalAmbientEquiv (globalAmbientEquiv.symm (affineEmbed x))
      (remainingCoordinateEquiv.symm j).val = _ at hh
    rw [Equiv.apply_symm_apply] at hh
    change embedGlobalCoordinates _ _ (remainingCoordinateEquiv.symm j).val = _ at hh
    rw [embedGlobalCoordinates_free, remainingCoordinateEquiv.apply_symm_apply] at hh
    exact hh.symm
  | inr j =>
    have hh := globalAmbientEquiv_coordinate (affineInversePoint x) j
    change globalAmbientEquiv (globalAmbientEquiv.symm (affineEmbed x)) (coordinatePivot j) = _ at hh
    rw [Equiv.apply_symm_apply] at hh
    change embedGlobalCoordinates _ _ (coordinatePivot j) = _ at hh
    rw [embedGlobalCoordinates_coordinate] at hh
    exact neg_injective hh.symm

end Ring
section Field
variable {K : Type*} [Field K]

/-- The original semigroup-defined variety, in the 54+3 paper coordinates. -/
def parameterAffineEquiv : ParameterSpace (K := K) ≃ (AffineCoordinate → K) :=
  parameterGlobalEquiv.trans globalAffineEquiv

theorem parameterAffineEquiv_q (p : ParameterSpace (K := K)) (j : Fin 54) :
    parameterAffineEquiv p (Sum.inl j) = p.val (remainingCoordinateEquiv.symm j).val :=
  parameterGlobalEquiv_q p (remainingCoordinateEquiv.symm j)

theorem parameterAffineEquiv_ABC (p : ParameterSpace (K := K)) (i : Fin 3) :
    parameterAffineEquiv p (Sum.inr i) = relationCoordinate p.val i :=
  parameterGlobalEquiv_ABC p i

theorem parameterAffineEquiv_inverse_point (x : AffineCoordinate → K) :
    (parameterAffineEquiv.symm x).val = affineInversePoint x := rfl

/-- Every coordinate of the map from the actual variety is a polynomial. -/
theorem parameterAffineEquiv_polynomial (p : ParameterSpace (K := K)) (i : AffineCoordinate) :
    MvPolynomial.eval₂ (Int.castRingHom K) p.val (affineForwardPolynomial i) =
      parameterAffineEquiv p i := by
  cases i with
  | inl j => exact (MvPolynomial.eval₂_X _ _ _).trans (parameterAffineEquiv_q p j).symm
  | inr j => exact (eval_relationCoordinatePolynomial p.val j).trans (parameterAffineEquiv_ABC p j).symm

/-- Every normal-form coefficient of the inverse is a polynomial. -/
theorem parameterAffineEquiv_inverse_polynomial (x : AffineCoordinate → K) (j : NormalCoordinate) :
    MvPolynomial.eval₂ (Int.castRingHom K) x (affineInversePolynomial j) =
      (parameterAffineEquiv.symm x).val j := eval_affineInversePolynomial x j

end Field
end EmbeddingDimensionStrata
