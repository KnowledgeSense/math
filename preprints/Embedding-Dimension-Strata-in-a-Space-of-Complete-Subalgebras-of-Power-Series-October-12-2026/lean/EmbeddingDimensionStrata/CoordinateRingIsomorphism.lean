import EmbeddingDimensionStrata.GlobalPolynomialMaps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual five-equation coordinate ring is polynomial in 54+3 variables -/
noncomputable section
namespace EmbeddingDimensionStrata

section BaseChange
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Evaluation of an integral polynomial agrees with evaluation after base change. -/
theorem aeval_integralPolynomial {ι : Type*} (p : ι → A) (Q : MvPolynomial ι ℤ) :
    MvPolynomial.aeval p (MvPolynomial.map (Int.castRingHom K) Q) =
      MvPolynomial.eval₂ (Int.castRingHom A) p Q := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  ext z
  simp

/-- Naturality of the forward global polynomial coordinates over every ring. -/
theorem map_affineForwardPoint {L : Type*} [CommRing L] (φ : K →+* L)
    (p : NormalCoordinate → K) (i : AffineCoordinate) :
    φ (affineForwardPoint p i) = affineForwardPoint (fun j => φ (p j)) i := by
  cases i with
  | inl j => rfl
  | inr j =>
    change φ (relationCoordinate p j) = relationCoordinate (fun k => φ (p k)) j
    rw [← eval_relationCoordinatePolynomial p j,
      ← eval_relationCoordinatePolynomial (fun k => φ (p k)) j]
    exact map_evaluateCoordinatePolynomial φ p (relationCoordinatePolynomial j)

end BaseChange

variable (K : Type*) [CommRing K]

abbrev NormalCoordinateRing := MvPolynomial NormalCoordinate K
abbrev AffineCoordinateRing := MvPolynomial AffineCoordinate K

/-- The original five polynomial equations, base changed from their integral formulas. -/
def parameterDefiningIdeal : Ideal (NormalCoordinateRing K) :=
  Ideal.span (Set.range fun i : Fin 5 =>
    MvPolynomial.map (Int.castRingHom K) (definingPolynomial i))

/-- The actual coordinate ring of the normal-form equation scheme. -/
abbrev ParameterCoordinateRing := NormalCoordinateRing K ⧸ parameterDefiningIdeal K

/-- The universal normal-form coefficient tuple in the actual quotient ring. -/
def universalParameterPoint : NormalCoordinate → ParameterCoordinateRing K :=
  fun j => Ideal.Quotient.mk (parameterDefiningIdeal K) (MvPolynomial.X j)

/-- Evaluation at the universal point is the original quotient homomorphism. -/
theorem aeval_universalParameterPoint :
    MvPolynomial.aeval (universalParameterPoint K) = Ideal.Quotient.mkₐ K (parameterDefiningIdeal K) := by
  apply MvPolynomial.algHom_ext
  intro j
  exact MvPolynomial.aeval_X _ _

/-- Each of the five equations vanishes in the actual quotient, by ideal membership. -/
theorem universalParameterPoint_equations (i : Fin 5) :
    definingEquation (universalParameterPoint K) i = 0 := by
  rw [← eval_definingPolynomial, ← aeval_integralPolynomial (K := K), aeval_universalParameterPoint]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_range_self i)

/-- The inverse polynomial coordinate map, evaluated universally. -/
def parameterToAffinePolynomial : NormalCoordinateRing K →ₐ[K] AffineCoordinateRing K :=
  MvPolynomial.aeval (affineInversePoint (MvPolynomial.X : AffineCoordinate → AffineCoordinateRing K))

theorem parameterDefiningIdeal_le_ker :
    parameterDefiningIdeal K ≤ RingHom.ker (parameterToAffinePolynomial K).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨i,rfl⟩
  change MvPolynomial.aeval _ (MvPolynomial.map (Int.castRingHom K) (definingPolynomial i)) = 0
  rw [aeval_integralPolynomial, eval_definingPolynomial]
  exact affineInverse_equations _ i

/-- The map descends because all five original equations have been proved to vanish. -/
def parameterToAffineRing : ParameterCoordinateRing K →ₐ[K] AffineCoordinateRing K :=
  Ideal.Quotient.liftₐ (parameterDefiningIdeal K) (parameterToAffinePolynomial K)
    (parameterDefiningIdeal_le_ker K)

/-- The reverse map uses the actual 54 retained coefficients and A,B,C. -/
def affineToParameterRing : AffineCoordinateRing K →ₐ[K] ParameterCoordinateRing K :=
  MvPolynomial.aeval (affineForwardPoint (universalParameterPoint K))

@[simp] theorem parameterToAffineRing_universal (j : NormalCoordinate) :
    parameterToAffineRing K (universalParameterPoint K j) =
      affineInversePoint (MvPolynomial.X : AffineCoordinate → AffineCoordinateRing K) j := by
  change MvPolynomial.aeval _ (MvPolynomial.X j) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem affineToParameterRing_X (i : AffineCoordinate) :
    affineToParameterRing K (MvPolynomial.X i) = affineForwardPoint (universalParameterPoint K) i :=
  MvPolynomial.aeval_X _ _

/-- The composite is the identity on the polynomial ring in 57 actual coordinates. -/
theorem parameterToAffine_comp_affineToParameter :
    (parameterToAffineRing K).comp (affineToParameterRing K) = AlgHom.id K (AffineCoordinateRing K) := by
  apply MvPolynomial.algHom_ext
  intro i
  change parameterToAffineRing K (affineToParameterRing K (MvPolynomial.X i)) = MvPolynomial.X i
  rw [affineToParameterRing_X]
  change (parameterToAffineRing K).toRingHom (affineForwardPoint (universalParameterPoint K) i) = _
  rw [map_affineForwardPoint]
  change affineForwardPoint (fun j => parameterToAffineRing K (universalParameterPoint K j)) i = _
  simp only [parameterToAffineRing_universal]
  exact congrFun (affineForward_inverse (MvPolynomial.X : AffineCoordinate → AffineCoordinateRing K)) i

/-- The other composite is the identity on the actual five-equation quotient. -/
theorem affineToParameter_comp_parameterToAffine :
    (affineToParameterRing K).comp (parameterToAffineRing K) = AlgHom.id K (ParameterCoordinateRing K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  change affineToParameterRing K (parameterToAffineRing K (universalParameterPoint K j)) =
    universalParameterPoint K j
  rw [parameterToAffineRing_universal]
  change (affineToParameterRing K).toRingHom (affineInversePoint MvPolynomial.X j) = _
  rw [map_affineInversePoint]
  change affineInversePoint (fun i => affineToParameterRing K (MvPolynomial.X i)) j = _
  simp only [affineToParameterRing_X]
  exact congrFun (affineInverse_forward (universalParameterPoint K)
    (universalParameterPoint_equations K)) j

/-- The actual coordinate-ring isomorphism, over every commutative coefficient ring. -/
def parameterCoordinateRingEquiv : ParameterCoordinateRing K ≃ₐ[K] AffineCoordinateRing K :=
  AlgEquiv.ofAlgHom (parameterToAffineRing K) (affineToParameterRing K)
    (parameterToAffine_comp_affineToParameter K) (affineToParameter_comp_parameterToAffine K)

end EmbeddingDimensionStrata
