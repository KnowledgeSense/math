import EmbeddingDimensionStrata.CoordinateRingIsomorphism
import EmbeddingDimensionStrata.GeometryObstructions

/-! # Scheme-level affine coordinates and the actual fourth open stratum -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace EmbeddingDimensionStrata
open AlgebraicGeometry CategoryTheory TopologicalSpace

section Ring
variable (K : Type*) [CommRing K]

/-- The affine scheme of the actual five normal-form equations. -/
abbrev parameterScheme : Scheme := Spec (CommRingCat.of (ParameterCoordinateRing K))

/-- The genuine scheme isomorphism induced by the proved coordinate-ring equivalence. -/
def parameterSchemeIso : parameterScheme K ≅ Spec (CommRingCat.of (AffineCoordinateRing K)) :=
  Scheme.Spec.mapIso (parameterCoordinateRingEquiv K).toRingEquiv.symm.toCommRingCatIso.op

/-- The classes of the actual reduction coefficients A,B,C in the equation ring. -/
def parameterRelationClass (i : Fin 3) : ParameterCoordinateRing K :=
  Ideal.Quotient.mk (parameterDefiningIdeal K)
    (MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i))

/-- The actual open rank-at-least-one locus of the cotangent relation matrix. -/
def parameterFourStratumOpen : (parameterScheme K).Opens :=
  ⨆ i : Fin 3, PrimeSpectrum.basicOpen (parameterRelationClass K i)

@[simp] theorem affineToParameterRing_right (i : Fin 3) :
    affineToParameterRing K (MvPolynomial.X (Sum.inr i)) = parameterRelationClass K i := by
  rw [affineToParameterRing_X]
  change relationCoordinate (universalParameterPoint K) i = _
  rw [← eval_relationCoordinatePolynomial, ← aeval_integralPolynomial (K := K),
    aeval_universalParameterPoint]
  rfl

end Ring
section Field
variable (K : Type*) [Field K]

/-- The scheme isomorphism takes the true union D(A) ∪ D(B) ∪ D(C) to the
punctured affine product, not merely its rational-point set. -/
theorem parameterSchemeIso_preimage_punctured :
    (parameterSchemeIso K).hom ⁻¹ᵁ GeometryObstructions.puncturedProductSchemeOpen K 54 =
      parameterFourStratumOpen K := by
  unfold GeometryObstructions.puncturedProductSchemeOpen parameterFourStratumOpen
  rw [Scheme.Hom.preimage_iSup]
  congr 1
  funext i
  ext x
  change affineToParameterRing K (MvPolynomial.X (Sum.inr i)) ∉ x.asIdeal ↔
    parameterRelationClass K i ∉ x.asIdeal
  rw [affineToParameterRing_right]

/-- An actual isomorphism of the open subschemes, including their structure sheaves. -/
def parameterFourStratumSchemeIso :
    (parameterFourStratumOpen K).toScheme ≅
      (GeometryObstructions.puncturedProductSchemeOpen K 54).toScheme :=
  (parameterScheme K).isoOfEq (parameterSchemeIso_preimage_punctured K).symm ≪≫
    (parameterSchemeIso K).hom.preimageIso (GeometryObstructions.puncturedProductSchemeOpen K 54)

/-- Non-affineness transferred to the original five-equation scheme's fourth stratum. -/
theorem parameterFourStratumScheme_not_affine :
    ¬ IsAffine (parameterFourStratumOpen K).toScheme := by
  intro h
  let : IsAffine (parameterFourStratumOpen K).toScheme := h
  exact GeometryObstructions.puncturedProductScheme_not_affine K 54
    (IsAffine.of_isIso (parameterFourStratumSchemeIso K).inv)

/-- The fourth stratum of the actual normal-form scheme is not the proposed product. -/
theorem parameterFourStratum_not_iso_predicted :
    IsEmpty ((parameterFourStratumOpen K).toScheme ≅
      GeometryObstructions.predictedFourStratumScheme K) := by
  constructor
  intro e
  exact (GeometryObstructions.puncturedProduct54_not_iso_predicted K).false
    ((parameterFourStratumSchemeIso K).symm ≪≫ e)


/-- Evaluation at an actual semigroup-defined parameter point descends to the
original equation coordinate ring. -/
def parameterPointEvaluation (p : ParameterSpace (K := K)) : ParameterCoordinateRing K →ₐ[K] K :=
  Ideal.Quotient.liftₐ (parameterDefiningIdeal K) (MvPolynomial.aeval p.val) (by
    change parameterDefiningIdeal K ≤ RingHom.ker (MvPolynomial.aeval p.val).toRingHom
    apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    change MvPolynomial.aeval p.val (MvPolynomial.map (Int.castRingHom K) (definingPolynomial i)) = 0
    rw [aeval_integralPolynomial, eval_definingPolynomial]
    exact parameterSpace_definingEquations p i)

/-- The scheme point corresponding to the actual embedded subalgebra parameter. -/
def parameterPrime (p : ParameterSpace (K := K)) : PrimeSpectrum (ParameterCoordinateRing K) :=
  ⟨RingHom.ker (parameterPointEvaluation K p).toRingHom,
    RingHom.ker_isPrime (parameterPointEvaluation K p).toRingHom⟩

@[simp] theorem parameterPointEvaluation_relationClass
    (p : ParameterSpace (K := K)) (i : Fin 3) :
    parameterPointEvaluation K p (parameterRelationClass K i) = relationCoordinate p.val i := by
  change MvPolynomial.aeval p.val
    (MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i)) = _
  rw [aeval_integralPolynomial, eval_relationCoordinatePolynomial]

/-- The original scheme open has the expected A,B,C condition on actual parameters. -/
theorem parameterFourStratumOpen_parameterPrime (p : ParameterSpace (K := K)) :
    parameterPrime K p ∈ parameterFourStratumOpen K ↔
      ∃ i : Fin 3, relationCoordinate p.val i ≠ 0 := by
  simp only [parameterFourStratumOpen, Opens.mem_iSup, PrimeSpectrum.mem_basicOpen]
  change (∃ i : Fin 3, ¬parameterPointEvaluation K p (parameterRelationClass K i) = 0) ↔ _
  simp only [parameterPointEvaluation_relationClass]

/-- Transport of actual structure-sheaf sections along the open-scheme isomorphism. -/
def parameterFourStratumSectionsIso :
    Γ(Spec (CommRingCat.of (AffineCoordinateRing K)), GeometryObstructions.puncturedProductSchemeOpen K 54) ≅
      Γ(parameterScheme K, parameterFourStratumOpen K) :=
  (GeometryObstructions.puncturedProductSchemeOpen K 54).topIso.symm ≪≫
    Scheme.Γ.mapIso (parameterFourStratumSchemeIso K).op ≪≫
      (parameterFourStratumOpen K).topIso

/-- The actual regular-function ring of the fourth stratum is a polynomial ring. -/
def parameterFourStratum_regularFunctionsEquiv :
    AffineCoordinateRing K ≃+* Γ(parameterScheme K, parameterFourStratumOpen K) :=
  (GeometryObstructions.puncturedProduct_regularFunctionsEquiv K 54).trans
    (parameterFourStratumSectionsIso K).commRingCatIsoToRingEquiv

/-- All invertible regular functions correspond precisely to nonzero scalar
polynomials under the actual structure-sheaf coordinate isomorphism. -/
theorem parameterFourStratum_regular_units
    (s : Γ(parameterScheme K, parameterFourStratumOpen K)) :
    IsUnit s ↔ ∃ c : K, c ≠ 0 ∧
      parameterFourStratum_regularFunctionsEquiv K (MvPolynomial.C c) = s := by
  let e := parameterFourStratum_regularFunctionsEquiv K
  constructor
  · intro hs
    obtain ⟨c,hc,he⟩ := (GeometryObstructions.polynomial_units_are_constants (e.symm s)).mp
      (hs.map e.symm.toMonoidHom)
    refine ⟨c,hc,?_⟩
    change e (MvPolynomial.C c) = s
    rw [← he, e.apply_symm_apply]
  · rintro ⟨c,hc,rfl⟩
    exact ((GeometryObstructions.polynomial_units_are_constants
      (MvPolynomial.C c : AffineCoordinateRing K)).mpr ⟨c,hc,rfl⟩).map e.toMonoidHom

end Field
end EmbeddingDimensionStrata
