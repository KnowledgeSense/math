import EmbeddingDimensionStrata.SchemeCoordinates

/-! # Units are canonical scalar sections on the original open subscheme -/
noncomputable section
namespace EmbeddingDimensionStrata
open AlgebraicGeometry CategoryTheory
variable (K : Type*) [Field K]

instance parameterFourSectionsAlgebra : Algebra (ParameterCoordinateRing K)
    Γ(parameterScheme K, parameterFourStratumOpen K) :=
  IsAffineOpen.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpens
    (R := CommRingCat.of (ParameterCoordinateRing K)) (U := parameterFourStratumOpen K)

theorem parameterCoordinateRingEquiv_relationClass (i : Fin 3) :
    parameterCoordinateRingEquiv K (parameterRelationClass K i) = MvPolynomial.X (Sum.inr i) := by
  rw [← affineToParameterRing_right]
  exact (parameterCoordinateRingEquiv K).apply_symm_apply _

/-- Canonical restriction, not an arbitrarily chosen ring isomorphism, is
bijective for regular functions on the actual four-generator stratum. -/
theorem parameterFour_canonical_sections_bijective :
    Function.Bijective (algebraMap (ParameterCoordinateRing K)
      Γ(parameterScheme K, parameterFourStratumOpen K)) := by
  let e := parameterCoordinateRingEquiv K
  let : IsDomain (ParameterCoordinateRing K) :=
    MulEquiv.isDomain (AffineCoordinateRing K) e.toRingEquiv.toMulEquiv
  have hA : Prime (parameterRelationClass K 0) := by
    apply (MulEquiv.prime_iff e).mp
    rw [parameterCoordinateRingEquiv_relationClass]
    exact MvPolynomial.X_prime
  have hB : parameterRelationClass K 1 ≠ 0 := by
    intro h
    have hh := congrArg e h
    rw [parameterCoordinateRingEquiv_relationClass, map_zero] at hh
    exact MvPolynomial.X_ne_zero _ hh
  have hAB : ¬ parameterRelationClass K 0 ∣ parameterRelationClass K 1 := by
    intro h
    have hh := map_dvd e.toRingHom h
    change parameterCoordinateRingEquiv K (parameterRelationClass K 0) ∣
      parameterCoordinateRingEquiv K (parameterRelationClass K 1) at hh
    rw [parameterCoordinateRingEquiv_relationClass,parameterCoordinateRingEquiv_relationClass,
      MvPolynomial.X_dvd_X] at hh
    exact (by decide : Sum.inr (0 : Fin 3) ≠ (Sum.inr 1 : AffineCoordinate)) hh
  exact GeometryObstructions.spec_sections_bijective_of_two_primes
    (CommRingCat.of (ParameterCoordinateRing K)) (parameterFourStratumOpen K)
    (parameterRelationClass K 0) (parameterRelationClass K 1) hA hB hAB
    (le_iSup (fun i : Fin 3 => PrimeSpectrum.basicOpen (parameterRelationClass K i)) 0)
    (le_iSup (fun i : Fin 3 => PrimeSpectrum.basicOpen (parameterRelationClass K i)) 1)

/-- The polynomial-ring description uses the canonical restriction map from
the original coordinate ring. -/
def parameterFour_canonical_regularFunctionsEquiv :
    AffineCoordinateRing K ≃+* Γ(parameterScheme K, parameterFourStratumOpen K) :=
  (parameterCoordinateRingEquiv K).symm.toRingEquiv.trans
    (RingEquiv.ofBijective (algebraMap (ParameterCoordinateRing K) _)
      (parameterFour_canonical_sections_bijective K))

/-- Constants in this explicit ring isomorphism are the canonical scalar
sections of the original open subscheme. -/
theorem parameterFour_canonical_regularFunctionsEquiv_C (c : K) :
    parameterFour_canonical_regularFunctionsEquiv K (MvPolynomial.C c) =
      algebraMap (ParameterCoordinateRing K) Γ(parameterScheme K, parameterFourStratumOpen K)
        (algebraMap K (ParameterCoordinateRing K) c) := by
  change algebraMap (ParameterCoordinateRing K) _
      ((parameterCoordinateRingEquiv K).symm (MvPolynomial.C c)) = _
  exact congrArg (algebraMap (ParameterCoordinateRing K)
    Γ(parameterScheme K, parameterFourStratumOpen K)) ((parameterCoordinateRingEquiv K).symm.commutes c)

/-- The literal constant-unit statement on the original structure sheaf. -/
theorem parameterFour_units_are_constant_sections
    (s : Γ(parameterScheme K, parameterFourStratumOpen K)) :
    IsUnit s ↔ ∃ c : K, c ≠ 0 ∧
      algebraMap (ParameterCoordinateRing K) Γ(parameterScheme K, parameterFourStratumOpen K)
        (algebraMap K (ParameterCoordinateRing K) c) = s := by
  let e := parameterFour_canonical_regularFunctionsEquiv K
  constructor
  · intro hs
    obtain ⟨c,hc,he⟩ := (GeometryObstructions.polynomial_units_are_constants (e.symm s)).mp
      (hs.map e.symm.toMonoidHom)
    refine ⟨c,hc,?_⟩
    rw [← parameterFour_canonical_regularFunctionsEquiv_C, ← he]
    exact e.apply_symm_apply s
  · rintro ⟨c,hc,rfl⟩
    exact (isUnit_iff_ne_zero.mpr hc).map
      ((algebraMap (ParameterCoordinateRing K) Γ(parameterScheme K, parameterFourStratumOpen K)).comp
        (algebraMap K (ParameterCoordinateRing K)))

end EmbeddingDimensionStrata
