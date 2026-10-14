import EmbeddingDimensionStrata.PolynomialOpenObstructions
import EmbeddingDimensionStrata.SchemeCoordinates

/-! # Obstructions quantified over all regular functions on the actual affine variety -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- A principal open for an arbitrary element of the actual quotient
coordinate ring, evaluated at the genuine parameter point. -/
def parameterRegularPrincipalOpen (h : ParameterCoordinateRing K) : Set (ParameterSpace (K := K)) :=
  {p | parameterPointEvaluation K p h ≠ 0}

@[simp]
theorem parameterRegularPrincipalOpen_mk (f : MvPolynomial NormalCoordinate K) :
    parameterRegularPrincipalOpen (Ideal.Quotient.mk (parameterDefiningIdeal K) f) =
      parameterPrincipalOpen f := rfl

/-- Every regular function is covered, since every element of the true
coordinate ring has an ambient polynomial representative. -/
theorem generatorStratum_four_regular_cover_lower_bound [IsAlgClosed K] (r : ℕ)
    (h : Fin r → ParameterCoordinateRing K)
    (hh : generatorStratum 4 = ⋃ i, parameterRegularPrincipalOpen (h i)) : 3 ≤ r := by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (h i)
  apply generatorStratum_four_principal_cover_lower_bound r f
  simpa only [← hf, parameterRegularPrincipalOpen_mk] using hh

theorem generatorStratum_four_not_regular_principal [IsAlgClosed K]
    (h : ParameterCoordinateRing K) : generatorStratum 4 ≠ parameterRegularPrincipalOpen h := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective h
  exact generatorStratum_four_not_principal_open f

theorem generatorStratum_four_not_two_regular_principals [IsAlgClosed K]
    (h₁ h₂ : ParameterCoordinateRing K) :
    generatorStratum 4 ≠ parameterRegularPrincipalOpen h₁ ∪ parameterRegularPrincipalOpen h₂ := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective h₁
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective h₂
  exact generatorStratum_four_not_two_principal_opens f g

theorem generatorStratum_four_three_regular_principals :
    generatorStratum (K := K) 4 = ⋃ i : Fin 3, parameterRegularPrincipalOpen (parameterRelationClass K i) := by
  change generatorStratum (K := K) 4 = ⋃ i : Fin 3,
    parameterRegularPrincipalOpen (Ideal.Quotient.mk (parameterDefiningIdeal K)
      (MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i)))
  simp only [parameterRegularPrincipalOpen_mk]
  exact generatorStratum_four_three_principal_opens

/-- Exactly three opens are required even when one allows arbitrary regular
functions of the actual affine variety, not just a displayed polynomial list. -/
theorem generatorStratum_four_minimal_regular_cover [IsAlgClosed K] :
    IsLeast {r : ℕ | ∃ h : Fin r → ParameterCoordinateRing K,
      generatorStratum 4 = ⋃ i, parameterRegularPrincipalOpen (h i)} 3 := by
  constructor
  · exact ⟨parameterRelationClass K, generatorStratum_four_three_regular_principals⟩
  · rintro r ⟨h,hh⟩
    exact generatorStratum_four_regular_cover_lower_bound r h hh

end EmbeddingDimensionStrata
