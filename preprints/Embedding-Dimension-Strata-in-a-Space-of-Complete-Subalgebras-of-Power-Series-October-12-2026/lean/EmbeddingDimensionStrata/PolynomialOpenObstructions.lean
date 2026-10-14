import EmbeddingDimensionStrata.EmbeddingStrata
import EmbeddingDimensionStrata.GeometryObstructions

/-! # Polynomial-open obstructions on the actual subalgebra parameter space -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- Pull a polynomial on the original 62 coefficients back through the
proved polynomial inverse of the genuine affine coordinate isomorphism. -/
def affinePullback : MvPolynomial NormalCoordinate K →ₐ[K] MvPolynomial AffineCoordinate K :=
  MvPolynomial.aeval (affineInversePoint MvPolynomial.X)

theorem eval_affinePullback (f : MvPolynomial NormalCoordinate K) (x : AffineCoordinate → K) :
    MvPolynomial.aeval x (affinePullback f) =
      MvPolynomial.aeval (parameterAffineEquiv.symm x).val f := by
  have hm (j : NormalCoordinate) :
      MvPolynomial.aeval x (affineInversePoint (MvPolynomial.X : AffineCoordinate → MvPolynomial AffineCoordinate K) j) = affineInversePoint x j := by
    have hh := map_affineInversePoint (MvPolynomial.aeval x).toRingHom
      (MvPolynomial.X : AffineCoordinate → MvPolynomial AffineCoordinate K) j
    have he : (fun i : AffineCoordinate => (MvPolynomial.aeval x).toRingHom (MvPolynomial.X i : MvPolynomial AffineCoordinate K)) = x := by
      funext i; exact MvPolynomial.aeval_X x i
    rw [he] at hh
    exact hh
  have he : (MvPolynomial.aeval x).comp (affinePullback (K := K)) =
      MvPolynomial.aeval (affineInversePoint x) := by
    ext j : 1
    simp only [AlgHom.comp_apply, affinePullback, MvPolynomial.aeval_X, hm]
  exact congrArg (fun F : MvPolynomial NormalCoordinate K →ₐ[K] K => F f) he

/-- Principal open defined by an arbitrary regular polynomial in the original
normal-form coefficients. -/
def parameterPrincipalOpen (f : MvPolynomial NormalCoordinate K) : Set (ParameterSpace (K := K)) :=
  {p | MvPolynomial.aeval p.val f ≠ 0}

theorem generatorStratum_four_principal_cover_lower_bound [IsAlgClosed K] (r : ℕ)
    (f : Fin r → MvPolynomial NormalCoordinate K)
    (hf : generatorStratum (K := K) 4 = ⋃ i, parameterPrincipalOpen (f i)) : 3 ≤ r := by
  apply GeometryObstructions.puncturedProduct_principal_cover_lower_bound 54 r (fun i => affinePullback (f i))
  ext x
  have hh := Set.ext_iff.mp hf (parameterAffineEquiv.symm x)
  rw [generatorStratum_four_coordinates] at hh
  simp only [Equiv.apply_symm_apply] at hh
  simpa only [GeometryObstructions.puncturedProduct, GeometryObstructions.polynomialPrincipalOpen,
    Set.mem_ofPred_eq, Set.mem_iUnion, parameterPrincipalOpen, eval_affinePullback] using hh

theorem generatorStratum_four_not_principal_open [IsAlgClosed K]
    (f : MvPolynomial NormalCoordinate K) : generatorStratum 4 ≠ parameterPrincipalOpen f := by
  intro hf
  have he : generatorStratum 4 = ⋃ _ : Fin 1, parameterPrincipalOpen f := by
    rw [hf]
    ext p
    simp only [Set.mem_iUnion]
    exact ⟨fun hp => ⟨0,hp⟩, fun ⟨_,hp⟩ => hp⟩
  have hh := generatorStratum_four_principal_cover_lower_bound 1 (fun _ => f) he
  omega

theorem generatorStratum_four_not_two_principal_opens [IsAlgClosed K]
    (f g : MvPolynomial NormalCoordinate K) :
    generatorStratum 4 ≠ parameterPrincipalOpen f ∪ parameterPrincipalOpen g := by
  intro hf
  have he : generatorStratum 4 = ⋃ i : Fin 2, parameterPrincipalOpen (![f,g] i) := by
    rw [hf]
    ext p
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hp | hp)
      · exact ⟨0,hp⟩
      · exact ⟨1,hp⟩
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
  have hh := generatorStratum_four_principal_cover_lower_bound 2 ![f,g] he
  omega

theorem generatorStratum_four_three_principal_opens :
    generatorStratum (K := K) 4 = ⋃ i : Fin 3,
      parameterPrincipalOpen (MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i)) := by
  ext p
  rw [generatorStratum_four_iff]
  simp only [Set.mem_iUnion, parameterPrincipalOpen, Set.mem_ofPred_eq]
  apply exists_congr
  intro i
  have he : MvPolynomial.aeval p.val
      (MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i)) = relationCoordinate p.val i := by
    change MvPolynomial.eval p.val (MvPolynomial.map (Int.castRingHom K) _) = _
    rw [← MvPolynomial.eval₂_eq_eval_map, eval_relationCoordinatePolynomial]
  rw [he]

/-- Exactly three principal opens are necessary and sufficient on the actual
semigroup-defined variety, not just on an abstract affine surrogate. -/
theorem generatorStratum_four_minimal_principal_cover [IsAlgClosed K] :
    IsLeast {r : ℕ | ∃ f : Fin r → MvPolynomial NormalCoordinate K,
      generatorStratum (K := K) 4 = ⋃ i, parameterPrincipalOpen (f i)} 3 := by
  constructor
  · exact ⟨fun i => MvPolynomial.map (Int.castRingHom K) (relationCoordinatePolynomial i),
      generatorStratum_four_three_principal_opens⟩
  · rintro r ⟨f,hf⟩
    exact generatorStratum_four_principal_cover_lower_bound r f hf

end EmbeddingDimensionStrata
