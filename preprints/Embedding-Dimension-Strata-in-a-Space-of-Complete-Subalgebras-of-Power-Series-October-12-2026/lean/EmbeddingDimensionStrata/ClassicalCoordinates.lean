import EmbeddingDimensionStrata.EmbeddingStrata
import EmbeddingDimensionStrata.TopologyObstructions

/-! # Classical topology on the actual coefficient variety -/
noncomputable section
namespace EmbeddingDimensionStrata

/-- The classical coefficient-subspace topology, rather than a topology
transported through the theorem being proved. -/
instance parameterSpaceTopology {K : Type*} [Field K] [TopologicalSpace K] :
    TopologicalSpace (ParameterSpace (K := K)) :=
  TopologicalSpace.induced (fun p : ParameterSpace (K := K) => p.val) inferInstance

/-- Polynomiality gives continuity in the ordinary coefficient topology. -/
theorem continuous_integerPolynomial {ι : Type*} (Q : MvPolynomial ι ℤ) :
    Continuous (fun x : ι → ℂ => MvPolynomial.eval₂ (Int.castRingHom ℂ) x Q) := by
  simp_rw [MvPolynomial.eval₂_eq_eval_map]
  continuity

theorem continuous_parameterAffineEquiv : Continuous (parameterAffineEquiv (K := ℂ)) := by
  apply continuous_pi
  intro i
  have hv : Continuous (fun p : ParameterSpace (K := ℂ) => p.val) := continuous_induced_dom
  have hh := (continuous_integerPolynomial (affineForwardPolynomial i)).comp hv
  exact hh.congr (fun p => parameterAffineEquiv_polynomial p i)

theorem continuous_parameterAffineEquiv_symm : Continuous (parameterAffineEquiv (K := ℂ)).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact (continuous_integerPolynomial (affineInversePolynomial j)).congr
    (fun x => parameterAffineEquiv_inverse_polynomial x j)

/-- The actual semigroup-defined coefficient variety is homeomorphic to C^57,
by the same polynomial coordinates used for the algebraic isomorphism. -/
def parameterAffineHomeomorph : ParameterSpace (K := ℂ) ≃ₜ (AffineCoordinate → ℂ) where
  toEquiv := parameterAffineEquiv
  continuous_toFun := continuous_parameterAffineEquiv
  continuous_invFun := continuous_parameterAffineEquiv_symm

/-- Restriction of that actual homeomorphism to the true four-generator locus. -/
def generatorStratumFourHomeomorph : generatorStratum (K := ℂ) 4 ≃ₜ
    GeometryObstructions.puncturedProduct (K := ℂ) 54 where
  toEquiv := generatorStratumFourEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_parameterAffineEquiv.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_parameterAffineEquiv_symm.comp continuous_subtype_val

/-- The actual four-generator stratum is simply connected. -/
theorem generatorStratum_four_simplyConnected : SimplyConnectedSpace (generatorStratum (K := ℂ) 4) := by
  have := TopologyObstructions.puncturedProduct_simplyConnected 54
  exact generatorStratumFourHomeomorph.toHomotopyEquiv.simplyConnectedSpace

/-- The proposed C* × C^56 is not even homeomorphic to the actual stratum. -/
theorem generatorStratum_four_not_homeomorphic_predicted :
    IsEmpty (generatorStratum (K := ℂ) 4 ≃ₜ TopologyObstructions.ClassicalPredictedProduct 56) := by
  constructor
  intro e
  exact TopologyObstructions.puncturedCoordinates54_not_homeomorphic_predicted.false
    (generatorStratumFourHomeomorph.symm.trans e)

end EmbeddingDimensionStrata
