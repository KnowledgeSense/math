import EmbeddingDimensionStrata.MainResults

/-! # Public regression examples on genuine subalgebra points -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

def stratumPoint (a b c : K) : ParameterSpace (K := K) :=
  parameterAffineEquiv.symm (Sum.elim (fun _ => 0) ![a,b,c])

theorem stratumPoint_coordinates (a b c : K) (i : Fin 3) :
    relationCoordinate (stratumPoint a b c).val i = ![a,b,c] i := by
  have hh := congrFun (parameterAffineEquiv.apply_symm_apply (Sum.elim (fun _ : Fin 54 => 0) ![a,b,c]))
    (Sum.inr i)
  rw [parameterAffineEquiv_ABC] at hh
  exact hh

example : embeddingDimension (stratumPoint (0 : K) 0 0) = 5 := by
  apply (embeddingDimension_eq_five _).mpr
  simp [stratumPoint_coordinates]

example : embeddingDimension (stratumPoint (1 : K) 1 0) = 3 := by
  apply (embeddingDimension_eq_three _).mpr
  simp [stratumPoint_coordinates]

example : embeddingDimension (stratumPoint (0 : K) 0 1) = 4 := by
  apply (embeddingDimension_eq_four _).mpr
  simp [stratumPoint_coordinates]

example (f : MvPolynomial (Fin 5) ℂ) :
    ¬ ∀ p : ParameterSpace (K := ℂ), p ∈ generatorStratum 4 ↔
      HasOrder (partialReduceSeries p.val 60 (generatorEvaluation (RingHom.id ℂ) p.val f)) 58 :=
  no_fixed_polynomial_reduction_detector f

example : SimplyConnectedSpace (generatorStratum (K := ℂ) 4) :=
  generatorStratum_four_simplyConnected

end EmbeddingDimensionStrata
