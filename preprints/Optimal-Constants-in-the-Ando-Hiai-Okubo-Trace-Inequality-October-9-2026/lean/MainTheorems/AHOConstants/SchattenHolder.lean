import MainTheorems.AHOConstants.TraceHolder
import MainTheorems.AHOConstants.SchattenTrace

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

structure SchattenFactor (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : Matrix I I ℂ
  weight : ℝ
  invertible : IsUnit matrix

noncomputable def SchattenFactor.asWeighted (f : SchattenFactor I) : WeightedFactor I where
  positiveMatrix := spectralPower (polarAbsolute f.matrix) (1 / f.weight)
  unitaryMatrix := polarUnitary f.matrix
  weight := f.weight
  positiveDefinite := spectralPower_posDef (polarAbsolute_posDef f.invertible) _
  unitaryMembership := polarUnitary_mem f.invertible

theorem SchattenFactor.asWeighted_value (f : SchattenFactor I) (hw : f.weight ≠ 0) :
    factorValue f.asWeighted = f.matrix := by
  unfold factorValue SchattenFactor.asWeighted
  rw [spectralPower_iterate (polarAbsolute_posDef f.invertible) _ _
    (one_div_ne_zero hw), one_div_mul_cancel hw,
    spectralPower_one _ (polarAbsolute_posDef f.invertible).posSemidef]
  exact (polar_decomposition f.invertible).symm

theorem SchattenFactor.asWeighted_bound (f : SchattenFactor I) :
    factorBound f.asWeighted = schattenNorm (1 / f.weight) f.matrix := by
  unfold factorBound SchattenFactor.asWeighted schattenNorm
  rw [one_div_one_div, schattenPower_eq_absolute_trace f.invertible]

theorem schatten_list_trace_holder [Nonempty I] (fs : List (SchattenFactor I))
    (hpos : ∀ f ∈ fs, 0 < f.weight)
    (hsum : (fs.map SchattenFactor.weight).sum = 1) :
    ‖Matrix.trace ((fs.map SchattenFactor.matrix).prod)‖ ≤
      (fs.map (fun f => schattenNorm (1 / f.weight) f.matrix)).prod := by
  have hwp : ∀ f ∈ fs.map SchattenFactor.asWeighted, 0 < f.weight := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hpos g hg
  have hws : totalWeight (fs.map SchattenFactor.asWeighted) = 1 := by
    simpa only [totalWeight, List.map_map, Function.comp_def,
      SchattenFactor.asWeighted] using hsum
  have h := weighted_positive_trace_bound (fs.map SchattenFactor.asWeighted) hwp hws
    ((unitary (Matrix I I ℂ)).one_mem)
  have hp : weightedProduct (fs.map SchattenFactor.asWeighted) =
      (fs.map SchattenFactor.matrix).prod := by
    unfold weightedProduct
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro f hf
    exact f.asWeighted_value (hpos f hf).ne'
  have hb : weightedBound (fs.map SchattenFactor.asWeighted) =
      (fs.map (fun f => schattenNorm (1 / f.weight) f.matrix)).prod := by
    unfold weightedBound
    simp only [List.map_map, Function.comp_def, SchattenFactor.asWeighted_bound]
  simpa only [Matrix.one_mul, hp, hb] using h

end ResearchMain.AHOConstants
