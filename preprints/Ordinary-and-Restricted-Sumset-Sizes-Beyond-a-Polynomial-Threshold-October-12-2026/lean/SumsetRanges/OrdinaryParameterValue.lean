import SumsetRanges.OrdinaryWeights
import SumsetRanges.ParameterValue

open Finset
namespace SumsetRanges

noncomputable def ordinaryCaps (h c b : ℕ) :=
  parameterCaps (h-1) (repetitionCap c) (sharedCap c) (denseWidth h b)

noncomputable def ordinaryParameterValue (h c b : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ) : ℤ :=
  ordinaryValue h c b (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (denseMaximum h b-v (denseIndex (h-1)))

theorem ordinary_parameter_dense_bounds (h b : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 1≤h) (hb : 2≤b) (hv : v (denseIndex (h-1))≤denseWidth h b) :
    b-1≤denseMaximum h b-v (denseIndex (h-1)) := by
  have hm := denseMaximum_ge h b hh hb
  unfold denseWidth at hv
  omega

@[simp] theorem ordinaryParameterValue_update_repetition (h c b m a : ℕ)
    (v : Fin (parameterDimension (h-1)) → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) m hm) a)=
      ordinaryValue h c b (Function.update (repetitionParameters (h-1) v) m a) (sharedParameters (h-1) v)
        (denseMaximum h b-v (denseIndex (h-1))) := by
  simp only [ordinaryParameterValue,repetitionParameters_update_repetition,sharedParameters_update_repetition,
    Function.update_of_ne (repetitionIndex_ne_dense (h-1) m hm).symm]

@[simp] theorem ordinaryParameterValue_update_shared (h c b m a : ℕ)
    (v : Fin (parameterDimension (h-1)) → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) m hm) a)=
      ordinaryValue h c b (repetitionParameters (h-1) v) (Function.update (sharedParameters (h-1) v) m (a+1))
        (denseMaximum h b-v (denseIndex (h-1))) := by
  simp only [ordinaryParameterValue,repetitionParameters_update_shared,sharedParameters_update_shared,
    Function.update_of_ne (sharedIndex_ne_dense (h-1) m hm).symm]

@[simp] theorem ordinaryParameterValue_update_dense (h c b a : ℕ)
    (v : Fin (parameterDimension (h-1)) → ℕ) :
    ordinaryParameterValue h c b (Function.update v (denseIndex (h-1)) a)=
      ordinaryValue h c b (repetitionParameters (h-1) v) (sharedParameters (h-1) v) (denseMaximum h b-a) := by
  simp only [ordinaryParameterValue,repetitionParameters_update_dense,sharedParameters_update_dense,Function.update_self]

end SumsetRanges
