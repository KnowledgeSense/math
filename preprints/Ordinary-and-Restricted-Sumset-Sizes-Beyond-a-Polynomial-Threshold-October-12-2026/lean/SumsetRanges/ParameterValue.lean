import SumsetRanges.ParameterCoordinates
import SumsetRanges.BoxMonotonicity

open Finset
namespace SumsetRanges
open scoped Classical

def denseMaximum (h b : ℕ) := h*(b-2)+1
def denseWidth (h b : ℕ) := denseMaximum h b-(b-1)
noncomputable def parameterValue (h c b : ℕ) (v : Fin (parameterDimension h) → ℕ) : ℤ :=
  largeValue h c b (repetitionParameters h v) (sharedParameters h v)
    (denseMaximum h b-v (denseIndex h))

theorem denseMaximum_ge (h b : ℕ) (hh : 1≤h) (hb : 2≤b) : b-1≤denseMaximum h b := by
  have hm := Nat.le_mul_of_pos_left (b-2) hh
  unfold denseMaximum
  omega

theorem parameter_dense_bounds (h b : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 1≤h) (hb : 2≤b) (hv : v (denseIndex h)≤denseWidth h b) :
    b-1≤denseMaximum h b-v (denseIndex h) := by
  have hm := denseMaximum_ge h b hh hb
  unfold denseWidth at hv
  omega

@[simp] theorem parameterValue_update_repetition (h c b μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    parameterValue h c b (Function.update v (repetitionIndex h μ hm) a)=
      largeValue h c b (Function.update (repetitionParameters h v) μ a) (sharedParameters h v)
        (denseMaximum h b-v (denseIndex h)) := by
  simp only [parameterValue,repetitionParameters_update_repetition,sharedParameters_update_repetition,
    Function.update_of_ne (repetitionIndex_ne_dense h μ hm).symm]

@[simp] theorem parameterValue_update_shared (h c b μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    parameterValue h c b (Function.update v (sharedIndex h μ hm) a)=
      largeValue h c b (repetitionParameters h v) (Function.update (sharedParameters h v) μ (a+1))
        (denseMaximum h b-v (denseIndex h)) := by
  simp only [parameterValue,repetitionParameters_update_shared,sharedParameters_update_shared,
    Function.update_of_ne (sharedIndex_ne_dense h μ hm).symm]

@[simp] theorem parameterValue_update_dense (h c b a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) :
    parameterValue h c b (Function.update v (denseIndex h) a)=
      largeValue h c b (repetitionParameters h v) (sharedParameters h v) (denseMaximum h b-a) := by
  simp only [parameterValue,repetitionParameters_update_dense,sharedParameters_update_dense,
    Function.update_self]

end SumsetRanges
