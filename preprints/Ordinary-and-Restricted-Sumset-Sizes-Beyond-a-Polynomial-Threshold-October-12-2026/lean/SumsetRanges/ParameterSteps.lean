import SumsetRanges.ParameterValue

open Finset
set_option maxHeartbeats 2000000
namespace SumsetRanges
open scoped Classical

noncomputable def admissibleCaps (h c b : ℕ) := parameterCaps h (repetitionCap c) (sharedCap c) (denseWidth h b)

theorem parameter_linear_step_bounds (h c b μ : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 h)
    (hv : InNatBox (admissibleCaps h c b) v)
    (hi : v (repetitionIndex h μ hm)<repetitionCap c) :
    restrictedWeight c b (h-μ)≤2*(parameterValue h c b v-
      parameterValue h c b (Function.update v (repetitionIndex h μ hm) (v (repetitionIndex h μ hm)+1))) ∧
    parameterValue h c b v-
      parameterValue h c b (Function.update v (repetitionIndex h μ hm) (v (repetitionIndex h μ hm)+1))≤
      2*restrictedWeight c b (h-μ) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds h (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := linear_step_box_bound h c μ (repetitionParameters h v) (sharedParameters h v)
    (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
    (by simpa only [repetitionParameters_at h μ v hm] using hi)
  have hx := parameter_dense_bounds h b v (by omega) hb hbds.2.2
  have hch := (large_c_elementary (h := h) (c := c) (by omega) hc).2
  have he := largeValue_linear_step h c b _ μ (repetitionParameters h v) (sharedParameters h v)
    (by omega) hch hb hx hm hnu
  rw [parameterValue_update_repetition]
  simpa only [parameterValue,repetitionParameters_at h μ v hm] using he

theorem parameter_shared_step_bounds (h c b μ : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 h)
    (hv : InNatBox (admissibleCaps h c b) v)
    (hi : v (sharedIndex h μ hm)<sharedCap c-1) :
    ((v (sharedIndex h μ hm) : ℤ)+1)*restrictedWeight c b (h-μ)≤2*(parameterValue h c b v-
      parameterValue h c b (Function.update v (sharedIndex h μ hm) (v (sharedIndex h μ hm)+1))) ∧
    parameterValue h c b v-
      parameterValue h c b (Function.update v (sharedIndex h μ hm) (v (sharedIndex h μ hm)+1))≤
      2*((v (sharedIndex h μ hm) : ℤ)+1)*restrictedWeight c b (h-μ) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds h (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := shared_step_box_bound h c μ (repetitionParameters h v) (sharedParameters h v)
    (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
    (by rw [sharedParameters_at h μ v hm]; omega)
  have hx := parameter_dense_bounds h b v (by omega) hb hbds.2.2
  have hch := (large_c_elementary (h := h) (c := c) (by omega) hc).2
  have he := largeValue_shared_step h c b _ μ (repetitionParameters h v) (sharedParameters h v)
    (by omega) hch hb hx hm (hbds.2.1 μ hm).1 hnu
  rw [parameterValue_update_shared]
  simpa only [parameterValue,sharedParameters_at h μ v hm,
    Nat.cast_add,Nat.cast_one] using he

theorem parameter_dense_step_bounds (h c b : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hv : InNatBox (admissibleCaps h c b) v)
    (hi : v (denseIndex h)<denseWidth h b) :
    0≤parameterValue h c b v-
      parameterValue h c b (Function.update v (denseIndex h) (v (denseIndex h)+1)) ∧
    parameterValue h c b v-
      parameterValue h c b (Function.update v (denseIndex h) (v (denseIndex h)+1))≤
      2*(c.choose (h-2) : ℤ) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds h (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := nonfreeSize_box_bound h c (repetitionParameters h v) (sharedParameters h v)
    (by omega) hc hbds.1 (fun m hm => (hbds.2.1 m hm).2)
  have hN : nonfreeSize h (repetitionParameters h v) (sharedParameters h v)≤c := by
    have ht := Nat.le_mul_of_pos_left (nonfreeSize h (repetitionParameters h v) (sharedParameters h v))
      (by omega : 0<8*h)
    omega
  have hm := denseMaximum_ge h b (by omega) hb
  have hx : b-1≤denseMaximum h b-(v (denseIndex h)+1) := by
    unfold denseWidth at hi
    omega
  have heq : denseMaximum h b-v (denseIndex h)=denseMaximum h b-(v (denseIndex h)+1)+1 := by
    unfold denseWidth at hi
    omega
  have hch := (large_c_elementary (h := h) (c := c) (by omega) hc).2
  have he := largeValue_dense_step h c b (denseMaximum h b-(v (denseIndex h)+1))
    (repetitionParameters h v) (sharedParameters h v) hh (by nlinarith) hb hx hN
  rw [parameterValue_update_dense]
  simpa only [parameterValue,heq] using he

end SumsetRanges
