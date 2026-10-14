import SumsetRanges.OrdinaryParameterValue

open Finset
set_option maxHeartbeats 2000000
namespace SumsetRanges
open scoped Classical


theorem ordinary_parameter_linear_step_bounds (h c b μ : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 (h-1))
    (hv : InNatBox (ordinaryCaps h c b) v)
    (hi : v (repetitionIndex (h-1) μ hm)<repetitionCap c) :
    ordinaryWeight c b (h-(μ+1))≤2*(ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) μ hm) (v (repetitionIndex (h-1) μ hm)+1))) ∧
    ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) μ hm) (v (repetitionIndex (h-1) μ hm)+1))≤
      2*ordinaryWeight c b (h-(μ+1)) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds (h-1) (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := ordinary_linear_box_bound h c μ (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
    (by simpa only [repetitionParameters_at (h-1) μ v hm] using hi)
  have hx := ordinary_parameter_dense_bounds h b v (by omega) hb hbds.2.2
  have hch := ordinary_cubic_bound h c (by omega) hc
  have he := ordinaryValue_linear_step h c b _ μ (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hch hb hx (Nat.sub_le _ _) hm hnu
  rw [ordinaryParameterValue_update_repetition]
  simpa only [ordinaryParameterValue,repetitionParameters_at (h-1) μ v hm] using he

theorem ordinary_parameter_shared_step_bounds (h c b μ : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 (h-1))
    (hv : InNatBox (ordinaryCaps h c b) v)
    (hi : v (sharedIndex (h-1) μ hm)<sharedCap c-1) :
    ((v (sharedIndex (h-1) μ hm) : ℤ)+1)*ordinaryWeight c b (h-(μ+1))≤2*(ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) μ hm) (v (sharedIndex (h-1) μ hm)+1))) ∧
    ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) μ hm) (v (sharedIndex (h-1) μ hm)+1))≤
      2*((v (sharedIndex (h-1) μ hm) : ℤ)+1)*ordinaryWeight c b (h-(μ+1)) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds (h-1) (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := ordinary_shared_box_bound h c μ (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
    (by rw [sharedParameters_at (h-1) μ v hm]; omega)
  have hx := ordinary_parameter_dense_bounds h b v (by omega) hb hbds.2.2
  have hch := ordinary_cubic_bound h c (by omega) hc
  have he := ordinaryValue_shared_step h c b _ μ (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hch hb hx (Nat.sub_le _ _) hm (hbds.2.1 μ hm).1 hnu
  rw [ordinaryParameterValue_update_shared]
  simpa only [ordinaryParameterValue,sharedParameters_at (h-1) μ v hm,
    Nat.cast_add,Nat.cast_one] using he

theorem ordinary_parameter_dense_step_bounds (h c b : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hv : InNatBox (ordinaryCaps h c b) v)
    (hi : v (denseIndex (h-1))<denseWidth h b) :
    0≤ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (denseIndex (h-1)) (v (denseIndex (h-1))+1)) ∧
    ordinaryParameterValue h c b v-
      ordinaryParameterValue h c b (Function.update v (denseIndex (h-1)) (v (denseIndex (h-1))+1))≤
      2*h*(ordinaryBeta c (h-2) : ℤ) := by
  have hcap := large_caps_positive (h := h) (c := c) (by omega) hc
  have hbds := parameterCoordinates_bounds (h-1) (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := ordinaryNonfreeSize_bound h c (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hc hbds.1 (fun m hm => (hbds.2.1 m hm).2)
  have hN : ordinaryNonfreeSize h (repetitionParameters (h-1) v) (sharedParameters (h-1) v)≤c := by
    have ht := Nat.le_mul_of_pos_left (ordinaryNonfreeSize h (repetitionParameters (h-1) v) (sharedParameters (h-1) v))
      (by omega : 0<4*h)
    omega
  have hm := denseMaximum_ge h b (by omega) hb
  have hx : b-1≤denseMaximum h b-(v (denseIndex (h-1))+1) := by
    unfold denseWidth at hi
    omega
  have heq : denseMaximum h b-v (denseIndex (h-1))=denseMaximum h b-(v (denseIndex (h-1))+1)+1 := by
    unfold denseWidth at hi
    omega
  have hch := ordinary_cubic_bound h c (by omega) hc
  have he := ordinaryValue_dense_step h c b (denseMaximum h b-(v (denseIndex (h-1))+1))
    (repetitionParameters (h-1) v) (sharedParameters (h-1) v) (by omega) (by
      have hp := (large_c_elementary (h := h) (c := c) (by omega) hc).2
      nlinarith) hb hx hN
  rw [ordinaryParameterValue_update_dense]
  simpa only [ordinaryParameterValue,heq] using he

end SumsetRanges
