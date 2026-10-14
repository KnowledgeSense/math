import SumsetRanges.OrdinaryParameterSteps

open Finset
namespace SumsetRanges
open scoped Classical

noncomputable def ordinaryParameterStepBound (h c b : ℕ) (i : Fin (parameterDimension (h-1))) : ℤ :=
  if i=denseIndex (h-1) then 2*h*(ordinaryBeta c (h-2) : ℤ)
  else if i.val=0 then 1
  else if i.val%2=0 then 2*ordinaryWeight c b (i.val/2)
  else 2*((sharedCap c-1 : ℕ) : ℤ)*ordinaryWeight c b (i.val/2)

noncomputable def ordinaryParameterWidthBound (h c b : ℕ) (i : Fin (parameterDimension (h-1))) : ℤ :=
  if i=denseIndex (h-1) then 0
  else if i.val%2=0 then 2*((sharedCap c-1 : ℕ) : ℤ)*ordinaryWeight c b (i.val/2)
  else 4*(h : ℤ)*((c+b : ℕ) : ℤ)*ordinaryWeight c b (i.val/2)

theorem ordinary_parameter_antitone (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) :
    ∀v w,InNatBox (ordinaryCaps h c b) v → InNatBox (ordinaryCaps h c b) w →
      (∀i,v i≤w i) → ordinaryParameterValue h c b w≤ordinaryParameterValue h c b v := by
  apply box_antitone_of_steps
  intro v hv i hi
  rcases parameterIndex_cases (h-1) (by omega) i with he | ⟨m,hm,he|he⟩
  · subst i
    have hi' : v (denseIndex (h-1))<denseWidth h b := by simpa [ordinaryCaps] using hi
    have hs := (ordinary_parameter_dense_step_bounds h c b v hh hc hb hv hi').1
    omega
  · subst i
    have hi' : v (repetitionIndex (h-1) m hm)<repetitionCap c := by simpa [ordinaryCaps] using hi
    have hs := (ordinary_parameter_linear_step_bounds h c b m v hh hc hb hm hv hi').1
    have hw := ordinaryWeight_nonneg c b (h-(m+1))
    omega
  · subst i
    have hi' : v (sharedIndex (h-1) m hm)<sharedCap c-1 := by simpa [ordinaryCaps] using hi
    have hs := (ordinary_parameter_shared_step_bounds h c b m v hh hc hb hm hv hi').1
    have hw := ordinaryWeight_nonneg c b (h-(m+1))
    have hp : 0≤((v (sharedIndex (h-1) m hm) : ℤ)+1)*ordinaryWeight c b (h-(m+1)) :=
      mul_nonneg (by positivity) hw
    omega

theorem ordinary_parameter_step_bound (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (v : Fin (parameterDimension (h-1)) → ℕ) (hv : InNatBox (ordinaryCaps h c b) v)
    (i : Fin (parameterDimension (h-1))) (hi : v i<ordinaryCaps h c b i) :
    ordinaryParameterValue h c b v-ordinaryParameterValue h c b (Function.update v i (v i+1))≤ordinaryParameterStepBound h c b i := by
  rcases parameterIndex_cases (h-1) (by omega) i with he | ⟨m,hm,he|he⟩
  · subst i
    have hi' : v (denseIndex (h-1))<denseWidth h b := by simpa [ordinaryCaps] using hi
    simpa [ordinaryParameterStepBound] using
      (ordinary_parameter_dense_step_bounds h c b v hh hc hb hv hi').2
  · subst i
    have hi' : v (repetitionIndex (h-1) m hm)<repetitionCap c := by simpa [ordinaryCaps] using hi
    by_cases he : m=h-1
    · subst m
      have hbds := parameterCoordinates_bounds (h-1) (repetitionCap c) (sharedCap c) (denseWidth h b) v
        (by have := large_caps_positive (by omega : 1≤h) hc; omega) hv
      have hnu := ordinary_linear_box_bound h c (h-1) (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
        (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
        (by simpa only [repetitionParameters_at (h-1) (h-1) v hm] using hi')
      have hN : ordinaryNonfreeSize h (repetitionParameters (h-1) v) (sharedParameters (h-1) v)+2≤c := by
        have ht := Nat.le_mul_of_pos_left (ordinaryNonfreeSize h (repetitionParameters (h-1) v) (sharedParameters (h-1) v)+2)
          (by omega : 0<4*h)
        omega
      have heq := ordinaryValue_top_linear_step h c b (denseMaximum h b-v (denseIndex (h-1))) (repetitionParameters (h-1) v) (sharedParameters (h-1) v) hh hN
      have hbound : ordinaryParameterStepBound h c b (repetitionIndex (h-1) (h-1) hm)=1 := by
        have hz : (repetitionIndex (h-1) (h-1) hm).val=0 := by simp [repetitionIndex]
        simp [ordinaryParameterStepBound,hz]
      rw [hbound,ordinaryParameterValue_update_repetition]
      simpa only [ordinaryParameterValue,repetitionParameters_at (h-1) (h-1) v hm] using heq.le
    · have hz : (repetitionIndex (h-1) m hm).val≠0 := by
        simp only [repetitionIndex]
        have := mem_Icc.mp hm
        omega
      simp only [ordinaryParameterStepBound,ite_eq_right (repetitionIndex_ne_dense (h-1) m hm),ite_eq_right hz]
      simpa [repetitionIndex,Nat.sub_sub,Nat.add_comm 1] using (ordinary_parameter_linear_step_bounds h c b m v hh hc hb hm hv hi').2
  · subst i
    have hi' : v (sharedIndex (h-1) m hm)<sharedCap c-1 := by simpa [ordinaryCaps] using hi
    have hs := (ordinary_parameter_shared_step_bounds h c b m v hh hc hb hm hv hi').2
    have hmul : ((v (sharedIndex (h-1) m hm) : ℤ)+1)≤((sharedCap c-1 : ℕ) : ℤ) := by omega
    have hw := ordinaryWeight_nonneg c b (h-(m+1))
    have hle := mul_le_mul_of_nonneg_right hmul hw
    have hz : (sharedIndex (h-1) m hm).val≠0 := by simp [sharedIndex]
    have hmod : (sharedIndex (h-1) m hm).val%2≠0 := by simp [sharedIndex,Nat.add_mod]
    have hdiv : (sharedIndex (h-1) m hm).val/2=h-(m+1) := by simp only [sharedIndex]; omega
    simp only [ordinaryParameterStepBound,ite_eq_right (sharedIndex_ne_dense (h-1) m hm),
      ite_eq_right hz,ite_eq_right hmod,hdiv]
    nlinarith

end SumsetRanges
