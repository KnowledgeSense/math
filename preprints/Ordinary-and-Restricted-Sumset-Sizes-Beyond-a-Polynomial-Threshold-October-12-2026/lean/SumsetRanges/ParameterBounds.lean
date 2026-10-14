import SumsetRanges.ParameterSteps

open Finset
namespace SumsetRanges
open scoped Classical

noncomputable def parameterStepBound (h c b : ℕ) (i : Fin (parameterDimension h)) : ℤ :=
  if i=denseIndex h then 2*(c.choose (h-2) : ℤ)
  else if i.val=0 then 1
  else if i.val%2=0 then 2*restrictedWeight c b (i.val/2)
  else 2*((sharedCap c-1 : ℕ) : ℤ)*restrictedWeight c b (i.val/2)

noncomputable def parameterWidthBound (h c b : ℕ) (i : Fin (parameterDimension h)) : ℤ :=
  if i=denseIndex h then 0
  else if i.val%2=0 then 2*((sharedCap c-1 : ℕ) : ℤ)*restrictedWeight c b (i.val/2)
  else 2*((c+b : ℕ) : ℤ)*restrictedWeight c b (i.val/2)

theorem parameter_antitone (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) :
    ∀v w,InNatBox (admissibleCaps h c b) v → InNatBox (admissibleCaps h c b) w →
      (∀i,v i≤w i) → parameterValue h c b w≤parameterValue h c b v := by
  apply box_antitone_of_steps
  intro v hv i hi
  rcases parameterIndex_cases h hh i with he | ⟨m,hm,he|he⟩
  · subst i
    have hi' : v (denseIndex h)<denseWidth h b := by simpa [admissibleCaps] using hi
    have hs := (parameter_dense_step_bounds h c b v hh hc hb hv hi').1
    omega
  · subst i
    have hi' : v (repetitionIndex h m hm)<repetitionCap c := by simpa [admissibleCaps] using hi
    have hs := (parameter_linear_step_bounds h c b m v hh hc hb hm hv hi').1
    have hw := restrictedWeight_nonneg c b (h-m)
    omega
  · subst i
    have hi' : v (sharedIndex h m hm)<sharedCap c-1 := by simpa [admissibleCaps] using hi
    have hs := (parameter_shared_step_bounds h c b m v hh hc hb hm hv hi').1
    have hw := restrictedWeight_nonneg c b (h-m)
    have hp : 0≤((v (sharedIndex h m hm) : ℤ)+1)*restrictedWeight c b (h-m) :=
      mul_nonneg (by positivity) hw
    omega

theorem parameter_step_bound (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (v : Fin (parameterDimension h) → ℕ) (hv : InNatBox (admissibleCaps h c b) v)
    (i : Fin (parameterDimension h)) (hi : v i<admissibleCaps h c b i) :
    parameterValue h c b v-parameterValue h c b (Function.update v i (v i+1))≤parameterStepBound h c b i := by
  rcases parameterIndex_cases h hh i with he | ⟨m,hm,he|he⟩
  · subst i
    have hi' : v (denseIndex h)<denseWidth h b := by simpa [admissibleCaps] using hi
    simpa [parameterStepBound] using
      (parameter_dense_step_bounds h c b v hh hc hb hv hi').2
  · subst i
    have hi' : v (repetitionIndex h m hm)<repetitionCap c := by simpa [admissibleCaps] using hi
    by_cases he : m=h
    · subst m
      have hbds := parameterCoordinates_bounds h (repetitionCap c) (sharedCap c) (denseWidth h b) v
        (by have := large_caps_positive (by omega : 1≤h) hc; omega) hv
      have hnu := linear_step_box_bound h c h (repetitionParameters h v) (sharedParameters h v)
        (by omega) hc hm hbds.1 (fun m hm => (hbds.2.1 m hm).2)
        (by simpa only [repetitionParameters_at h h v hm] using hi')
      have hN : nonfreeSize h (repetitionParameters h v) (sharedParameters h v)+2*h≤c := by
        have ht := Nat.le_mul_of_pos_left (nonfreeSize h (repetitionParameters h v) (sharedParameters h v)+2*h)
          (by omega : 0<8*h)
        omega
      have heq := largeValue_top_linear_step h c b (denseMaximum h b-v (denseIndex h)) (repetitionParameters h v) (sharedParameters h v) hh hN
      have hbound : parameterStepBound h c b (repetitionIndex h h hm)=1 := by
        have hz : (repetitionIndex h h hm).val=0 := by simp [repetitionIndex]
        simp [parameterStepBound,hz]
      rw [hbound,parameterValue_update_repetition]
      simpa only [parameterValue,repetitionParameters_at h h v hm] using heq.le
    · have hz : (repetitionIndex h m hm).val≠0 := by
        simp only [repetitionIndex]
        have := mem_Icc.mp hm
        omega
      simp only [parameterStepBound,ite_eq_right (repetitionIndex_ne_dense h m hm),ite_eq_right hz]
      simpa [repetitionIndex] using (parameter_linear_step_bounds h c b m v hh hc hb hm hv hi').2
  · subst i
    have hi' : v (sharedIndex h m hm)<sharedCap c-1 := by simpa [admissibleCaps] using hi
    have hs := (parameter_shared_step_bounds h c b m v hh hc hb hm hv hi').2
    have hmul : ((v (sharedIndex h m hm) : ℤ)+1)≤((sharedCap c-1 : ℕ) : ℤ) := by omega
    have hw := restrictedWeight_nonneg c b (h-m)
    have hle := mul_le_mul_of_nonneg_right hmul hw
    have hz : (sharedIndex h m hm).val≠0 := by simp [sharedIndex]
    have hmod : (sharedIndex h m hm).val%2≠0 := by simp [sharedIndex,Nat.add_mod]
    have hdiv : (sharedIndex h m hm).val/2=h-m := by simp only [sharedIndex]; omega
    simp only [parameterStepBound,ite_eq_right (sharedIndex_ne_dense h m hm),
      ite_eq_right hz,ite_eq_right hmod,hdiv]
    nlinarith

end SumsetRanges
