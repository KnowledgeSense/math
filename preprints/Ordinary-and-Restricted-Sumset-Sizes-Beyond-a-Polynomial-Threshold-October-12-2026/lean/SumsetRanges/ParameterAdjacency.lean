import SumsetRanges.ParameterBounds

namespace SumsetRanges
open scoped Classical

theorem restrictedWeight_step (c b D : ℕ) (hD : 1≤D) :
    restrictedWeight c b D≤((c+b : ℕ) : ℤ)*restrictedWeight c b (D-1) := by
  simpa only [Nat.sub_zero,zero_add] using restrictedWeight_adjacent D c b 0 (by omega)

theorem parameter_first_bound (h c b : ℕ) (hh : 2≤h)
    (i : Fin (parameterDimension h)) (hi : i.val=0) : parameterStepBound h c b i≤1 := by
  have hn : i≠denseIndex h := by
    intro he
    have hv := congrArg Fin.val he
    simp only [denseIndex] at hv
    omega
  simp [parameterStepBound,hn,hi]

theorem parameter_next_bound (h c b : ℕ) (hh : 2≤h) (hk : 1≤c+b)
    (i j : Fin (parameterDimension h)) (hij : j.val+1=i.val) :
    parameterStepBound h c b i≤parameterWidthBound h c b j := by
  have hj : j≠denseIndex h := by
    intro he
    have hv := congrArg Fin.val he
    simp only [denseIndex] at hv
    have hi := i.isLt
    simp only [parameterDimension] at hi
    omega
  have hi0 : i.val≠0 := by omega
  simp only [parameterWidthBound,ite_eq_right hj]
  by_cases hid : i=denseIndex h
  · have hi : i.val=2*(h-1) := congrArg Fin.val hid
    have hjmod : j.val%2=1 := by omega
    have hjdiv : j.val/2=h-2 := by omega
    simp only [parameterStepBound,ite_eq_left hid,hjmod,hjdiv]
    norm_num
    have hw : (c.choose (h-2) : ℤ)≤restrictedWeight c b (h-2) := by
      unfold restrictedWeight
      apply le_add_of_nonneg_right
      split_ifs <;> positivity
    have hn := restrictedWeight_nonneg c b (h-2)
    have hk' : (1 : ℤ)≤((c+b : ℕ) : ℤ) := by exact_mod_cast hk
    nlinarith
  · simp only [parameterStepBound,ite_eq_right hid,ite_eq_right hi0]
    rcases Nat.mod_two_eq_zero_or_one i.val with hm | hm
    · have hjm : j.val%2=1 := by omega
      have hd : i.val/2=j.val/2+1 := by omega
      simp only [hm,hjm]
      norm_num
      have hw := restrictedWeight_step c b (i.val/2) (by omega)
      have hd' : i.val/2-1=j.val/2 := by omega
      rw [hd'] at hw
      push_cast at hw
      linarith
    · have hjm : j.val%2=0 := by omega
      have hd : i.val/2=j.val/2 := by omega
      simp [hm,hjm,hd]

end SumsetRanges
