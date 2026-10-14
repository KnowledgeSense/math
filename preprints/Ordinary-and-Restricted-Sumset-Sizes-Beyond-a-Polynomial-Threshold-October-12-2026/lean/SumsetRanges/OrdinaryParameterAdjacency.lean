import SumsetRanges.OrdinaryParameterBounds

namespace SumsetRanges

theorem ordinary_parameter_first_bound (h c b : ℕ) (hh : 3≤h)
    (i : Fin (parameterDimension (h-1))) (hi : i.val=0) : ordinaryParameterStepBound h c b i≤1 := by
  have hn : i≠denseIndex (h-1) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [denseIndex] at hv
    omega
  simp [ordinaryParameterStepBound,hn,hi]

theorem ordinary_parameter_next_bound (h c b : ℕ) (hh : 3≤h) (hc : h≤c)
    (i j : Fin (parameterDimension (h-1))) (hij : j.val+1=i.val) :
    ordinaryParameterStepBound h c b i≤ordinaryParameterWidthBound h c b j := by
  have hj : j≠denseIndex (h-1) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [denseIndex] at hv
    have hi := i.isLt
    simp only [parameterDimension] at hi
    omega
  have hi0 : i.val≠0 := by omega
  simp only [ordinaryParameterWidthBound,ite_eq_right hj]
  by_cases hid : i=denseIndex (h-1)
  · have hi : i.val=2*(h-1-1) := congrArg Fin.val hid
    have hjmod : j.val%2=1 := by omega
    have hjdiv : j.val/2=h-3 := by omega
    simp only [ordinaryParameterStepBound,ite_eq_left hid,hjmod,hjdiv]
    norm_num
    have hw : (ordinaryBeta c (h-3) : ℤ)≤ordinaryWeight c b (h-3) := by
      unfold ordinaryWeight
      apply le_add_of_nonneg_right
      split_ifs <;> positivity
    have hb : (ordinaryBeta c (h-2) : ℤ)≤2*(c : ℤ)*ordinaryBeta c (h-3) := by
      exact_mod_cast ordinaryBeta_dense_previous h c hh hc
    have hn := ordinaryWeight_nonneg c b (h-3)
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℤ)≤2*(h:ℤ))
    have hm' := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℤ)≤4*(h:ℤ)*c)
    have hp : 0≤(h:ℤ)*b*ordinaryWeight c b (h-3) := by positivity
    nlinarith
  · simp only [ordinaryParameterStepBound,ite_eq_right hid,ite_eq_right hi0]
    rcases Nat.mod_two_eq_zero_or_one i.val with hm | hm
    · have hjm : j.val%2=1 := by omega
      have hd : i.val/2=j.val/2+1 := by omega
      simp only [hm,hjm]
      norm_num
      have hi : i.val<parameterDimension (h-1) := i.isLt
      have hDh : i.val/2≤h := by simp only [parameterDimension] at hi; omega
      have hw := ordinaryWeight_adjacent h c b (i.val/2) hc (by omega) (by omega) hDh
      have hd' : i.val/2-1=j.val/2 := by omega
      rw [hd'] at hw
      have hn := ordinaryWeight_nonneg c b (j.val/2)
      have hh' : (1:ℤ)≤h := by omega
      have hnon : 0≤((c+b:ℕ):ℤ)*ordinaryWeight c b (j.val/2) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hh' hnon
      push_cast at hw hmul ⊢
      nlinarith
    · have hjm : j.val%2=0 := by omega
      have hd : i.val/2=j.val/2 := by omega
      simp [hm,hjm,hd]

end SumsetRanges
