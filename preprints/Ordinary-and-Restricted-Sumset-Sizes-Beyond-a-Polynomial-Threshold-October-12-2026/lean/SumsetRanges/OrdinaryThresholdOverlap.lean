import SumsetRanges.RestrictedThresholdOverlap
import SumsetRanges.OrdinaryBaselineSize
import SumsetRanges.OrdinarySmallRange

namespace SumsetRanges

theorem ordinary_threshold_elementary (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    h≤k ∧ 8*h≤k-1 ∧ h^2+1≤(k-1)/2 := by
  have hp : (2*h)^4≤k := (Nat.pow_le_pow_right (by omega) (by omega : 4≤80)).trans hk
  have hh2 : h^2≥4 := by nlinarith
  have hh4 : h^4≥h^2 := Nat.pow_le_pow_right (by omega) (by omega)
  have he : (2*h)^4=16*h^4 := by ring
  have hk' : 2*(h^2+1)+1≤k := by nlinarith
  have hk'' : 8*h+1≤k := by nlinarith [sq_nonneg (h-2:ℤ)]
  refine ⟨by omega,by omega,?_⟩
  omega

theorem ordinary_overlap_properties (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    k+h-3≤overlapEndpoint h k ∧
    (8*h)^h*overlapEndpoint h k≤(k-1)^h ∧
    3*h*k*(sparseThreshold k)^(h-1)≤h*overlapEndpoint h k+1 ∧
    h+overlapEndpoint h k≤k^h := by
  have hel := ordinary_threshold_elementary h k hh hk
  have hK := sparseThreshold_large hh hk
  have hKpos : 1≤sparseThreshold k := by
    have hp : 1≤(32*h^3)^10 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpow : 1≤(sparseThreshold k)^(h-1) := Nat.one_le_pow _ _ hKpos
  have hD : 8*h≤restrictedDenominator h := by
    unfold restrictedDenominator
    have ht : 1≤2*h-1 := by omega
    nlinarith
  have hratio := threshold_ratio_bound h k hh hk
  have hratio' : (8*(8*h))^2*sparseThreshold k≤k :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hD) _)).trans hratio
  refine ⟨?_,?_,?_,(overlapEndpoint_properties h k hh hk).2.2.2⟩
  · unfold overlapEndpoint
    have hm := Nat.mul_le_mul_left (4*k) hpow
    have hh' := hel.1
    omega
  · exact overlap_power_bound h k (8*h) (sparseThreshold k) hh (by omega) (by omega) hratio'
  · unfold overlapEndpoint
    have hm := Nat.mul_le_mul_right (h*k*(sparseThreshold k)^(h-1)) (by omega : 3≤4)
    nlinarith only [hm]

theorem ordinaryExponent_ge_order (h : ℕ) (hh : 2≤h) : h≤ordinaryExponent h := by
  unfold ordinaryExponent
  nlinarith [sq_nonneg (h:ℤ)]

theorem ordinary_interval_realized_of_three_le (h k t : ℕ) (hh : 3≤h)
    (hk : (2*h)^80≤k) (ht : ordinaryMinimum h k≤t)
    (htop : t≤(h+k-1).choose h) (hex : t∉excludedValues h k) :
    ∃A : Finset ℤ,A.card=k ∧ (∀a∈A,0≤a ∧ a≤(k^(ordinaryExponent h):ℕ)) ∧
      (ordinarySums A h).card=t := by
  have hh2 : 2≤h := by omega
  have hel := ordinary_threshold_elementary h k hh2 hk
  have hov := ordinary_overlap_properties h k hh2 hk
  by_cases hsmall : t≤h*overlapEndpoint h k+1
  · obtain ⟨A,hAc,hA,hAs⟩ := ordinary_small_range h k (overlapEndpoint h k) t hh2 hel.1
      hel.2.1 hel.2.2 hov.1 hov.2.1 ht hsmall hex
    refine ⟨A,hAc,?_,hAs⟩
    intro a ha
    have hb := Finset.mem_Icc.mp (hA ha)
    refine ⟨hb.1,hb.2.trans ?_⟩
    exact_mod_cast hov.2.2.2.trans (Nat.pow_le_pow_right (by omega) (ordinaryExponent_ge_order h hh2))
  · have hlarge : 3*(h:ℤ)*k*(sparseThreshold k:ℤ)^(h-1)≤(t:ℤ) := by
      exact_mod_cast hov.2.2.1.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
    obtain ⟨A,hAc,hA,hAs⟩ := ordinary_large_range h k (sparseThreshold k) hh
      (sparseThreshold_large hh2 hk) (by have := sparseThreshold_le_sub_two hh2 hk; omega)
      le_rfl t hlarge (by exact_mod_cast htop)
    exact ⟨A,hAc,hA,by exact_mod_cast hAs⟩

end SumsetRanges
