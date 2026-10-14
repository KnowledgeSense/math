import SumsetRanges.RestrictedThresholdOverlap
import SumsetRanges.RestrictedSmallRange
import SumsetRanges.BaselineSizeBound
import SumsetRanges.RestrictedBounds

open Finset
namespace SumsetRanges

theorem h_le_restrictedExponent (h : ℕ) (hh : 2≤h) : h≤restrictedExponent h := by
  have hd : 1≤restrictedDimension h := by unfold restrictedDimension; omega
  have hm : h≤momentOrder h := by unfold momentOrder; nlinarith
  unfold restrictedExponent
  have hp : momentOrder h≤momentOrder h*restrictedDimension h := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Every prescribed cardinality in the full interval has an integer witness
with the diameter bound of the fixed release. -/
theorem restricted_interval_realized (h k t : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k)
    (ht : h*(k-h)+1≤t) (htop : t≤k.choose h) :
    ∃A : Finset ℤ,A.card=k ∧ (∀a∈A,0≤a ∧ a≤(k^(restrictedExponent h):ℕ)) ∧
      (restrictedSums A h).card=t := by
  have he := restricted_threshold_elementary h k hh hk
  have hm := overlapEndpoint_properties h k hh hk
  by_cases hs : t≤h*overlapEndpoint h k+h-(h-1)^2+1
  · obtain ⟨A,hA,hAb,hAc⟩ := restricted_small_range h k (overlapEndpoint h k) t hh
      he.1 hm.1 hm.2.1 ht hs
    refine ⟨A,hA,?_,hAc⟩
    intro a ha
    have hab := Finset.mem_Icc.mp (hAb ha)
    refine ⟨hab.1,hab.2.trans ?_⟩
    have hp : h+overlapEndpoint h k≤k^(restrictedExponent h) :=
      hm.2.2.2.trans (Nat.pow_le_pow_right (by omega) (h_le_restrictedExponent h hh))
    exact_mod_cast hp
  · have hK := sparseThreshold_large hh hk
    have hKk := sparseThreshold_le_sub_two hh hk
    have hz : 3*h*k*(sparseThreshold k)^(h-1)≤t := by omega
    obtain ⟨A,hA,hAb,hAc⟩ := restricted_large_range h k (sparseThreshold k) hh hK
      (by omega) (le_refl _) (t:ℤ) (by exact_mod_cast hz) (by exact_mod_cast htop)
    exact ⟨A,hA,hAb,by exact_mod_cast hAc⟩

/-- Exact restricted-sumset classification past the original polynomial threshold. -/
theorem restricted_range_eq (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    restrictedRange h k = Set.Icc (h*(k-h)+1) (k.choose h) := by
  apply Set.Subset.antisymm
  · apply restrictedRange_bounds
    have := restricted_threshold_elementary h k hh hk
    omega
  · intro t ht
    obtain ⟨A,hA,_,hAc⟩ := restricted_interval_realized h k t hh hk ht.1 ht.2
    exact ⟨A,hA,hAc⟩

theorem restricted_main : RestrictedMainStatement := by
  intro h k hh hk
  refine ⟨restricted_range_eq h k hh hk,?_⟩
  intro t ht
  exact restricted_interval_realized h k t hh hk ht.1 ht.2

end SumsetRanges
