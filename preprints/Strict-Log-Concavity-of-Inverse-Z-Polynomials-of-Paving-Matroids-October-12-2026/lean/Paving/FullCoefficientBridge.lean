import Paving.NormalizationBridge

namespace Paving
open MatroidInverseZ
variable {α : Type*} [Fintype α]

theorem IsPaving.actual_coefficient_center {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2≤m) (hr : rank M=2*m) :
    ((matroidInverseZ M).coeff m:ℝ)=normalization M*actualEvenMixture M m m := by
  have he : (matroidInverseZ M).coeff m = (matroidInverseZ M).coeff (m-1) +
      uniformEntry (2*m) M.E.ncard m-uniformEntry (2*m) M.E.ncard (m-1) := by
    rw [hM.source_central_coefficient m hm hr,hM.source_noncentral_coefficient (by omega) (m-1) (by omega),hr]
    ring
  rw [he]
  push_cast
  rw [hM.actual_coefficient_lower (by omega) (m-1) (by omega),
    uniformEntry_cast_normalized _ _ _ (hr ▸ rank_le_ground_card M) (by omega),
    uniformEntry_cast_normalized _ _ _ (hr ▸ rank_le_ground_card M) (by omega)]
  have hB : (M.E.ncard.choose (2*m-1):ℝ)=normalization M := by simp only [normalization,hr]
  rw [hB]
  change normalization M*actualLowerMixture M (m-1)+
    normalization M*uniformComponent (2*m) M.E.ncard m-
    normalization M*uniformComponent (2*m) M.E.ncard (m-1)=_
  rw [show normalization M*actualLowerMixture M (m-1)+
      normalization M*uniformComponent (2*m) M.E.ncard m-
      normalization M*uniformComponent (2*m) M.E.ncard (m-1)=
      normalization M*(actualLowerMixture M (m-1)+
        (uniformComponent (2*m) M.E.ncard m-uniformComponent (2*m) M.E.ncard (m-1))) by ring,
    uniform_middle_difference m M.E.ncard (by omega) (hr ▸ rank_le_ground_card M)]
  simp only [actualEvenMixture,ite_true]

/-- Complete supported coefficient bridge in odd rank. -/
theorem IsPaving.actual_coefficient_odd {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 1≤m) (hr : rank M=2*m+1) (k : ℕ) (hk : k≤rank M) :
    ((matroidInverseZ M).coeff k:ℝ)=normalization M*actualReflectedMixture M k := by
  change ((matroidInverseZ M).coeff k:ℝ)=
    normalization M*actualLowerMixture M (min k (rank M-k))
  by_cases hhalf : 2*k<rank M
  · rw [Nat.min_eq_left (by omega),hM.actual_coefficient_lower (by omega) k hhalf]
  · rw [Nat.min_eq_right (by omega),actual_inverseZ_coeff_symm M k hk,
      hM.actual_coefficient_lower (by omega) (rank M-k) (by omega)]

/-- Complete supported coefficient bridge in even rank, including the paid center. -/
theorem IsPaving.actual_coefficient_even {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2≤m) (hr : rank M=2*m) (k : ℕ) (hk : k≤2*m) :
    ((matroidInverseZ M).coeff k:ℝ)=normalization M*actualEvenMixture M m k := by
  by_cases he : k=m
  · subst k
    exact hM.actual_coefficient_center m hm hr
  · unfold actualEvenMixture
    rw [ite_eq_right he]
    by_cases hkm : k<m
    · rw [Nat.min_eq_left (by omega),hM.actual_coefficient_lower (by omega) k (by omega)]
    · rw [Nat.min_eq_right (by omega),actual_inverseZ_coeff_symm M k (by omega),hr,
        hM.actual_coefficient_lower (by omega) (2*m-k) (by omega)]

end Paving
