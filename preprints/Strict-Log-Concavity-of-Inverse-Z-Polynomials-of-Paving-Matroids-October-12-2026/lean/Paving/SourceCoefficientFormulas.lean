import Paving.CentralDecomposition
import Paving.CentralBinomial

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem uniformEntry_free_hyperplane (r k : ℕ) (hk : k+1<r) :
    uniformEntry r (r-1) k = 0 := by
  unfold uniformEntry
  rw [Nat.choose_eq_zero_of_lt (by omega : r-1-k-1<r-1-k), Nat.cast_zero, mul_zero]

theorem hyperplane_uniformEntry_sum (M : Matroid α) (k : ℕ) (hk : k+1<rank M) :
    (∑ H ∈ hyperplanes M, uniformEntry (rank M) H.ncard k) =
      ∑ H ∈ stressedHyperplanes M, uniformEntry (rank M) H.ncard k := by
  rw [stressedHyperplanes,sum_filter]
  apply sum_congr rfl
  intro H hH
  by_cases hs : rank M≤H.ncard
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hc := hyperplane_card_lower ((mem_hyperplanes M H).mp hH)
    have he : H.ncard=rank M-1 := by omega
    rw [he,uniformEntry_free_hyperplane _ _ hk]

theorem uniformEntry_source (r n k : ℕ) (hr : r≤n) (hk : k<r) :
    uniformEntry r n k = (n.choose k:ℤ)*(n-k-1).choose (n-r) := by
  unfold uniformEntry
  have he : n-k-1-(r-1-k)=n-r := by omega
  rw [← Nat.choose_symm (show r-1-k≤n-k-1 by omega),he]

/-- The source subtraction formula away from the even center, now proved
for the original invariant from actual flats, with exactly the stressed hyperplanes. -/
theorem IsPaving.source_noncentral_coefficient (hM : IsPaving M) (hr : 3≤rank M)
    (k : ℕ) (hk : 2*k<rank M) :
    (matroidInverseZ M).coeff k = uniformEntry (rank M) M.E.ncard k -
      ∑ H ∈ stressedHyperplanes M, uniformEntry (rank M) H.ncard k := by
  rw [hM.actual_inverseZ_noncentral_formula hr k hk,hyperplane_uniformEntry_sum M k (by omega)]

/-- The complete even-center correction has been evaluated using the actual
uniform hyperplane inverse-Q term. -/
theorem IsPaving.source_central_coefficient (hM : IsPaving M) (m : ℕ) (hm : 2≤m)
    (hr : rank M=2*m) :
    (matroidInverseZ M).coeff m = uniformEntry (2*m) M.E.ncard m -
      ∑ H ∈ stressedHyperplanes M, uniformEntry (2*m) H.ncard (m-1) := by
  rw [hM.actual_inverseZ_center_split m hm hr]
  have hs : (∑ H ∈ hyperplanes M, uniformEntry (2*m) H.ncard m) -
      (∑ H ∈ hyperplanes M, (uniformQ (α:=H) (2*m-2)).coeff (m-1)) =
      ∑ H ∈ hyperplanes M, uniformEntry (2*m) H.ncard (m-1) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro H hH
    have hc := hyperplane_card_lower ((mem_hyperplanes M H).mp hH)
    have hn : Fintype.card H=H.ncard := (Set.ncard_eq_toFinset_card' H).trans (Set.toFinset_card H) |>.symm
    have h := uniform_central_correction (α:=H) m hm (by rw [hn]; omega)
    simpa only [hn] using h
  have ht := hyperplane_uniformEntry_sum M (m-1) (by omega)
  rw [hr] at ht
  rw [ht] at hs
  omega

end Paving
