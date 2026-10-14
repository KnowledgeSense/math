import SumsetRanges.OrdinarySparseBounds

open Finset
namespace SumsetRanges

theorem ordinarySeries_carryG_zero (m : ℕ) (hm : 2≤m) :
    ordinarySeries (carryG m 0)=geometricSeries := by
  simp [carryG_series_geometric m 0 hm]

theorem ordinarySeries_carryH_one (m : ℕ) (hm : 2≤m) :
    ordinarySeries (carryH m 1)=geometricSeries^2 := by
  have he := ordinary_carryH_step m 0 hm
  have hzero : carryH m 0=∅ := by simp [carryH]
  rw [hzero,ordinarySeries_empty] at he
  simpa using (sub_eq_zero.mp (by simpa using he)).symm

theorem ordinarySparseSeries_baseline (h c : ℕ) (r u : ℕ → ℕ)
    (hr : ∀m∈Icc 2 (h-1),r m=0) (hu : ∀m∈Icc 2 (h-1),u m=1)
    (hc : ordinaryNonfreeSize h r u≤c) :
    ordinarySparseSeries h c r u=geometricSeries^c := by
  have he : (∏m∈Icc 2 (h-1),ordinarySeries (carryG (m+1) (r m))*ordinarySeries (carryH m (u m)))=
      geometricSeries^(ordinaryNonfreeSize h r u) := by
    rw [ordinaryNonfreeSize,←Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro m hm
    rw [hr m hm,hu m hm,ordinarySeries_carryG_zero (m+1) (by have := (mem_Icc.mp hm).1; omega),
      ordinarySeries_carryH_one m (mem_Icc.mp hm).1]
    norm_num [pow_succ]
    ring
  rw [ordinarySparseSeries,he,←pow_add,Nat.sub_add_cancel hc]

end SumsetRanges
