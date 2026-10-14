import HardCoreActivityThreshold.PartitionMaximizers

namespace HardCoreActivityThreshold

open Set Filter

theorem maximizing_positive_coordinates_equal {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Icc 0 criticalEndpoint)
    (hA : ∀i,a i<concavityEndpoint)
    (hm : IsMaxOn partitionCost (partitionDomain n (partitionTotal a)) a)
    (i j : Fin n) (hi : 0<a i) (hj : 0<a j) : a i=a j := by
  by_cases hij : i=j
  · subst j; rfl
  have hiX : a i<criticalEndpoint := (hA i).trans concavityEndpoint_lt_criticalEndpoint
  have hjX : a j<criticalEndpoint := (hA j).trans concavityEndpoint_lt_criticalEndpoint
  have hiN : ∀ᶠt in nhds (0 : ℝ),a i+t∈Ioo 0 criticalEndpoint := by
    have hc : ContinuousAt (fun t : ℝ => a i+t) 0 := by fun_prop
    apply hc.eventually
    change Ioo 0 criticalEndpoint ∈ nhds (a i+0)
    simpa only [add_zero] using Ioo_mem_nhds hi hiX
  have hjN : ∀ᶠt in nhds (0 : ℝ),a j-t∈Ioo 0 criticalEndpoint := by
    have hc : ContinuousAt (fun t : ℝ => a j-t) 0 := by fun_prop
    apply hc.eventually
    change Ioo 0 criticalEndpoint ∈ nhds (a j-0)
    simpa only [sub_zero] using Ioo_mem_nhds hj hjX
  have hlocal : IsLocalMax (transferFunction (a i) (a j)) 0 := by
    filter_upwards [hiN,hjN] with t hit hjt
    have had : partitionTransfer a i j t∈partitionDomain n (partitionTotal a) := by
      constructor
      · intro k
        by_cases hkj : k=j
        · subst k
          have he : a j-t∈Icc 0 criticalEndpoint := ⟨hjt.1.le,hjt.2.le⟩
          simpa only [partitionTransfer,Function.update_self] using he
        · by_cases hki : k=i
          · subst k
            simpa [partitionTransfer,Function.update_of_ne hij] using ⟨hit.1.le,hit.2.le⟩
          · simpa [partitionTransfer,Function.update_of_ne hkj,Function.update_of_ne hki] using ha k
      · exact partitionTransfer_total a i j hij t
    have h := hm had
    change partitionCost (partitionTransfer a i j t)≤partitionCost a at h
    rw [partitionTransfer_cost a i j hij t] at h
    change transferFunction (a i) (a j) t≤transferFunction (a i) (a j) 0
    simp only [transferFunction,add_zero,sub_zero]
    unfold transferFunction at h
    linarith
  exact transfer_local_max_equal (a i) (a j) ⟨hi,hA i⟩ ⟨hj,hA j⟩ hlocal

end HardCoreActivityThreshold
