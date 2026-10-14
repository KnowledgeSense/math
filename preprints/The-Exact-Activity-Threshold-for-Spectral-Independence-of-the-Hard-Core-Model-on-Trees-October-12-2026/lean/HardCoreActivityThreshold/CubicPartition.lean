import HardCoreActivityThreshold.MaximizerEquality

namespace HardCoreActivityThreshold

open Set Finset

theorem equal_positive_partition_values {n : ℕ} (a : Fin n → ℝ) (x : ℝ)
    (ha : ∀i,0≤a i) (he : ∀i,0<a i → a i=x) :
    ∃b : ℕ,partitionTotal a=(b : ℝ)*x ∧ partitionCost a=(b : ℝ)*scalarPartitionFunction x := by
  classical
  let s : Finset (Fin n) := univ.filter (fun i => 0<a i)
  have hzero : ∀i,i∉s → a i=0 := by
    intro i hi
    have hle : a i≤0 := by simpa [s] using hi
    exact le_antisymm hle (ha i)
  have hpos : ∀i,i∈s → a i=x := by
    intro i hi
    exact he i (by simpa [s] using hi)
  refine ⟨s.card,?_,?_⟩
  · calc
      partitionTotal a=∑i : Fin n,if i∈s then x else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i∈s
        · simp [hi,hpos i hi]
        · simp [hi,hzero i hi]
      _=(s.card : ℝ)*x := by simp
  · calc
      partitionCost a=∑i : Fin n,if i∈s then scalarPartitionFunction x else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i∈s
        · simp [hi,hpos i hi]
        · simp [hi,hzero i hi,partitionFunction_zero]
      _=(s.card : ℝ)*scalarPartitionFunction x := by simp

theorem cubic_partition_inequality {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Set.Icc 0 criticalEndpoint) :
    partitionCost a≤potential (partitionTotal a) := by
  by_contra! hbad
  obtain ⟨b,hb,hm⟩ := partitionCost_maximizer a ha
  have hcost : partitionCost a≤partitionCost b := hm ⟨ha,rfl⟩
  have hbtotal : partitionTotal b=partitionTotal a := hb.2
  have hbadb : potential (partitionTotal b)<partitionCost b := by rw [hbtotal]; exact hbad.trans_le hcost
  have hmiddle := violating_partition_middle b hb.1 hbadb
  have hA := violating_partition_coordinates b hb.1 hbadb
  have hex : ∃i,0<b i := by
    by_contra! hn
    have hs : partitionTotal b≤0 := sum_nonpos (fun i _ => hn i)
    linarith [hmiddle.1]
  obtain ⟨i,hi⟩ := hex
  have he : ∀j,0<b j → b j=b i := by
    intro j hj
    exact maximizing_positive_coordinates_equal b hb.1 hA (by simpa [hbtotal] using hm) j i hj hi
  obtain ⟨k,hY,hC⟩ := equal_positive_partition_values b (b i) (fun j => (hb.1 j).1) he
  have hfinal := equal_partition_bound k (b i) hi.le (hb.1 i).2
  rw [←hY,←hC] at hfinal
  exact (not_lt_of_ge hfinal) hbadb

end HardCoreActivityThreshold
