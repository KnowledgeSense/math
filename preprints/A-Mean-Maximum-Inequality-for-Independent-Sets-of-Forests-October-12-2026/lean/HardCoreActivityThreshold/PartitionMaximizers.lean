import HardCoreActivityThreshold.FinitePartitions

namespace HardCoreActivityThreshold

open Set Finset

theorem partitionCost_le {n : ℕ} (a : Fin n → ℝ) (ha : ∀i,a i∈Set.Icc 0 criticalEndpoint) :
    partitionCost a≤1.001*partitionTotal a := by
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => partitionFunction_global_le (a i) (ha i))
  simpa [partitionCost,partitionTotal,Finset.mul_sum] using h

theorem partitionCost_large_coordinate {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Set.Icc 0 criticalEndpoint) (i : Fin n) (hi : concavityEndpoint≤a i) :
    partitionCost a≤1.001*partitionTotal a-0.011*a i := by
  have h : ∀k : Fin n,scalarPartitionFunction (a k)≤1.001*a k-(if k=i then 0.011*a i else 0) := by
    intro k
    by_cases hk : k=i
    · subst k
      simp only [↓reduceIte]
      have hf := partitionFunction_high_bound (a i) hi (ha i).2
      linarith
    · simp only [hk,↓reduceIte,sub_zero]
      exact partitionFunction_global_le (a k) (ha k)
  have hs := sum_le_sum (s := (univ : Finset (Fin n))) (fun k _ => h k)
  simpa [partitionCost,partitionTotal,sum_sub_distrib,Finset.mul_sum] using hs

theorem violating_partition_middle {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Set.Icc 0 criticalEndpoint) (hv : potential (partitionTotal a)<partitionCost a) :
    partitionTotal a∈Set.Ioo 2.5 3.1 := by
  have hY : 0≤partitionTotal a := sum_nonneg (fun i _ => (ha i).1)
  by_contra hm
  have hout : partitionTotal a≤5/2 ∨ 31/10≤partitionTotal a := by
    simp only [Set.mem_Ioo,not_and_or,not_lt] at hm
    rcases hm with h | h
    · left; linarith
    · right; linarith
  have hz : cubicCenter∈Set.Icc (28310/10000) (28311/10000) := by
    convert cubicCenter_bounds using 1; norm_num
  have hp := cubicPotential_outside cubicCenter _ hz hY hout
  have hc := partitionCost_le a ha
  change cubicPotential cubicCenter (partitionTotal a)<partitionCost a at hv
  linarith

theorem violating_partition_coordinates {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Set.Icc 0 criticalEndpoint) (hv : potential (partitionTotal a)<partitionCost a) :
    ∀i,a i<concavityEndpoint := by
  intro i
  by_contra hi
  have hi' : concavityEndpoint≤a i := le_of_not_gt hi
  have hcost := partitionCost_large_coordinate a ha i hi'
  have hY := violating_partition_middle a ha hv
  have hA : 0.9<concavityEndpoint := by
    have h := logarithm_concavity_bounds
    unfold concavityEndpoint
    linarith [h.1]
  have hnon : 0≤partitionTotal a := by linarith [hY.1]
  have hp := cubicPotential_ge cubicCenter (partitionTotal a) hnon
  change cubicPotential cubicCenter (partitionTotal a)<partitionCost a at hv
  linarith [hY.2]

end HardCoreActivityThreshold
