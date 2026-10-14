import HardCoreActivityThreshold.SubcriticalCompensation

namespace HardCoreActivityThreshold

open Finset

theorem subcritical_partition_contraction (Λ : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) :
    ∃γ : ℝ,0<γ ∧ γ<1 ∧ ∀n : ℕ,∀a : Fin n → ℝ,
      (∀i,0<a i ∧ a i≤subcriticalEndpoint Λ) →
      (∑i,subcriticalFunction Λ (a i))≤γ*potential (partitionTotal a) := by
  obtain ⟨η,hη,hηhalf,hcomp⟩ := subcritical_uniform_compensation Λ hΛ hL
  refine ⟨1-η/2,by linarith,by linarith,?_⟩
  intro n a ha
  have hs := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin n))) =>
    hcomp (a i) (ha i).1 (ha i).2)
  have hsum : (∑i,((1-η)*scalarPartitionFunction (a i)+η*a i/2))=
      (1-η)*partitionCost a+η*partitionTotal a/2 := by
    simp only [sum_add_distrib,mul_div_assoc,←mul_sum,partitionCost,partitionTotal]
    rw [←sum_div]
  rw [hsum] at hs
  have hcrit := cubic_partition_inequality a (fun i => ⟨(ha i).1.le,
    (ha i).2.trans (subcriticalEndpoint_lt Λ hΛ hL).le⟩)
  have hY : 0≤partitionTotal a := sum_nonneg (fun i _ => (ha i).1.le)
  have hphi : partitionTotal a≤potential (partitionTotal a) :=
    cubicPotential_ge cubicCenter _ hY
  have hm := mul_le_mul_of_nonneg_left hcrit (show 0≤1-η by linarith)
  have hn := mul_le_mul_of_nonneg_left hphi hη.le
  nlinarith

end HardCoreActivityThreshold
