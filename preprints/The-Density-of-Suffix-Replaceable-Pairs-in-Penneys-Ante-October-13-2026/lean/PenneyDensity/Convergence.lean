import PenneyDensity.BoundaryMarginal
import PenneyDensity.ExceptionalBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
namespace PenneyDensity
open Filter
open scoped Topology

 theorem density_local_approximation {n K : ℕ} (hn : 2*K<n) :
    |density n-boundaryProbability K|≤
      4*(1/2 : ℝ)^K+collisionCoefficient K*(1/2 : ℝ)^(n-2*K) := by
  rw [density_eq_probability,← small_overlap_probability hn]
  have hh := probability_difference_le (P := fun f : Fin (n+n) → Bool =>
    PropertyR (pairWords f false) (pairWords f true))
    (Q := fun f => SmallOverlapAgreement (pairWords f) K)
    (E := fun f => LongOverlap (pairWords f) K ∨ BlockCollision (pairWords f) n K)
    (fun f hf => propertyR_localization (pairWords_length f) hn
      (fun ha => hf (Or.inl ha)) (fun hb => hf (Or.inr hb)))
  exact hh.trans ((probability_or_le _ _).trans
    (add_le_add (long_overlap_probability_bound n K) (block_collision_probability_bound hn)))

 theorem density_cauchy : CauchySeq density := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h8 : Tendsto (fun k : ℕ => 8*(1/2 : ℝ)^k) atTop (𝓝 0) := by
    simpa using hp.const_mul 8
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((tendsto_order.mp h8).2 (ε/2) (by linarith))
  have hK' := hK K le_rfl
  have htail : Tendsto (fun n : ℕ => collisionCoefficient K*(1/2 : ℝ)^(n-2*K)) atTop (𝓝 0) := by
    simpa using (hp.comp (tendsto_sub_atTop_nat (2*K))).const_mul (collisionCoefficient K)
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_order.mp htail).2 (ε/4) (by linarith))
  refine ⟨max (2*K+1) M,?_⟩
  intro m hm n hn
  have hmK : 2*K<m := by omega
  have hnK : 2*K<n := by omega
  have hmM : M≤m := by omega
  have hnM : M≤n := by omega
  have ham := density_local_approximation hmK
  have han := density_local_approximation hnK
  have htm := hM m hmM
  have htn := hM n hnM
  rw [Real.dist_eq]
  have htri := abs_sub_le (density m) (boundaryProbability K) (density n)
  rw [abs_sub_comm (boundaryProbability K) (density n)] at htri
  linarith

/-- Convergence of the entire original density sequence; no subsequence or
restriction on the target word pairs is used. -/
theorem density_has_limit : ∃ ρ : ℝ,Tendsto density atTop (𝓝 ρ) :=
  cauchySeq_tendsto_of_complete density_cauchy

end PenneyDensity
