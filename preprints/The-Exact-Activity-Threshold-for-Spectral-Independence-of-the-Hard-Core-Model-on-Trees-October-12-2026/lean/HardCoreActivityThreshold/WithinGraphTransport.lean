import HardCoreActivityThreshold.RestrictedLaw
import HardCoreActivityThreshold.CovarianceResponse

/-! Restricted hard-core laws are exactly induced-graph laws with vacant coordinates adjoined. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def allowedEmbedding (allowed : Finset V) : {v : V // v ∈ allowed} ↪ V :=
  Function.Embedding.subtype _

omit [Fintype V] [DecidableEq V] in
@[simp] theorem allowedEmbedding_apply (allowed : Finset V) (v : {v : V // v ∈ allowed}) :
    allowedEmbedding allowed v = v.val := rfl

omit [Fintype V] [DecidableEq V] in
theorem allowed_map_subset (allowed : Finset V) (s : Finset {v : V // v ∈ allowed}) :
    s.map (allowedEmbedding allowed) ⊆ allowed := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := mem_map.mp hv
  exact w.property

omit [Fintype V] [DecidableEq V] in
theorem allowed_map_univ (allowed : Finset V) :
    (univ : Finset {v : V // v ∈ allowed}).map (allowedEmbedding allowed) = allowed := by
  ext v
  simp [allowedEmbedding]

omit [Fintype V] [DecidableEq V] in
theorem partitionWithin_induce (G : SimpleGraph V) (activity : V → ℝ) (allowed : Finset V) :
    partitionWithin G activity allowed =
      partitionFunction (G.induce (allowed : Set V)) (fun v => activity v.val) := by
  calc
    _ = partitionWithin G activity (univ.map (allowedEmbedding allowed)) := by rw [allowed_map_univ]
    _ = partitionWithin (G.induce (allowed : Set V)) (fun v => activity v.val) univ :=
      partitionWithin_map _ _ _ (fun _ _ => Iff.rfl) activity univ
    _ = _ := partitionWithin_univ _ _

omit [Fintype V] [DecidableEq V] in
theorem configurationWeight_allowed_map (G : SimpleGraph V) (activity : V → ℝ) (allowed : Finset V)
    (s : Finset {v : V // v ∈ allowed}) :
    configurationWeight G activity (s.map (allowedEmbedding allowed)) =
      configurationWeight (G.induce (allowed : Set V)) (fun v => activity v.val) s := by
  unfold configurationWeight
  rw [independent_map_iff (G.induce (allowed : Set V)) G (allowedEmbedding allowed) (fun _ _ => Iff.rfl)]
  split_ifs
  · exact prod_map _ _ _
  · rfl

/-- Exact expectation transport, including every function of the original vertex coordinates. -/
theorem hardCoreWithin_expectation_induce (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (f : Finset V → ℝ) :
    (hardCoreWithin G activity ha allowed).expectation f =
      (hardCoreLaw (G.induce (allowed : Set V)) (fun v => activity v.val) (fun v => ha v.val)).expectation
        (fun s => f (s.map (allowedEmbedding allowed))) := by
  unfold FiniteLaw.expectation
  simp only [hardCoreWithin, withinWeight, ite_div, zero_div, ite_mul, zero_mul]
  rw [← sum_filter]
  symm
  apply sum_bij (fun s _ => s.map (allowedEmbedding allowed))
  · intro s _
    simp only [mem_filter, mem_univ, true_and]
    exact allowed_map_subset allowed s
  · intro s _ t _ he
    exact Finset.map_injective _ he
  · intro s hs
    have hsub : s ⊆ allowed := (mem_filter.mp hs).2
    refine ⟨s.subtype (fun v => v ∈ allowed), mem_univ _, ?_⟩
    exact subtype_map_of_mem (fun v hv => hsub hv)
  · intro s _
    rw [hardCoreLaw_mass, configurationWeight_allowed_map, partitionWithin_induce]

omit [Fintype V] in
@[simp] theorem occupation_allowed_map (allowed : Finset V) (v : {v : V // v ∈ allowed})
    (s : Finset {v : V // v ∈ allowed}) :
    occupation v.val (s.map (allowedEmbedding allowed)) = occupation v s := by
  simp [occupation, allowedEmbedding]

omit [Fintype V] in
theorem occupation_allowed_map_outside (allowed : Finset V) (v : V) (hv : v ∉ allowed)
    (s : Finset {v : V // v ∈ allowed}) : occupation v (s.map (allowedEmbedding allowed)) = 0 := by
  have hn : v ∉ s.map (allowedEmbedding allowed) := fun h => hv (allowed_map_subset allowed s h)
  simp [occupation, hn]

theorem hardCoreWithin_marginal_induce (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (v : {v : V // v ∈ allowed}) :
    marginal (hardCoreWithin G activity ha allowed) v.val =
      marginal (hardCoreLaw (G.induce (allowed : Set V)) (fun v => activity v.val) (fun v => ha v.val)) v := by
  unfold marginal
  rw [hardCoreWithin_expectation_induce]
  simp only [occupation_allowed_map]

theorem hardCoreWithin_marginal_outside (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (v : V) (hv : v ∉ allowed) :
    marginal (hardCoreWithin G activity ha allowed) v = 0 := by
  unfold marginal
  rw [hardCoreWithin_expectation_induce]
  simp only [occupation_allowed_map_outside allowed v hv, FiniteLaw.expectation_const]

theorem hardCoreWithin_correlation_induce (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (u v : {v : V // v ∈ allowed}) :
    correlationMatrix (hardCoreWithin G activity ha allowed) u.val v.val =
      correlationMatrix (hardCoreLaw (G.induce (allowed : Set V)) (fun v => activity v.val) (fun v => ha v.val)) u v := by
  unfold correlationMatrix occupationCovariance occupationVariance
  simp only [occupation_variance, hardCoreWithin_marginal_induce]
  rw [FiniteLaw.covariance_eq_mixed_moment, FiniteLaw.covariance_eq_mixed_moment]
  change (_ - marginal _ u.val * marginal _ v.val) / _ = (_ - marginal _ u * marginal _ v) / _
  rw [hardCoreWithin_marginal_induce, hardCoreWithin_marginal_induce, hardCoreWithin_expectation_induce]
  simp only [occupation_allowed_map]

theorem hardCoreWithin_correlation_outside_right (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (u v : V) (hv : v ∉ allowed) :
    correlationMatrix (hardCoreWithin G activity ha allowed) u v = 0 := by
  have hvar : (hardCoreWithin G activity ha allowed).variance (occupation v) = 0 := by
    rw [occupation_variance, hardCoreWithin_marginal_outside G activity ha allowed v hv]
    ring
  unfold correlationMatrix occupationCovariance
  rw [FiniteLaw.covariance_eq_zero_of_variance_eq_zero _ _ _ hvar, zero_div]

omit [DecidableEq V] in
theorem sum_over_allowed (allowed : Finset V) (f : V → ℝ) (hf : ∀ v, v ∉ allowed → f v = 0) :
    (∑ v, f v) = ∑ v : {v : V // v ∈ allowed}, f v.val := by
  rw [← Finset.sum_subtype (p := fun v => v ∈ allowed) allowed (fun _ => Iff.rfl) f]
  symm
  exact sum_subset (subset_univ allowed) (fun v _ hv => hf v hv)

/-- Adjoining deterministic vacant coordinates preserves the exact quadratic correlation bound. -/
theorem hardCoreWithin_correlationBound (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) {C : ℝ} (hC : 0 ≤ C)
    (hc : CorrelationBound (hardCoreLaw (G.induce (allowed : Set V))
      (fun v => activity v.val) (fun v => ha v.val)) C) :
    CorrelationBound (hardCoreWithin G activity ha allowed) C := by
  intro c
  have hz (u v : V) (h : u ∉ allowed ∨ v ∉ allowed) :
      c u * correlationMatrix (hardCoreWithin G activity ha allowed) u v * c v = 0 := by
    rcases h with hu|hv
    · rw [correlationMatrix_symm, hardCoreWithin_correlation_outside_right G activity ha allowed v u hu]
      ring
    · rw [hardCoreWithin_correlation_outside_right G activity ha allowed u v hv]
      ring
  have hs : (∑ u, ∑ v, c u * correlationMatrix (hardCoreWithin G activity ha allowed) u v * c v) =
      ∑ u : {v : V // v ∈ allowed}, ∑ v : {v : V // v ∈ allowed},
        c u.val * correlationMatrix (hardCoreWithin G activity ha allowed) u.val v.val * c v.val := by
    have hi (u : V) : (∑ v, c u * correlationMatrix (hardCoreWithin G activity ha allowed) u v * c v) =
        ∑ v : {v : V // v ∈ allowed}, c u * correlationMatrix (hardCoreWithin G activity ha allowed) u v.val * c v.val :=
      sum_over_allowed allowed _ (fun v hv => hz u v (Or.inr hv))
    simp_rw [hi]
    apply sum_over_allowed allowed
    intro u hu
    exact sum_eq_zero (fun v _ => hz u v.val (Or.inl hu))
  rw [hs]
  simp_rw [hardCoreWithin_correlation_induce]
  apply (hc (fun v => c v.val)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have he : (∑ v ∈ allowed, c v^2) ≤ ∑ v, c v^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ allowed) (fun v _ _ => sq_nonneg _)
  convert he using 1
  exact (Finset.sum_subtype (p := fun v => v ∈ allowed) allowed (fun _ => Iff.rfl) (fun v => c v^2)).symm

end HardCoreActivityThreshold
