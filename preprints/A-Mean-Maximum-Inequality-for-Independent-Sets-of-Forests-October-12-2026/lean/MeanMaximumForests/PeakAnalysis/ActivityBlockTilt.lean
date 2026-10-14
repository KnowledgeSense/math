import MeanMaximumForests.PeakAnalysis.FiniteTiltLog
import MeanMaximumForests.PeakAnalysis.PartitionDeletion

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def blockActivity (activity : V → ℝ) (L : Finset V) (t : ℝ) (v : V) : ℝ :=
  activity v * if v ∈ L then Real.exp t else 1

omit [Fintype V] in
theorem blockActivity_pos (activity : V → ℝ) (ha : ∀ v, 0 < activity v) (L : Finset V) (t : ℝ) :
    ∀ v, 0 < blockActivity activity L t v := by
  intro v
  unfold blockActivity
  split_ifs <;> positivity [ha v]

noncomputable def blockCard (L : Finset V) (I : Finset V) : ℝ := (I ∩ L).card

omit [Fintype V] in
theorem configurationWeight_blockActivity (G : SimpleGraph V) (activity : V → ℝ)
    (L : Finset V) (t : ℝ) (I : Finset V) :
    configurationWeight G (blockActivity activity L t) I =
      configurationWeight G activity I * Real.exp (t * blockCard L I) := by
  have hprod : (∏ v ∈ I, if v ∈ L then Real.exp t else 1) = Real.exp (t * blockCard L I) := by
    rw [← prod_filter]
    have hs : I.filter (fun v => v ∈ L) = I ∩ L := by ext v; simp
    rw [hs, prod_const, ← Real.exp_nat_mul]
    unfold blockCard
    congr 1
    ring
  unfold configurationWeight
  split_ifs
  · simp only [blockActivity, prod_mul_distrib, hprod]
  · simp

theorem block_tiltPartition (G : SimpleGraph V) (activity : V → ℝ) (ha : ∀ v, 0 < activity v)
    (L : Finset V) (t : ℝ) :
    tiltPartition (hardCoreLaw G activity ha) (blockCard L) t =
      partitionFunction G (blockActivity activity L t) / partitionFunction G activity := by
  unfold tiltPartition tiltMoment
  simp only [hardCoreLaw_mass, mul_one, div_mul_eq_mul_div, ← sum_div]
  congr 1
  unfold partitionFunction
  apply sum_congr rfl
  intro I _
  exact (configurationWeight_blockActivity G activity L t I).symm

theorem finiteTilt_blockActivity (G : SimpleGraph V) (activity : V → ℝ) (ha : ∀ v, 0 < activity v)
    (L : Finset V) (t : ℝ) :
    finiteTilt (hardCoreLaw G activity ha) (blockCard L) t =
      hardCoreLaw G (blockActivity activity L t) (blockActivity_pos activity ha L t) := by
  apply FiniteLaw.ext
  intro I
  change (hardCoreLaw G activity ha).mass I * Real.exp (t * blockCard L I) /
    (hardCoreLaw G activity ha).expectation (fun I => Real.exp (t * blockCard L I)) = _
  have he : (hardCoreLaw G activity ha).expectation (fun I => Real.exp (t * blockCard L I)) =
      tiltPartition (hardCoreLaw G activity ha) (blockCard L) t := by
    simp only [FiniteLaw.expectation, tiltPartition, tiltMoment, mul_one]
  rw [he, block_tiltPartition, hardCoreLaw_mass, hardCoreLaw_mass, configurationWeight_blockActivity]
  have hz := (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  have hzt := (partitionFunction_pos G (blockActivity activity L t)
    (fun v => (blockActivity_pos activity ha L t v).le)).ne'
  field_simp

omit [Fintype V] in
theorem sum_occupation_block (L I : Finset V) : (∑ v ∈ L, occupation v I) = blockCard L I := by
  simp [occupation, blockCard, inter_comm]

theorem expectation_blockCard (μ : FiniteLaw (Finset V)) (L : Finset V) :
    μ.expectation (blockCard L) = ∑ v ∈ L, marginal μ v := by
  have he : blockCard L = fun I => ∑ v ∈ L, occupation v I := by
    funext I
    exact (sum_occupation_block L I).symm
  rw [he]
  unfold marginal FiniteLaw.expectation
  simp only [mul_sum]
  exact sum_comm

end MeanMaximumForests.PeakAnalysis
