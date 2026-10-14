import MeanMaximumForests.PeakAnalysis.FiniteTilt
import MeanMaximumForests.PeakAnalysis.TiltVariance

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem configurationWeight_exp (G : SimpleGraph V) (t : ℝ) (s : Finset V) :
    configurationWeight G (fun _ => Real.exp t) s =
      configurationWeight G (fun _ => 1) s * Real.exp (t * (s.card : ℝ)) := by
  unfold configurationWeight
  split_ifs
  · simp only [prod_const_one, one_mul, prod_const]
    rw [mul_comm, Real.exp_nat_mul]
  · simp

theorem graph_tiltPartition (G : SimpleGraph V) (t : ℝ) :
    tiltPartition (uniformIndependentSetLaw G) (fun s => (s.card : ℝ)) t =
      partitionFunction G (fun _ => Real.exp t) / partitionFunction G (fun _ => 1) := by
  unfold tiltPartition tiltMoment uniformIndependentSetLaw
  simp only [hardCoreLaw_mass, mul_one, div_mul_eq_mul_div, ← sum_div]
  congr 1
  unfold partitionFunction
  apply sum_congr rfl
  intro s _
  exact (configurationWeight_exp G t s).symm

theorem graph_finiteTilt (G : SimpleGraph V) (t : ℝ) :
    finiteTilt (uniformIndependentSetLaw G) (fun s => (s.card : ℝ)) t =
      hardCoreLaw G (fun _ => Real.exp t) (fun _ => Real.exp_pos t) := by
  apply FiniteLaw.ext
  intro s
  change (uniformIndependentSetLaw G).mass s * Real.exp (t * (s.card : ℝ)) /
    (uniformIndependentSetLaw G).expectation (fun s => Real.exp (t * (s.card : ℝ))) = _
  have hz : (uniformIndependentSetLaw G).expectation (fun s => Real.exp (t * (s.card : ℝ))) =
      tiltPartition (uniformIndependentSetLaw G) (fun s => (s.card : ℝ)) t := by
    simp only [FiniteLaw.expectation, tiltPartition, tiltMoment, mul_one]
  rw [hz, graph_tiltPartition]
  unfold uniformIndependentSetLaw
  rw [hardCoreLaw_mass, hardCoreLaw_mass, configurationWeight_exp]
  have hz1 := partitionFunction_pos G (fun _ => 1) (fun _ => by norm_num)
  have hzt := partitionFunction_pos G (fun _ => Real.exp t) (fun _ => (Real.exp_pos t).le)
  field_simp

noncomputable def graphTiltMean (G : SimpleGraph V) (t : ℝ) : ℝ :=
  (hardCoreLaw G (fun _ => Real.exp t) (fun _ => Real.exp_pos t)).expectation
    (fun s => (s.card : ℝ))

noncomputable def graphTiltVariance (G : SimpleGraph V) (t : ℝ) : ℝ :=
  (hardCoreLaw G (fun _ => Real.exp t) (fun _ => Real.exp_pos t)).variance
    (fun s => (s.card : ℝ))

theorem graphTiltMean_hasDerivAt (G : SimpleGraph V) (t : ℝ) :
    HasDerivAt (graphTiltMean G) (graphTiltVariance G t) t := by
  have h := finiteTilt_mean_hasDerivAt (uniformIndependentSetLaw G) (fun s => (s.card : ℝ)) t
  simp_rw [graph_finiteTilt] at h
  exact h

@[simp] theorem graphTiltMean_zero (G : SimpleGraph V) : graphTiltMean G 0 = graphMean G := by
  change (hardCoreLaw G (fun _ => Real.exp 0) _).expectation _ = _
  simp only [Real.exp_zero]
  exact uniformIndependentSetLaw_mean G

theorem graphTiltMean_quarter (G : SimpleGraph V) :
    graphTiltMean G (Real.log (1 / 4)) ≤ (Fintype.card V : ℝ) / 5 := by
  unfold graphTiltMean
  rw [expectation_card_eq_sum_marginal]
  have he : Real.exp (Real.log (1 / 4 : ℝ)) = 1 / 4 := Real.exp_log (by norm_num)
  have hm : ∀ v : V, marginal (hardCoreLaw G (fun _ => Real.exp (Real.log (1 / 4))) (fun _ => Real.exp_pos _)) v ≤
      (1 / 5 : ℝ) := by
    intro v
    have h := hardCore_marginal_cap G (fun _ => Real.exp (Real.log (1 / 4)))
      (fun _ => Real.exp_pos _) (Λ := 1 / 4) (by norm_num)
      (fun _ => he.le) v
    norm_num at h
    exact h
  calc
    _ ≤ ∑ _ : V, (1 / 5 : ℝ) := sum_le_sum fun v _ => hm v
    _ = _ := by simp; ring

end MeanMaximumForests.PeakAnalysis
