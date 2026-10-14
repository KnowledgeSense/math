import MeanMaximumForests.GraphInvariants
import HardCoreActivityThreshold.CovarianceResponse
import HardCoreActivityThreshold.CorrelationQuadratic

/-! A linear variance bound for the actual uniform independent-set size.
The dependency's covariance theorem is proved for arbitrary-degree forests;
activity one is checked to lie strictly inside its admissible interval. -/
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

namespace MeanMaximumForests
attribute [local instance] Classical.propDecidable
open Finset
open HardCoreActivityThreshold hiding Independent independent_empty
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized hard-core law at activity one. -/
noncomputable def uniformIndependentSetLaw (G : SimpleGraph V) : FiniteLaw (Finset V) :=
  hardCoreLaw G (fun _ => 1) (fun _ => by norm_num)

omit [DecidableEq V] in
theorem independent_filter_univ (G : SimpleGraph V) :
    univ.filter (HardCoreActivityThreshold.Independent G) = independentSetsWithin G univ := by
  classical
  ext s
  simp only [mem_filter, mem_univ, true_and, mem_independentSetsWithin, subset_univ]
  rfl

omit [DecidableEq V] in
theorem partitionFunction_one (G : SimpleGraph V) :
    partitionFunction G (fun _ => 1) = (independentSetCount G univ : ℝ) := by
  classical
  unfold partitionFunction configurationWeight
  simp only [prod_const_one]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, independent_filter_univ, independentSetCount]

omit [DecidableEq V] in
theorem uniformIndependentSetLaw_expectation (G : SimpleGraph V) (f : Finset V → ℝ) :
    (uniformIndependentSetLaw G).expectation f =
      (∑ s ∈ independentSetsWithin G univ, f s) / independentSetCount G univ := by
  classical
  unfold uniformIndependentSetLaw FiniteLaw.expectation
  simp only [hardCoreLaw_mass, configurationWeight, prod_const_one, partitionFunction_one]
  simp_rw [div_mul_eq_mul_div, ite_mul, one_mul, zero_mul]
  rw [← sum_div, ← sum_filter, independent_filter_univ]

omit [DecidableEq V] in
theorem uniformIndependentSetLaw_mean (G : SimpleGraph V) :
    (uniformIndependentSetLaw G).expectation (fun s => (s.card : ℝ)) = graphMean G := by
  rw [uniformIndependentSetLaw_expectation]
  unfold graphMean meanIndependentSetSize independentSetSizeSum
  norm_cast

/-- Variance of the independent-set cardinality under the uniform law, written as an actual sum. -/
noncomputable def graphVariance (G : SimpleGraph V) : ℝ :=
  (∑ s ∈ independentSetsWithin G univ, ((s.card : ℝ) - graphMean G) ^ 2) /
    independentSetCount G univ

omit [DecidableEq V] in
theorem uniformIndependentSetLaw_variance (G : SimpleGraph V) :
    (uniformIndependentSetLaw G).variance (fun s => (s.card : ℝ)) = graphVariance G := by
  unfold FiniteLaw.variance
  rw [uniformIndependentSetLaw_mean, uniformIndependentSetLaw_expectation]
  rfl

theorem sum_occupation_card (s : Finset V) : (∑ v, occupation v s) = (s.card : ℝ) := by
  classical
  simp [occupation]

theorem expectation_card_eq_sum_marginal (μ : FiniteLaw (Finset V)) :
    μ.expectation (fun s => (s.card : ℝ)) = ∑ v, marginal μ v := by
  simp only [marginal, ← μ.expectation_sum]
  congr 1
  funext s
  exact (sum_occupation_card s).symm

/-- A correlation quadratic bound controls the variance of the cardinality statistic itself. -/
theorem cardinal_variance_le_of_correlation (μ : FiniteLaw (Finset V)) (C : ℝ)
    (hC : 0 ≤ C) (hc : CorrelationBound μ C) (hv : ∀ v, 0 < occupationVariance μ v) :
    μ.variance (fun s => (s.card : ℝ)) ≤ C * (Fintype.card V : ℝ) / 4 := by
  let c : V → ℝ := fun v => Real.sqrt (occupationVariance μ v)
  have hs : ∀ s, linearOccupation μ c s =
      (s.card : ℝ) - μ.expectation (fun t => (t.card : ℝ)) := by
    intro s
    have hc' : ∀ v, c v * normalizedOccupation μ v s = occupation v s - marginal μ v := by
      intro v
      have hne : Real.sqrt (occupationVariance μ v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hv v))
      dsimp [c, normalizedOccupation]
      field_simp
    simp only [linearOccupation, hc', sum_sub_distrib, sum_occupation_card,
      expectation_card_eq_sum_marginal]
  have hvar : μ.variance (linearOccupation μ c) = μ.variance (fun s => (s.card : ℝ)) := by
    conv_lhs => rw [FiniteLaw.variance, linearOccupation_mean]
    simp only [sub_zero, hs]
    rfl
  have hb := hc c
  rw [correlation_quadratic_variance, hvar] at hb
  have hsum : (∑ v, c v ^ 2) ≤ (Fintype.card V : ℝ) / 4 := by
    calc
      _ = ∑ v, occupationVariance μ v := by
        apply sum_congr rfl
        intro v _
        exact Real.sq_sqrt (hv v).le
      _ ≤ ∑ _v : V, (1 / 4 : ℝ) := by
        apply sum_le_sum
        intro v _
        unfold occupationVariance
        rw [occupation_variance]
        nlinarith [sq_nonneg (marginal μ v - 1 / 2)]
      _ = _ := by simp [div_eq_mul_inv]
  calc
    _ ≤ C * ∑ v, c v ^ 2 := hb
    _ ≤ C * ((Fintype.card V : ℝ) / 4) := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring

end MeanMaximumForests
