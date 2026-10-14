import MeanMaximumForests.PeakAnalysis.GraphTilt
import MeanMaximumForests.IndependenceCoefficients
import MeanMaximumForests.GraphPeaks

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- The actual probability that the independent-set cardinality equals `k`, at log activity `t`. -/
noncomputable def graphTiltSizeMass (G : SimpleGraph V) (t : ℝ) (k : ℕ) : ℝ :=
  (hardCoreLaw G (fun _ => Real.exp t) (fun _ => Real.exp_pos t)).expectation
    (fun s => if s.card = k then 1 else 0)

theorem graphTiltSizeMass_eq (G : SimpleGraph V) (t : ℝ) (k : ℕ) :
    graphTiltSizeMass G t k = (independentSetCoefficient G univ k : ℝ) *
      Real.exp (t * k) / partitionFunction G (fun _ => Real.exp t) := by
  unfold graphTiltSizeMass FiniteLaw.expectation
  simp only [hardCoreLaw_mass]
  simp_rw [configurationWeight_exp]
  simp only [configurationWeight, prod_const_one]
  simp_rw [div_mul_eq_mul_div, mul_ite, mul_one, mul_zero]
  rw [← sum_div]
  congr 1
  have he (s : Finset V) : (if HardCoreActivityThreshold.Independent G s then 1 else 0) *
      Real.exp (t * (s.card : ℝ)) * (if s.card = k then 1 else 0) =
      if HardCoreActivityThreshold.Independent G s ∧ s.card = k then Real.exp (t * k) else 0 := by
    split_ifs <;> simp_all
  have hsum : (∑ s : Finset V,
      if s.card = k then (if HardCoreActivityThreshold.Independent G s then 1 else 0) *
        Real.exp (t * (s.card : ℝ)) else 0) =
      ∑ s : Finset V, if HardCoreActivityThreshold.Independent G s ∧ s.card = k then
        Real.exp (t * k) else 0 := by
    apply sum_congr rfl
    intro s _
    simpa only [mul_ite, mul_one, mul_zero] using he s
  rw [hsum]
  have hsets : univ.filter (fun s : Finset V => HardCoreActivityThreshold.Independent G s ∧ s.card = k) =
      (independentSetsWithin G univ).filter (fun s => s.card = k) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_independentSetsWithin, subset_univ]
    rfl
  rw [← sum_filter, hsets, sum_const, nsmul_eq_mul]
  rfl

theorem graphTiltSizeMass_pos (G : SimpleGraph V) (t : ℝ) {k : ℕ} (hk : k ≤ G.indepNum) :
    0 < graphTiltSizeMass G t k := by
  rw [graphTiltSizeMass_eq]
  refine div_pos (mul_pos ?_ (Real.exp_pos _))
    (partitionFunction_pos G _ (fun _ => (Real.exp_pos t).le))
  apply Nat.cast_pos.mpr
  exact (coefficient_pos_iff_le G univ k).mpr (by simpa only [independenceNumber_univ] using hk)

theorem weakLocalPeak_tilt_mass_step (G : SimpleGraph V) (t : ℝ) {k : ℕ}
    (hk : WeakLocalPeak G k) :
    graphTiltSizeMass G t (k + 1) ≤ Real.exp t * graphTiltSizeMass G t k := by
  rw [graphTiltSizeMass_eq, graphTiltSizeMass_eq]
  have he : Real.exp (t * ((k + 1 : ℕ) : ℝ)) = Real.exp t * Real.exp (t * k) := by
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
    ring
  rw [he]
  have hcoef : (independentSetCoefficient G univ (k + 1) : ℝ) ≤ independentSetCoefficient G univ k :=
    Nat.cast_le.mpr hk.2.2
  have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ Real.exp t * Real.exp (t * k))
  have hd := div_le_div_of_nonneg_right hm
    (partitionFunction_pos G (fun _ => Real.exp t) (fun _ => (Real.exp_pos t).le)).le
  convert hd using 1
  ring

end MeanMaximumForests.PeakAnalysis
