import HardCoreActivityThreshold.HardCoreLaw
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Correlation and influence matrices of actual occupation random variables. -/
namespace HardCoreActivityThreshold
open Finset
open scoped ENNReal
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def jointOccupation (μ : FiniteLaw (Finset V)) (u v : V) : ℝ :=
  μ.eventMass (fun s => u ∈ s ∧ v ∈ s)

noncomputable def occupationVariance (μ : FiniteLaw (Finset V)) (v : V) : ℝ :=
  μ.variance (occupation v)

noncomputable def occupationCovariance (μ : FiniteLaw (Finset V)) (u v : V) : ℝ :=
  μ.covariance (occupation u) (occupation v)

theorem occupation_product_expectation (μ : FiniteLaw (Finset V)) (u v : V) :
    μ.expectation (fun s => occupation u s * occupation v s) = jointOccupation μ u v := by
  unfold FiniteLaw.expectation jointOccupation FiniteLaw.eventMass occupation
  apply sum_congr rfl
  intro s _
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp [hu, hv]

theorem occupationCovariance_eq (μ : FiniteLaw (Finset V)) (u v : V) :
    occupationCovariance μ u v = jointOccupation μ u v - marginal μ u * marginal μ v := by
  unfold occupationCovariance
  rw [μ.covariance_eq_mixed_moment, occupation_product_expectation]
  rfl

theorem absent_eventMass (μ : FiniteLaw (Finset V)) (u : V) :
    μ.eventMass (fun s => u ∉ s) = 1 - marginal μ u := by
  rw [marginal_eq_eventMass, ← μ.sum_one]
  unfold FiniteLaw.eventMass
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro s _
  by_cases hu : u ∈ s <;> simp [hu]

theorem absent_jointMass (μ : FiniteLaw (Finset V)) (u v : V) :
    μ.eventMass (fun s => u ∉ s ∧ v ∈ s) = marginal μ v - jointOccupation μ u v := by
  rw [marginal_eq_eventMass]
  unfold jointOccupation FiniteLaw.eventMass
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro s _
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp [hu, hv]

/-- Occupation probability at `v` conditioned on the specified value at `u`. -/
noncomputable def conditionalOccupation (μ : FiniteLaw (Finset V)) (u : V)
    (occupied : Bool) (v : V) : ℝ :=
  if occupied then jointOccupation μ u v / marginal μ u
  else μ.eventMass (fun s => u ∉ s ∧ v ∈ s) / μ.eventMass (fun s => u ∉ s)

theorem conditionalOccupation_difference (μ : FiniteLaw (Finset V)) (u v : V)
    (hpos : 0 < marginal μ u) (hlt : marginal μ u < 1) :
    conditionalOccupation μ u true v - conditionalOccupation μ u false v =
      occupationCovariance μ u v / occupationVariance μ u := by
  simp only [conditionalOccupation, ite_true, Bool.false_eq_true, ite_false,
    absent_jointMass, absent_eventMass, occupationVariance, occupation_variance,
    occupationCovariance_eq]
  have ha : marginal μ u ≠ 0 := ne_of_gt hpos
  have hb : 1 - marginal μ u ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  field_simp
  ring

/-- The correlation matrix uses the actual covariance and occupation variances. -/
noncomputable def correlationMatrix (μ : FiniteLaw (Finset V)) : Matrix V V ℝ := fun u v =>
  occupationCovariance μ u v /
    Real.sqrt (occupationVariance μ u * occupationVariance μ v)

theorem correlationMatrix_symm (μ : FiniteLaw (Finset V)) (u v : V) :
    correlationMatrix μ u v = correlationMatrix μ v u := by
  unfold correlationMatrix occupationCovariance
  rw [μ.covariance_symm, mul_comm (occupationVariance μ u)]

theorem correlationMatrix_diag (μ : FiniteLaw (Finset V)) (v : V)
    (hv : 0 < occupationVariance μ v) : correlationMatrix μ v v = 1 := by
  unfold correlationMatrix occupationCovariance
  rw [μ.covariance_self]
  change occupationVariance μ v / Real.sqrt (occupationVariance μ v * occupationVariance μ v) = 1
  rw [Real.sqrt_mul_self hv.le, div_self hv.ne']

/-- The absolute influence matrix, with deterministic coordinates and the diagonal set to zero. -/
noncomputable def influenceMatrix (μ : FiniteLaw (Finset V)) : Matrix V V ℝ := fun u v =>
  if u = v ∨ occupationVariance μ u = 0 then 0
  else |conditionalOccupation μ u true v - conditionalOccupation μ u false v|

@[simp] theorem influenceMatrix_diag (μ : FiniteLaw (Finset V)) (v : V) :
    influenceMatrix μ v v = 0 := by simp [influenceMatrix]

theorem influenceMatrix_nonneg (μ : FiniteLaw (Finset V)) (u v : V) :
    0 ≤ influenceMatrix μ u v := by
  unfold influenceMatrix
  split_ifs
  · rfl
  · exact abs_nonneg _

theorem influenceMatrix_eq_covariance (μ : FiniteLaw (Finset V)) {u v : V}
    (huv : u ≠ v) (hpos : 0 < marginal μ u) (hlt : marginal μ u < 1) :
    influenceMatrix μ u v = |occupationCovariance μ u v| / occupationVariance μ u := by
  have hv : 0 < occupationVariance μ u := by
    unfold occupationVariance
    rw [occupation_variance]
    exact mul_pos hpos (sub_pos.mpr hlt)
  simp only [influenceMatrix, huv, hv.ne', or_self, ite_false]
  rw [conditionalOccupation_difference μ u v hpos hlt, abs_div, abs_of_pos hv]

/-- Spectral radius over the complex spectrum, not a matrix-norm surrogate. -/
noncomputable def influenceSpectralRadius (μ : FiniteLaw (Finset V)) : ℝ≥0∞ :=
  spectralRadius ℂ ((influenceMatrix μ).map (fun x : ℝ => (x : ℂ)))

/-- External fields are applied to the actual probability law before conditioning. -/
noncomputable def fieldWeight (field : V → ℝ) (s : Finset V) : ℝ := ∏ v ∈ s, field v

omit [Fintype V] [DecidableEq V] in
theorem fieldWeight_pos (field : V → ℝ) (hfield : ∀ v, 0 < field v) (s : Finset V) :
    0 < fieldWeight field s := prod_pos (fun v _ => hfield v)

omit [DecidableEq V] in
theorem field_expectation_pos (μ : FiniteLaw (Finset V)) (field : V → ℝ)
    (hfield : ∀ v, 0 < field v) : 0 < μ.expectation (fieldWeight field) := by
  have hex : ∃ s, 0 < μ.mass s := by
    by_contra! h
    have hz : ∑ s, μ.mass s ≤ 0 := sum_nonpos (fun s _ => h s)
    rw [μ.sum_one] at hz
    norm_num at hz
  obtain ⟨s, hs⟩ := hex
  apply sum_pos'
  · intro t _
    exact mul_nonneg (μ.nonneg t) (fieldWeight_pos field hfield t).le
  · exact ⟨s, mem_univ _, mul_pos hs (fieldWeight_pos field hfield s)⟩

noncomputable def applyField (μ : FiniteLaw (Finset V)) (field : V → ℝ)
    (hfield : ∀ v, 0 < field v) : FiniteLaw (Finset V) :=
  μ.reweight (fieldWeight field) (fun s => (fieldWeight_pos field hfield s).le)
    (field_expectation_pos μ field hfield)

/-- Complete spectral independence quantifies over every positive field at most one,
and every feasible partial assignment. Pinned coordinates add only zero rows/columns. -/
def CompletelySpectrallyIndependent (μ : FiniteLaw (Finset V)) (η : ℝ) : Prop :=
  ∀ (field : V → ℝ) (hfield : ∀ v, 0 < field v), (∀ v, field v ≤ 1) →
    ∀ (pinned occupied : Finset V)
      (hpin : 0 < (applyField μ field hfield).eventMass (agreesWith pinned occupied)),
      influenceSpectralRadius
        ((applyField μ field hfield).condition (agreesWith pinned occupied) hpin) ≤
          ENNReal.ofReal η

end HardCoreActivityThreshold
