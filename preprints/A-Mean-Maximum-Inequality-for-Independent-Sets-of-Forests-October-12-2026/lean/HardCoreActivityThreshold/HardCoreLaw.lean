import HardCoreActivityThreshold.FiniteProbability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset

/-! The hard-core law on actual vertex subsets, including heterogeneous activities. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A configuration is admissible precisely when its occupied vertices are independent. -/
def Independent (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

omit [Fintype V] [DecidableEq V] in
@[simp] theorem independent_empty (G : SimpleGraph V) : Independent G ∅ := by
  simp [Independent]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem independent_singleton (G : SimpleGraph V) (v : V) :
    Independent G {v} := by
  simp [Independent]

noncomputable def configurationWeight (G : SimpleGraph V) (activity : V → ℝ)
    (s : Finset V) : ℝ :=
  if Independent G s then ∏ v ∈ s, activity v else 0

noncomputable def partitionFunction (G : SimpleGraph V) (activity : V → ℝ) : ℝ :=
  ∑ s : Finset V, configurationWeight G activity s

omit [Fintype V] [DecidableEq V] in
@[simp] theorem configurationWeight_empty (G : SimpleGraph V) (activity : V → ℝ) :
    configurationWeight G activity ∅ = 1 := by
  simp [configurationWeight]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem configurationWeight_singleton (G : SimpleGraph V) (activity : V → ℝ)
    (v : V) : configurationWeight G activity {v} = activity v := by
  simp [configurationWeight]

omit [Fintype V] [DecidableEq V] in
theorem configurationWeight_nonneg (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 ≤ activity v) (s : Finset V) : 0 ≤ configurationWeight G activity s := by
  unfold configurationWeight
  split_ifs
  · exact prod_nonneg (fun v _ => ha v)
  · rfl

omit [Fintype V] [DecidableEq V] in
theorem configurationWeight_pos_iff (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (s : Finset V) :
    0 < configurationWeight G activity s ↔ Independent G s := by
  unfold configurationWeight
  split_ifs with h
  · exact iff_of_true (prod_pos (fun v _ => ha v)) h
  · simp [h]

omit [DecidableEq V] in
theorem partitionFunction_pos (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 ≤ activity v) : 0 < partitionFunction G activity := by
  apply sum_pos'
  · intro s _
    exact configurationWeight_nonneg G activity ha s
  · exact ⟨∅, mem_univ _, by simp⟩

/-- The actual normalized hard-core probability law, zero on non-independent subsets. -/
noncomputable def hardCoreLaw (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) : FiniteLaw (Finset V) where
  mass s := configurationWeight G activity s / partitionFunction G activity
  nonneg s := div_nonneg (configurationWeight_nonneg G activity (fun v => (ha v).le) s)
    (partitionFunction_pos G activity (fun v => (ha v).le)).le
  sum_one := by
    rw [← sum_div]
    exact div_self (partitionFunction_pos G activity (fun v => (ha v).le)).ne'

omit [DecidableEq V] in
@[simp] theorem hardCoreLaw_mass (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (s : Finset V) :
    (hardCoreLaw G activity ha).mass s =
      configurationWeight G activity s / partitionFunction G activity := rfl

omit [DecidableEq V] in
theorem hardCoreLaw_support (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (s : Finset V) :
    0 < (hardCoreLaw G activity ha).mass s ↔ Independent G s := by
  rw [hardCoreLaw_mass, div_pos_iff_of_pos_right
    (partitionFunction_pos G activity (fun v => (ha v).le))]
  exact configurationWeight_pos_iff G activity ha s

noncomputable def occupation (v : V) (s : Finset V) : ℝ := if v ∈ s then 1 else 0

omit [Fintype V] in
@[simp] theorem occupation_sq (v : V) (s : Finset V) : occupation v s ^ 2 = occupation v s := by
  unfold occupation
  split_ifs <;> norm_num

noncomputable def marginal (μ : FiniteLaw (Finset V)) (v : V) : ℝ :=
  μ.expectation (occupation v)

theorem marginal_eq_eventMass (μ : FiniteLaw (Finset V)) (v : V) :
    marginal μ v = μ.eventMass (fun s => v ∈ s) := by
  unfold marginal FiniteLaw.expectation FiniteLaw.eventMass occupation
  apply sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem marginal_nonneg (μ : FiniteLaw (Finset V)) (v : V) : 0 ≤ marginal μ v := by
  rw [marginal_eq_eventMass]
  exact μ.eventMass_nonneg _

theorem marginal_le_one (μ : FiniteLaw (Finset V)) (v : V) : marginal μ v ≤ 1 := by
  rw [marginal_eq_eventMass]
  exact μ.eventMass_le_one _

theorem hardCore_marginal_pos (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) : 0 < marginal (hardCoreLaw G activity ha) v := by
  rw [marginal_eq_eventMass]
  apply sum_pos'
  · intro s _
    split_ifs
    · exact (hardCoreLaw G activity ha).nonneg s
    · rfl
  · refine ⟨{v}, mem_univ _, ?_⟩
    simp only [mem_singleton, ite_true]
    exact (hardCoreLaw_support G activity ha {v}).mpr (independent_singleton G v)

theorem hardCore_marginal_lt_one (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) : marginal (hardCoreLaw G activity ha) v < 1 := by
  rw [marginal_eq_eventMass, ← (hardCoreLaw G activity ha).sum_one]
  apply sum_lt_sum
  · intro s _
    split_ifs
    · exact le_refl _
    · exact (hardCoreLaw G activity ha).nonneg s
  · refine ⟨∅, mem_univ _, ?_⟩
    simpa only [Finset.notMem_empty, ite_false] using
      (hardCoreLaw_support G activity ha ∅).mpr (independent_empty G)

theorem occupation_variance (μ : FiniteLaw (Finset V)) (v : V) :
    μ.variance (occupation v) = marginal μ v * (1 - marginal μ v) := by
  rw [μ.variance_eq_second_moment]
  simp only [occupation_sq]
  unfold marginal
  ring

theorem hardCore_occupation_variance_pos (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) :
    0 < (hardCoreLaw G activity ha).variance (occupation v) := by
  rw [occupation_variance]
  exact mul_pos (hardCore_marginal_pos G activity ha v)
    (sub_pos.mpr (hardCore_marginal_lt_one G activity ha v))

omit [Fintype V] [DecidableEq V] in
/-- Multiplying activities by a local field multiplies configuration weights by that field. -/
theorem configurationWeight_field (G : SimpleGraph V) (activity field : V → ℝ)
    (s : Finset V) :
    configurationWeight G (fun v => activity v * field v) s =
      configurationWeight G activity s * ∏ v ∈ s, field v := by
  unfold configurationWeight
  split_ifs <;> simp [prod_mul_distrib]

/-- A partial assignment fixes occupied and unoccupied vertices in the specified set. -/
def agreesWith (pinned occupied : Finset V) (s : Finset V) : Prop :=
  s ∩ pinned = occupied

/-- The actual pinned hard-core law, conditioned on a feasible assignment. -/
noncomputable def pinnedHardCoreLaw (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (pinned occupied : Finset V)
    (hfeasible : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    FiniteLaw (Finset V) :=
  (hardCoreLaw G activity ha).condition (agreesWith pinned occupied) hfeasible

end HardCoreActivityThreshold
