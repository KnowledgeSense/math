import RandomWalkSearch.EndpointCoverage
import RandomWalkSearch.LazyExitLaw

/-! # Actual one-setup consecutive endpoint algorithms

The policies, successful outputs, and charged costs are those of the shared
history-dependent oracle execution. The probability results integrate the actual
iid lazy tape; no success or expected-cost premise is imposed on the policies.
-/

noncomputable section
namespace RandomWalkSearch.EndpointPolicy

variable {X : Type*} [DecidableEq X]

theorem collectThenCheck_checkCost_le (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (Q : ℕ)
    (hmark : ∀ v, cover v → ∃ x ∈ tests v, o x = true)
    (hbound : ∀ v, cover v → (tests v).card ≤ Q) :
    checkCost (collectThenCheck cover tests) r o ≤ Q := by
  classical
  by_cases he : ∃ t, cover (trail r t).visited
  · obtain ⟨t, ht⟩ := he
    exact (collectThenCheck_costs cover tests r o t Q ht hmark hbound).2.2
  · apply iSup_le
    intro n
    cases n with
    | zero => simp [History.checks]
    | succ n =>
      rw [run_eq_trail cover tests r o n (fun j _ hj => he ⟨j, hj⟩), trail_checks]
      exact zero_le

end RandomWalkSearch.EndpointPolicy

namespace RandomWalkSearch.Cycle
open EndpointPolicy LazyWalk MeasureTheory
open scoped ENNReal

variable {k : ℕ} [NeZero (N k)]

theorem sparsePolicy_checks_le [NeZero (L k)] (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    checkCost sparsePolicy (lazyTapes z w) (oracle a) ≤ L k := by
  apply collectThenCheck_checkCost_le _ _ _ _ (L k)
  · exact sparse_tests_marked hk a
  · intro v _
    exact (representatives_card_le _ v).trans_eq (ZMod.card (L k))

theorem densePolicy_checks_le (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    checkCost densePolicy (lazyTapes z w) (oracle a) ≤ k := by
  apply collectThenCheck_checkCost_le _ _ _ _ k
  · exact dense_tests_marked hk a
  · intro v _
    exact (Finset.card_le_card Finset.inter_subset_right).trans (grid_card_le k (D k))

theorem sparsePolicy_updates_le_exit [NeZero (L k)] (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    updatesENN sparsePolicy (lazyTapes z w) (oracle a) ≤ exitENN (L k) (w 0) := by
  classical
  by_cases he : ∃ n, (L k : ℤ) ≤ |integerWalk (w 0) n|
  · rw [exitENN_at_first (w 0) (first_exit_boundary he)
      (fun j hj => lt_of_not_ge (Nat.find_min he hj))]
    exact (updatesENN_le_nat ..).mpr
      (sparsePolicy_costs_at_exit hk z w a (Nat.find he) (first_exit_boundary he)).2.1
  · rw [exitENN_of_no_exit (L k) (w 0) he]
    exact le_top

theorem densePolicy_updates_le_exit (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    updatesENN densePolicy (lazyTapes z w) (oracle a) ≤ exitENN (N k) (w 0) := by
  classical
  by_cases he : ∃ n, (N k : ℤ) ≤ |integerWalk (w 0) n|
  · rw [exitENN_at_first (w 0) (first_exit_boundary he)
      (fun j hj => lt_of_not_ge (Nat.find_min he hj))]
    exact (updatesENN_le_nat ..).mpr
      (densePolicy_costs_at_exit hk z w a (Nat.find he) (first_exit_boundary he)).2.1
  · rw [exitENN_of_no_exit (N k) (w 0) he]
    exact le_top

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Consecutive sparse endpoint: one setup, certain success, at most `L` checks,
and at most `2L²` expected genuine updates, on every translate. -/
theorem sparse_endpoint [NeZero (L k)] (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hlaw : IID μ (fun ω => w ω 0)) (a : Vertex k) :
    (∀ ω, Consecutive oracle 1 sparsePolicy (lazyTapes (z ω) (w ω))) ∧
    (∀ ω, checkCost sparsePolicy (lazyTapes (z ω) (w ω)) (oracle a) ≤ L k) ∧
    (∫⁻ ω, successScore sparsePolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) = 1 ∧
    (∫⁻ ω, updatesENN sparsePolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) ≤
      ENNReal.ofReal (2 * (L k : ℝ) ^ 2) := by
  refine ⟨fun ω => sparsePolicy_consecutive _, fun ω => sparsePolicy_checks_le hk _ _ a, ?_, ?_⟩
  · have hs := (ae_exit_finite μ (fun ω => w ω 0) hlaw (L k)).mono (fun ω hω => by
      obtain ⟨t, ht⟩ := hω
      exact (sparsePolicy_costs_at_exit hk (z ω) (w ω) a t ht).1)
    calc
      _ = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hs.mono (fun ω hω => by
        simp [successScore, hω]))
      _ = 1 := by simp
  · exact (lintegral_mono (fun ω => sparsePolicy_updates_le_exit hk (z ω) (w ω) a)).trans_eq
      (lintegral_exitENN μ (fun ω => w ω 0) hlaw (L k))

/-- Consecutive dense endpoint: one setup, certain success, at most `k` checks,
and at most `2N²` expected genuine updates, on every translate. -/
theorem dense_endpoint (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hlaw : IID μ (fun ω => w ω 0)) (a : Vertex k) :
    (∀ ω, Consecutive oracle 1 densePolicy (lazyTapes (z ω) (w ω))) ∧
    (∀ ω, checkCost densePolicy (lazyTapes (z ω) (w ω)) (oracle a) ≤ k) ∧
    (∫⁻ ω, successScore densePolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) = 1 ∧
    (∫⁻ ω, updatesENN densePolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) ≤
      ENNReal.ofReal (2 * (N k : ℝ) ^ 2) := by
  refine ⟨fun ω => densePolicy_consecutive _, fun ω => densePolicy_checks_le hk _ _ a, ?_, ?_⟩
  · have hs := (ae_exit_finite μ (fun ω => w ω 0) hlaw (N k)).mono (fun ω hω => by
      obtain ⟨t, ht⟩ := hω
      exact (densePolicy_costs_at_exit hk (z ω) (w ω) a t ht).1)
    calc
      _ = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hs.mono (fun ω hω => by
        simp [successScore, hω]))
      _ = 1 := by simp
  · exact (lintegral_mono (fun ω => densePolicy_updates_le_exit hk (z ω) (w ω) a)).trans_eq
      (lintegral_exitENN μ (fun ω => w ω 0) hlaw (N k))

end RandomWalkSearch.Cycle
