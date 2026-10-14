import RandomWalkSearch.ConsecutiveEndpoints
import RandomWalkSearch.RestorationEndpoints
import RandomWalkSearch.CanonicalRandomness

/-! # Four actual endpoint algorithms on a concrete probability space

The canonical space consists of an independent uniform setup and an infinite iid
uniform four-symbol update tape. Each witness is an actual history policy;
its costs are the suprema of the shared execution's charged operation counts.
-/

noncomputable section
namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal

variable {k : ℕ} [NeZero (N k)]

/-- Per-translate, actual endpoint performance under the concrete independent law. -/
structure EndpointCosts (p : Policy (Vertex k)) (U : ℝ) (Q : ℕ) : Prop where
  success : ∀ a, (Canonical.algorithm k p).success (Canonical.measure k) a = 1
  updates : ∀ a, (∫⁻ ω, updatesENN p
    (lazyTapes (Canonical.setups k ω) (Canonical.increments k ω)) (oracle a)
      ∂Canonical.measure k) ≤ ENNReal.ofReal U
  checks : ∀ a ω, checkCost p
    (lazyTapes (Canonical.setups k ω) (Canonical.increments k ω)) (oracle a) ≤ Q

def IsRestorationEndpoint (p : Policy (Vertex k)) (U : ℝ) (Q : ℕ) : Prop :=
  (∀ ω : Canonical.Outcome k,
    Restoration oracle 1 p (lazyTapes (Canonical.setups k ω) (Canonical.increments k ω))) ∧
      EndpointCosts p U Q

def IsConsecutiveEndpoint (p : Policy (Vertex k)) (U : ℝ) (Q : ℕ) : Prop :=
  (∀ ω : Canonical.Outcome k,
    Consecutive oracle 1 p (lazyTapes (Canonical.setups k ω) (Canonical.increments k ω))) ∧
      EndpointCosts p U Q

omit [NeZero (N k)] in
theorem N_gt_two (hk : 2 ≤ k) : 2 < N k := by
  have h := Nat.pow_le_pow_left hk 8
  norm_num at h
  dsimp [N]
  omega

theorem canonical_sparse_restoration [NeZero (L k)] (hk : 2 ≤ k) :
    IsRestorationEndpoint (k := k) sparseRestorationPolicy (4 * ((L k - 1 : ℕ) : ℝ)) (L k) := by
  have h (a : Vertex k) := sparse_restoration_endpoint (by omega : 0 < k) (N_gt_two hk)
    (Canonical.measure k) (Canonical.setups k) (Canonical.increments k) (Canonical.increments_iid k) a
  refine ⟨(h 0).1, ⟨?_, ?_, ?_⟩⟩
  · intro a
    exact (h a).2.2.1
  · intro a
    exact (h a).2.2.2
  · intro a
    exact (h a).2.1

theorem canonical_dense_restoration (hk : 2 ≤ k) :
    IsRestorationEndpoint (k := k) denseRestorationPolicy (4 * ((N k - 1 : ℕ) : ℝ)) k := by
  have h (a : Vertex k) := dense_restoration_endpoint (by omega : 0 < k) (N_gt_two hk)
    (Canonical.measure k) (Canonical.setups k) (Canonical.increments k) (Canonical.increments_iid k) a
  refine ⟨(h 0).1, ⟨?_, ?_, ?_⟩⟩
  · intro a
    exact (h a).2.2.1
  · intro a
    exact (h a).2.2.2
  · intro a
    exact (h a).2.1

theorem canonical_sparse_consecutive [NeZero (L k)] (hk : 2 ≤ k) :
    IsConsecutiveEndpoint (k := k) sparsePolicy (2 * (L k : ℝ) ^ 2) (L k) := by
  have h (a : Vertex k) := sparse_endpoint (by omega : 0 < k)
    (Canonical.measure k) (Canonical.setups k) (Canonical.increments k) (Canonical.increments_iid k) a
  refine ⟨(h 0).1, ⟨?_, ?_, ?_⟩⟩
  · intro a
    exact (h a).2.2.1
  · intro a
    exact (h a).2.2.2
  · intro a
    exact (h a).2.1

theorem canonical_dense_consecutive (hk : 2 ≤ k) :
    IsConsecutiveEndpoint (k := k) densePolicy (2 * (N k : ℝ) ^ 2) k := by
  have h (a : Vertex k) := dense_endpoint (by omega : 0 < k)
    (Canonical.measure k) (Canonical.setups k) (Canonical.increments k) (Canonical.increments_iid k) a
  refine ⟨(h 0).1, ⟨?_, ?_, ?_⟩⟩
  · intro a
    exact (h a).2.2.1
  · intro a
    exact (h a).2.2.2
  · intro a
    exact (h a).2.1

/-- The paper's four endpoint orders, witnessed by genuine algorithms with one
uniform setup and actual iid lazy updates. No supplied success/cost inequalities
occur in the hypotheses. -/
theorem four_endpoints [NeZero (L k)] (hk : 2 ≤ k) :
    ∃ pRS pRD pCS pCD : Policy (Vertex k),
      IsRestorationEndpoint pRS (4 * ((L k - 1 : ℕ) : ℝ)) (L k) ∧
      IsRestorationEndpoint pRD (4 * ((N k - 1 : ℕ) : ℝ)) k ∧
      IsConsecutiveEndpoint pCS (2 * (L k : ℝ) ^ 2) (L k) ∧
      IsConsecutiveEndpoint pCD (2 * (N k : ℝ) ^ 2) k :=
  ⟨sparseRestorationPolicy, denseRestorationPolicy, sparsePolicy, densePolicy,
    canonical_sparse_restoration hk, canonical_dense_restoration hk,
    canonical_sparse_consecutive hk, canonical_dense_consecutive hk⟩

end RandomWalkSearch.Cycle
