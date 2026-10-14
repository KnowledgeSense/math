import RandomWalkSearch.RestorationCoverage

/-! The actual one-setup restoration endpoints, including their expected costs. -/
noncomputable section
namespace RandomWalkSearch.Cycle
open EndpointPolicy LazyWalk MeasureTheory
open scoped ENNReal

variable {k : ℕ} [NeZero (N k)]

theorem sparseRestorationPolicy_checks_le [NeZero (L k)] (hk : 0 < k) (hN : 2 < N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    checkCost sparseRestorationPolicy (lazyTapes z w) (oracle a) ≤ L k := by
  apply restorationCollect_checks_le hN _ _ _ _ _ (L k)
  · exact sparse_tests_marked hk a
  · intro v _
    exact (representatives_card_le _ v).trans_eq (ZMod.card (L k))

theorem denseRestorationPolicy_checks_le (hk : 0 < k) (hN : 2 < N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    checkCost denseRestorationPolicy (lazyTapes z w) (oracle a) ≤ k := by
  apply restorationCollect_checks_le hN _ _ _ _ _ k
  · exact dense_tests_marked hk a
  · intro v _
    exact (Finset.card_le_card Finset.inter_subset_right).trans (grid_card_le k (D k))

theorem sparseRestorationPolicy_updates_le_right [NeZero (L k)] (hk : 0 < k) (hN : 2 < N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    updatesENN sparseRestorationPolicy (lazyTapes z w) (oracle a) ≤ rightENN (L k - 1) (w 0) := by
  classical
  by_cases he : ∃ n, L k - 1 ≤ rightCountStream (w 0) n
  · rw [rightENN_at_first (w 0) he]
    exact (updatesENN_le_nat ..).mpr
      (sparseRestorationPolicy_at_count hk hN z w a (Nat.find he) (Nat.find_spec he)).2.1
  · rw [rightENN_of_no_finish (L k - 1) (w 0) he]
    exact le_top

theorem denseRestorationPolicy_updates_le_right (hk : 0 < k) (hN : 2 < N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) :
    updatesENN denseRestorationPolicy (lazyTapes z w) (oracle a) ≤ rightENN (N k - 1) (w 0) := by
  classical
  by_cases he : ∃ n, N k - 1 ≤ rightCountStream (w 0) n
  · rw [rightENN_at_first (w 0) he]
    exact (updatesENN_le_nat ..).mpr
      (denseRestorationPolicy_at_count hk hN z w a (Nat.find he) (Nat.find_spec he)).2.1
  · rw [rightENN_of_no_finish (N k - 1) (w 0) he]
    exact le_top

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Restoration sparse endpoint: one setup, certain success, at most `L` checks,
and at most `4(L−1)` expected updates, on every translate. -/
theorem sparse_restoration_endpoint [NeZero (L k)] (hk : 0 < k) (hN : 2 < N k)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hlaw : IID μ (fun ω => w ω 0)) (a : Vertex k) :
    (∀ ω, Restoration oracle 1 sparseRestorationPolicy (lazyTapes (z ω) (w ω))) ∧
    (∀ ω, checkCost sparseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ≤ L k) ∧
    (∫⁻ ω, successScore sparseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) = 1 ∧
    (∫⁻ ω, updatesENN sparseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) ≤
      ENNReal.ofReal (4 * ((L k - 1 : ℕ) : ℝ)) := by
  refine ⟨fun ω => sparseRestorationPolicy_restoration _,
    fun ω => sparseRestorationPolicy_checks_le hk hN _ _ a, ?_, ?_⟩
  · have hs := (ae_right_finite μ (fun ω => w ω 0) hlaw (L k - 1)).mono (fun ω hω => by
      obtain ⟨t, ht⟩ := hω
      exact (sparseRestorationPolicy_at_count hk hN (z ω) (w ω) a t ht).1)
    calc
      _ = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hs.mono (fun ω hω => by
        simp [successScore, hω]))
      _ = 1 := by simp
  · exact (lintegral_mono (fun ω => sparseRestorationPolicy_updates_le_right hk hN (z ω) (w ω) a)).trans_eq
      (lintegral_rightENN μ (fun ω => w ω 0) hlaw (L k - 1))

/-- Restoration dense endpoint: one setup, certain success, at most `k` checks,
and at most `4(N−1)` expected updates, on every translate. -/
theorem dense_restoration_endpoint (hk : 0 < k) (hN : 2 < N k)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hlaw : IID μ (fun ω => w ω 0)) (a : Vertex k) :
    (∀ ω, Restoration oracle 1 denseRestorationPolicy (lazyTapes (z ω) (w ω))) ∧
    (∀ ω, checkCost denseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ≤ k) ∧
    (∫⁻ ω, successScore denseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) = 1 ∧
    (∫⁻ ω, updatesENN denseRestorationPolicy (lazyTapes (z ω) (w ω)) (oracle a) ∂μ) ≤
      ENNReal.ofReal (4 * ((N k - 1 : ℕ) : ℝ)) := by
  refine ⟨fun ω => denseRestorationPolicy_restoration _,
    fun ω => denseRestorationPolicy_checks_le hk hN _ _ a, ?_, ?_⟩
  · have hs := (ae_right_finite μ (fun ω => w ω 0) hlaw (N k - 1)).mono (fun ω hω => by
      obtain ⟨t, ht⟩ := hω
      exact (denseRestorationPolicy_at_count hk hN (z ω) (w ω) a t ht).1)
    calc
      _ = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hs.mono (fun ω hω => by
        simp [successScore, hω]))
      _ = 1 := by simp
  · exact (lintegral_mono (fun ω => denseRestorationPolicy_updates_le_right hk hN (z ω) (w ω) a)).trans_eq
      (lintegral_rightENN μ (fun ω => w ω 0) hlaw (N k - 1))

end RandomWalkSearch.Cycle
