import SphericalTreeFailures.TotalDecomposition
import SphericalTreeFailures.CensusFixedPoint

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset

noncomputable def totalSubtree (k : ℕ) (b : Bool) (ω : TotalSizeSpace k) : TotalSizeSpace k :=
  (subtreeInput b ω.1, subtreeInput b ω.2)

theorem measurable_totalSubtree (k : ℕ) (b : Bool) : Measurable (totalSubtree k b) :=
  ((measurable_subtreeInput b).comp measurable_fst).prodMk
    ((measurable_subtreeInput b).comp measurable_snd)

theorem totalSubtree_preserving (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) (b : Bool) :
    MeasurePreserving (totalSubtree k b) (totalSizeMeasure p k activity ha)
      (totalSizeMeasure p k activity ha) := by
  exact (broadcast_subtreeInput_preserving p b).prod
    (subtreeInput_measurePreserving (tailSampleMeasure k activity ha) b)

theorem sampledTotalSize_zero (k : ℕ) (i : Bool) (ω : TotalSizeSpace k) :
    sampledTotalSize k 0 i ω = boolIndicator i + selectedTailSize k i (ω.2 []) := by
  simp [sampledTotalSize, binaryLevel, broadcastState]

theorem level_occupation_subtree (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    (∑ v ∈ binaryLevel (h + 1), boolIndicator (broadcastState i ω v)) =
      (∑ v ∈ binaryLevel h, boolIndicator
        (broadcastState (broadcastState i ω [false]) (subtreeInput false ω) v)) +
      (∑ v ∈ binaryLevel h, boolIndicator
        (broadcastState (broadcastState i ω [true]) (subtreeInput true ω) v)) := by
  rw [sum_binaryLevel_append, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [broadcastState_subtree, broadcastState_subtree]

theorem sampledTotalSize_succ (k m : ℕ) (i : Bool) (ω : TotalSizeSpace k) :
    sampledTotalSize k (m + 1) i ω = boolIndicator i +
      sampledTotalSize k m (broadcastState i ω.1 [false]) (totalSubtree k false ω) +
      sampledTotalSize k m (broadcastState i ω.1 [true]) (totalSubtree k true ω) := by
  unfold sampledTotalSize
  rw [sum_range_succ']
  simp only [show binaryLevel 0 = {[]} from rfl, sum_singleton, broadcastState]
  simp_rw [level_occupation_subtree]
  rw [sum_binaryLevel_append]
  simp_rw [broadcastState_subtree]
  simp only [sum_add_distrib, totalSubtree, subtreeInput, broadcastState]
  ring

end SphericalTreeFailures
