import TerminalLogConcavity.ReleaseCounts
import TerminalLogConcavity.LogarithmicParameter

namespace TerminalLogConcavity
set_option backward.isDefEq.respectTransparency false

theorem releaseTree_order {r H : ℕ} (hr : 1 ≤ r) (hH : 1 ≤ H) :
    Fintype.card (releaseTree r H).Vertex ≤
      1200 * (r + 1) ^ 4 * (r + 1 + logarithmicParameter H) := by
  apply exact_release_order_bound (by omega : 2 ≤ r + 1) hH
  exact releaseForest_count_identity (by omega) _

theorem releaseTree_geometry {r H : ℕ} (hr : 1 ≤ r) (hH : 1 ≤ H) :
    (releaseTree r H).graph.IsTree ∧
      (∀ v, ((releaseTree r H).graph.neighborSet v).ncard ≤ 3) ∧
      Fintype.card (releaseTree r H).Vertex ≤
        1200 * (r + 1) ^ 4 * (r + 1 + logarithmicParameter H) :=
  ⟨releaseTree_isTree r H, releaseTree_subcubic r H, releaseTree_order hr hH⟩

end TerminalLogConcavity
