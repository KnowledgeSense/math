import MeanMaximumForests.GlobalModeLocalization
import MeanMaximumForests.HubApproximation
import MeanMaximumForests.GraphPeaks
import MeanMaximumForests.TreeInfimum

namespace MeanMaximumForests
open Filter
open scoped Topology

/-- The upper half of the original weak-peak limit theorem holds for all sufficiently
large orders. A global mode is used only to supply one eligible weak local peak. -/
theorem treePeakMinimum_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, treePeakMinimum n < beta + ε := by
  obtain ⟨r, hr, hnear⟩ := exists_lt_of_csInf_lt treeRatios_nonempty
    (show sInf treeRatios < beta + ε / 2 by change beta < _; linarith)
  obtain ⟨V, i, G, hG, rfl⟩ := hr
  let := i
  let := hG.connected.nonempty
  have ht := eventually_exists_tree_ratio_lt G hG.isAcyclic (beta + ε / 2) hnear
  obtain ⟨N, hN⟩ := forest_global_modes_uniform_ratio.{0} (ε / 2) (by positivity)
  filter_upwards [ht, eventually_ge_atTop N] with n hn hnN
  obtain ⟨H, hH, hratio⟩ := hn
  obtain ⟨k, hk, hmax⟩ := exists_maximum_coefficient H
  have hclose := hN H hH.isAcyclic (by simpa using hnN) k hmax
  have hpeak : WeakLocalPeak H k := ⟨hk, Or.inr (hmax (k - 1)), hmax (k + 1)⟩
  have hmem : (k : ℝ) / H.indepNum ∈ treePeakRatios n := ⟨H, k, hH, hpeak, rfl⟩
  have hmin : treePeakMinimum n ≤ (k : ℝ) / H.indepNum :=
    csInf_le ((forestPeakRatios_bddBelow n).mono (treePeakRatios_subset n)) hmem
  have hh := (abs_lt.mp hclose).2
  linarith

/-- The forest minimum is no larger than the tree minimum at every positive order. -/
theorem forestPeakMinimum_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, forestPeakMinimum n < beta + ε := by
  filter_upwards [treePeakMinimum_eventually_lt ε hε, eventually_gt_atTop 0] with n hn hn0
  exact (forestPeakMinimum_le_treePeakMinimum hn0).trans_lt hn

end MeanMaximumForests
