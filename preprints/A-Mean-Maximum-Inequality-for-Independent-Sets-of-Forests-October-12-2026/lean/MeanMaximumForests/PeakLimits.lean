import MeanMaximumForests.PeakAnalysis.ForestAdjacentRatio
import MeanMaximumForests.PeakUpperLimit
import MeanMaximumForests.MainTheorem

namespace MeanMaximumForests
open PeakAnalysis
open Filter
open scoped Topology

/-- Every weak local peak of every sufficiently large forest is asymptotically at least the tree mean infimum. -/
theorem forest_weak_peaks_uniform_lower (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      N ≤ Fintype.card V → ∀ k : ℕ, WeakLocalPeak G k →
        beta - ε < (k : ℝ) / G.indepNum := by
  obtain ⟨C, hC, hgap⟩ := weakLocalPeak_gap_of_tilted_mass_bound
  let η := ε / (2 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN⟩ := forest_tilted_adjacent_ratio η hη
  refine ⟨max N 5, ?_⟩
  intro V _ _ G hG hn k hk
  have hn5 : 5 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hm := hgap G hG hn5 k hk η hη (fun t ht hmean =>
    hN G hG ((le_max_left _ _).trans hn) k t ht hmean)
  have hcard := forest_card_le_twice_indepNum G hG
  have ha : (0 : ℝ) < G.indepNum := Nat.cast_pos.mpr (by omega)
  have hcard' : (Fintype.card V : ℝ) ≤ 2 * G.indepNum := by exact_mod_cast hcard
  have he : C * (Fintype.card V : ℝ) * η = (ε / 2) * Fintype.card V := by
    dsimp [η]
    field_simp
  rw [he] at hm
  have hmean := forest_beta_bound G hG
  apply (lt_div_iff₀ ha).mpr
  have hs := mul_le_mul_of_nonneg_left hcard' (show 0 ≤ ε / 2 by positivity)
  nlinarith only [hm, hmean, hs]

 theorem forestPeakMinimum_eventually_gt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, beta - ε < forestPeakMinimum n := by
  obtain ⟨N, hN⟩ := forest_weak_peaks_uniform_lower ε hε
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hn hn0
  obtain ⟨G, k, hG, hk, he⟩ := forestPeakMinimum_mem hn0
  rw [he]
  exact hN G hG (by simpa using hn) k hk

 theorem treePeakMinimum_eventually_gt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, beta - ε < treePeakMinimum n := by
  filter_upwards [forestPeakMinimum_eventually_gt ε hε, eventually_gt_atTop 0] with n hn hn0
  exact hn.trans_le (forestPeakMinimum_le_treePeakMinimum hn0)

/-- The original normalized minimum weak-peak sequence over forests converges to beta. -/
theorem forestPeakMinimum_tendsto : Tendsto forestPeakMinimum atTop (𝓝 beta) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [forestPeakMinimum_eventually_gt ε hε, forestPeakMinimum_eventually_lt ε hε] with n hlo hhi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The original normalized minimum weak-peak sequence over trees has the same limit. -/
theorem treePeakMinimum_tendsto : Tendsto treePeakMinimum atTop (𝓝 beta) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [treePeakMinimum_eventually_gt ε hε, treePeakMinimum_eventually_lt ε hε] with n hlo hhi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Both genuine weak-local-peak limits, with the paper's numerical interval. -/
theorem weak_peak_limits :
    Tendsto forestPeakMinimum atTop (𝓝 beta) ∧
    Tendsto treePeakMinimum atTop (𝓝 beta) ∧
    (47 / 100 : ℝ) ≤ beta ∧ beta < (473403 / 1000000 : ℝ) :=
  ⟨forestPeakMinimum_tendsto, treePeakMinimum_tendsto,
    beta_lower_bound Release.release_invariant, beta_lt⟩

end MeanMaximumForests
