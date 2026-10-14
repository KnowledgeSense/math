import MainTheorems.Corona.UnimodalityClassification
import MainTheorems.Corona.CoefficientIntervals
import MainTheorems.Corona.Homogeneity

namespace ResearchMain.Corona

open Classical Filter Polynomial

variable {W : Type} [Fintype W] [DecidableEq W]

def UniversalLogConcavity (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    LogConcave (fun k => (independentCount (corona G H) k : ℝ))

def ConnectedUniversalLogConcavity (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected →
    LogConcave (fun k => (independentCount (corona G H) k : ℝ))

noncomputable def attachmentScale (_H : SimpleGraph W) : ℝ := 1 / ((Fintype.card W : ℝ) + 1)

omit [DecidableEq W] in
theorem attachmentScale_positive (H : SimpleGraph W) : 0 < attachmentScale H := by
  unfold attachmentScale
  positivity

omit [DecidableEq W] in
theorem attachmentScale_le_one (H : SimpleGraph W) : attachmentScale H ≤ 1 := by
  unfold attachmentScale
  apply (div_le_one (by positivity)).mpr
  have h : (0 : ℝ) ≤ Fintype.card W := by positivity
  linarith

noncomputable def logConcavityIndex (H : SimpleGraph W) (m : ℕ) : ℕ :=
  balanceIndex (mass (rescale (independencePolynomial H) (attachmentScale H))) m

theorem all_attachments_eventually_not_logConcave (H : SimpleGraph W) :
    ∀ᶠ m : ℕ in atTop,
      ¬LogConcave (fun k => (independentCount (corona (baseGraph (logConcavityIndex H m) m) H) k : ℝ)) := by
  have ht := attachmentScale_positive H
  have hmass := rescale_graph_mass H ht (attachmentScale_le_one H)
  have hmean : mean (rescale (independencePolynomial H) (attachmentScale H)) ≠ 1 :=
    ne_of_lt (rescale_graph_mean_lt_one H)
  have hnonneg := rescale_nonnegative (independencePolynomial_nonnegative H) ht.le
  have hbad := twoPeak_eventually_not_unimodal hnonneg hmass hmean
  filter_upwards [hbad] with m hm
  intro hLC
  have hU := independencePolynomial_scaled_unimodal
    (corona (baseGraph (logConcavityIndex H m) m) H) ht hLC
  rw [corona_baseGraph_comp H (ne_of_gt ht)] at hU
  simp only [coeff_C_mul] at hU
  exact hm ((unimodal_mul_pos_iff (pow_pos ht (logConcavityIndex H m + 2 * m))).mp hU)

theorem all_attachments_arbitrarily_large_not_logConcave (H : SimpleGraph W) (N : ℕ) :
    ∃ a m : ℕ, N ≤ a + 2 * m ∧ (baseGraph a m).Connected ∧ P4Free (baseGraph a m) ∧
      ¬LogConcave (fun k => (independentCount (corona (baseGraph a m) H) k : ℝ)) := by
  obtain ⟨m, hm, hm1, hmN⟩ := ((all_attachments_eventually_not_logConcave H).and
    ((eventually_ge_atTop (1 : ℕ)).and (eventually_ge_atTop N))).exists
  let a := logConcavityIndex H m
  have hmass : 0 < mass (rescale (independencePolynomial H) (attachmentScale H)) := by
    have := rescale_graph_mass H (attachmentScale_positive H) (attachmentScale_le_one H)
    linarith
  have ha : 1 ≤ a := hm1.trans (balanceIndex_order hmass hm1).1
  exact ⟨a, m, by omega, baseGraph_connected ha hm1, baseGraph_P4Free a m, hm⟩

theorem no_connected_universal_logConcavity (H : SimpleGraph W) :
    ¬ConnectedUniversalLogConcavity H := by
  intro h
  obtain ⟨a, m, _, hconnected, _, hbad⟩ := all_attachments_arbitrarily_large_not_logConcave H 0
  exact hbad (h _ (baseGraph a m) hconnected)

theorem no_universal_logConcavity (H : SimpleGraph W) : ¬UniversalLogConcavity H := by
  intro h
  apply no_connected_universal_logConcavity H
  exact fun V _ _ G _ => h V G

end ResearchMain.Corona
