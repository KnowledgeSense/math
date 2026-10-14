import MainTheorems.Corona.Mean
import MainTheorems.Corona.TwoPeaks
import MainTheorems.Corona.Cographs

namespace ResearchMain.Corona

open Classical Filter Polynomial

variable {W : Type} [Fintype W] [DecidableEq W]

def UniversalUnimodality (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Unimodal (fun k => (independentCount (corona G H) k : ℝ))

def ConnectedUniversalUnimodality (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected →
    Unimodal (fun k => (independentCount (corona G H) k : ℝ))

theorem independencePolynomial_mass_ge_one (H : SimpleGraph W) :
    1 ≤ mass (independencePolynomial H) := by
  rw [mass, independencePolynomial_eval_one]
  have hn := Finset.card_pos.mpr ⟨∅, independentSets_empty_mem H⟩
  exact_mod_cast (show 1 ≤ (independentSets H).card by omega)

theorem mean_one_iff_cliqueMinusEdge (H : SimpleGraph W) :
    mean (independencePolynomial H) = 1 ↔ CliqueMinusEdge H := by
  have hmass : mass (independencePolynomial H) ≠ 0 := by
    have := independencePolynomial_mass_ge_one H
    linarith
  simp only [mean, firstMoment, eulerDerivative, eval_mul, eval_X, mul_one]
  rw [div_eq_iff hmass, one_mul]
  exact independencePolynomial_mean_one_iff H

theorem nonexceptional_eventually_not_unimodal (H : SimpleGraph W) (hH : ¬CliqueMinusEdge H) :
    ∀ᶠ m : ℕ in atTop,
      ¬Unimodal (fun k => (independentCount
        (corona (baseGraph (balanceIndex (mass (independencePolynomial H)) m) m) H) k : ℝ)) := by
  have hmean : mean (independencePolynomial H) ≠ 1 :=
    fun h => hH ((mean_one_iff_cliqueMinusEdge H).mp h)
  have ht := twoPeak_eventually_not_unimodal (independencePolynomial_nonnegative H)
    (independencePolynomial_mass_ge_one H) hmean
  filter_upwards [ht] with m hm
  simpa only [← independencePolynomial_corona_baseGraph, independencePolynomial_coeff] using hm

theorem nonexceptional_arbitrarily_large (H : SimpleGraph W) (hH : ¬CliqueMinusEdge H) (N : ℕ) :
    ∃ a m : ℕ, N ≤ a + 2 * m ∧ (baseGraph a m).Connected ∧ P4Free (baseGraph a m) ∧
      ¬Unimodal (fun k => (independentCount (corona (baseGraph a m) H) k : ℝ)) := by
  have ht := nonexceptional_eventually_not_unimodal H hH
  obtain ⟨m, hm, hm1, hmN⟩ := (ht.and ((eventually_ge_atTop (1 : ℕ)).and
    (eventually_ge_atTop N))).exists
  let a := balanceIndex (mass (independencePolynomial H)) m
  have hq : 0 < mass (independencePolynomial H) := by
    have := independencePolynomial_mass_ge_one H
    linarith
  have ha : 1 ≤ a := hm1.trans (balanceIndex_order hq hm1).1
  exact ⟨a, m, by omega, baseGraph_connected ha hm1, baseGraph_P4Free a m, hm⟩

theorem connected_universal_unimodality_classification (H : SimpleGraph W) :
    ConnectedUniversalUnimodality H ↔ CliqueMinusEdge H := by
  constructor
  · intro h
    by_contra hH
    obtain ⟨a, m, _, hconnected, _, hbad⟩ := nonexceptional_arbitrarily_large H hH 0
    exact hbad (h _ (baseGraph a m) hconnected)
  · intro hH V _ _ G _
    exact ⟨Fintype.card V, corona_unimodal_cliqueMinusEdge G H hH⟩

theorem universal_unimodality_classification (H : SimpleGraph W) :
    UniversalUnimodality H ↔ CliqueMinusEdge H := by
  constructor
  · intro h
    apply (connected_universal_unimodality_classification H).mp
    exact fun V _ _ G _ => h V G
  · intro hH V _ _ G
    exact ⟨Fintype.card V, corona_unimodal_cliqueMinusEdge G H hH⟩

end ResearchMain.Corona
