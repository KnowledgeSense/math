import MeanMaximumForests.ForestVariance
import MeanMaximumForests.SizeDistribution
import MeanMaximumForests.FiniteModeBounds
import MeanMaximumForests.ForestOrderBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Localization of actual global coefficient maxima. The separate assertion
that every weak local peak is such a maximum is not presupposed here. -/
namespace MeanMaximumForests
open Finset HardCoreActivityThreshold
universe u

/-- A global maximum of the actual independence coefficients. -/
def GlobalCoefficientMode {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ j, independentSetCoefficient G univ j ≤ independentSetCoefficient G univ k

theorem globalCoefficientMode_le_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : GlobalCoefficientMode G k) : k ≤ Fintype.card V := by
  classical
  have hp : 0 < independentSetCoefficient G univ k := by
    have h := hk 0
    rw [coefficient_zero] at h
    omega
  obtain ⟨s, _, _, hs⟩ := (coefficient_pos_iff G univ k).mp hp
  exact hs ▸ card_le_univ s

theorem graph_global_mode_squared_distance {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : GlobalCoefficientMode G k)
    (r : ℝ) (hr : 0 < r) (hv : 2 * graphVariance G ≤ r ^ 2) :
    ((k : ℝ) - graphMean G) ^ 2 ≤ 2 * (2 * r + 1) * graphVariance G := by
  let j : Fin (Fintype.card V + 1) := ⟨k, Nat.lt_succ_of_le (globalCoefficientMode_le_card G k hk)⟩
  have hm := independentSizeLaw_mode G j hk
  have hb := global_mode_squared_distance (independentSizeLaw G) j hm r hr
    (by rwa [independentSizeLaw_variance])
  simpa only [independentSizeLaw_mean, independentSizeLaw_variance, j] using hb

/-- A single threshold works for every forest, regardless of its shape or maximum degree. -/
theorem forest_global_modes_uniform_localization (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsAcyclic → N ≤ Fintype.card V → ∀ k, GlobalCoefficientMode G k →
        |(k : ℝ) - graphMean G| < ε * Fintype.card V := by
  obtain ⟨C, hC, hvar⟩ := forest_variance_linear.{u}
  let δ : ℝ := ε ^ 2 / (8 * C)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have heq : 8 * C * δ = ε ^ 2 := by dsimp [δ]; field_simp
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / δ ^ 2 + 4 * C / ε ^ 2 + 1)
  refine ⟨N, ?_⟩
  intro V _ _ G hG hn k hk
  let n : ℝ := Fintype.card V
  have hn' : 2 * C / δ ^ 2 + 4 * C / ε ^ 2 + 1 < n :=
    hN.trans_le (Nat.cast_le.mpr hn)
  have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hd
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hn0 : 0 < n := by
    have ha : 0 ≤ 2 * C / δ ^ 2 := by positivity
    have hb : 0 ≤ 4 * C / ε ^ 2 := by positivity
    linarith
  have hn1 : 2 * C / δ ^ 2 < n := by
    have : 0 ≤ 4 * C / ε ^ 2 := by positivity
    linarith
  have hn2 : 4 * C / ε ^ 2 < n := by
    have : 0 ≤ 2 * C / δ ^ 2 := by positivity
    linarith
  have hdn : 2 * C < n * δ ^ 2 := (div_lt_iff₀ hd2).mp hn1
  have hen : 4 * C < n * ε ^ 2 := (div_lt_iff₀ he2).mp hn2
  have hv := hvar G hG
  change graphVariance G ≤ C * n at hv
  have hrv : 2 * graphVariance G ≤ (δ * n) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdn.le hn0.le
    nlinarith
  have hb := graph_global_mode_squared_distance G k hk (δ * n) (mul_pos hd hn0) hrv
  have hmul := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * (2 * (δ * n) + 1))
  have heq' := congrArg (fun x : ℝ => x * n ^ 2) heq
  have hen' := mul_lt_mul_of_pos_right hen hn0
  have hsq : ((k : ℝ) - graphMean G) ^ 2 < (ε * n) ^ 2 := by nlinarith
  change |(k : ℝ) - graphMean G| < ε * n
  nlinarith [sq_abs ((k : ℝ) - graphMean G), abs_nonneg ((k : ℝ) - graphMean G),
    mul_pos hε hn0]

/-- Uniform localization after normalization by the independence number. -/
theorem forest_global_modes_uniform_ratio (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsAcyclic → N ≤ Fintype.card V → ∀ k, GlobalCoefficientMode G k →
        |(k : ℝ) / G.indepNum - graphMean G / G.indepNum| < ε := by
  obtain ⟨N, hN⟩ := forest_global_modes_uniform_localization.{u} (ε / 2) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro V _ _ G hG hn k hk
  have hn0 : 0 < Fintype.card V := by omega
  have hcard := forest_card_le_twice_indepNum G hG
  have hα : (0 : ℝ) < G.indepNum := Nat.cast_pos.mpr (by omega)
  have hd := hN G hG (by omega) k hk
  rw [← sub_div, abs_div, abs_of_pos hα]
  apply (div_lt_iff₀ hα).mpr
  apply hd.trans_le
  have hc : (Fintype.card V : ℝ) ≤ 2 * G.indepNum := by exact_mod_cast hcard
  nlinarith

end MeanMaximumForests
