import MeanMaximumForests.PeakAnalysis.BipartiteMixture
import MeanMaximumForests.PeakAnalysis.TiltVariance
import MeanMaximumForests.PeakAnalysis.FiniteConcentration
import HardCoreActivityThreshold.FiniteVariance

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bipartiteConditionalMean (G : SimpleGraph V) (L : Finset V) (z : ℝ)
    (r : Finset V) : ℝ := r.card + (availableIn G L r).card * z / (1 + z)

theorem binomial_shifted_mean (n a : ℕ) (z : ℝ) (hz : 0 < z) :
    (binomialSizeLaw n z hz).expectation (fun k => ((a + k.val : ℕ) : ℝ)) =
      (a : ℝ) + n * z / (1 + z) := by
  simp only [Nat.cast_add, FiniteLaw.expectation_add, FiniteLaw.expectation_const, binomialSizeLaw_mean]

theorem bipartite_conditional_mean (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) :
    (bipartiteMixLaw G L R hL hR hd hc z hz).expectation
      (fun r => bipartiteConditionalMean G L z r.val) =
      (hardCoreLaw G (fun _ => z) (fun _ => hz)).expectation (fun I => (I.card : ℝ)) := by
  rw [bipartite_cardinality_mixture G L R hL hR hd hc z hz (fun k => (k : ℝ))]
  simp only [binomial_shifted_mean, bipartiteConditionalMean]

/-- The variance of the conditional means is bounded by the actual cardinality variance. -/
theorem bipartite_conditional_variance (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) :
    (bipartiteMixLaw G L R hL hR hd hc z hz).variance
      (fun r => bipartiteConditionalMean G L z r.val) ≤
      (hardCoreLaw G (fun _ => z) (fun _ => hz)).variance (fun I => (I.card : ℝ)) := by
  let μ := hardCoreLaw G (fun _ => z) (fun _ => hz)
  let w := bipartiteMixLaw G L R hL hR hd hc z hz
  let c := μ.expectation (fun I => (I.card : ℝ))
  have hm : w.expectation (fun r => bipartiteConditionalMean G L z r.val) = c :=
    bipartite_conditional_mean G L R hL hR hd hc z hz
  have hp (r : {r : Finset V // r ⊆ R}) :
      (bipartiteConditionalMean G L z r.val - c) ^ 2 ≤
      (binomialSizeLaw (availableIn G L r.val).card z hz).expectation
        (fun k => (((r.val.card + k.val : ℕ) : ℝ) - c) ^ 2) := by
    rw [FiniteLaw.variance_eq_centered, binomial_shifted_mean]
    exact le_add_of_nonneg_left (FiniteLaw.variance_nonneg _ _)
  have he := w.expectation_mono hp
  have hmix := bipartite_cardinality_mixture G L R hL hR hd hc z hz
    (fun k => ((k : ℝ) - c) ^ 2)
  change μ.expectation (fun I => ((I.card : ℝ) - c) ^ 2) = _ at hmix
  rw [← hmix] at he
  change w.variance (fun r => bipartiteConditionalMean G L z r.val) ≤ μ.variance (fun I => (I.card : ℝ))
  unfold FiniteLaw.variance
  rw [hm]
  exact he

/-- A uniform square-root window captures at least half of the mixture's conditional means. -/
theorem forest_conditional_means_concentration : ∃ A : ℝ, 1 ≤ A ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
    ∀ (L R : Finset V) (hL : Independent G L) (hR : Independent G R)
      (hd : Disjoint L R) (hc : L ∪ R = univ) (z : ℝ) (hz : 0 < z), z ≤ 1 →
      0 < Fintype.card V →
      (1 / 2 : ℝ) ≤ (bipartiteMixLaw G L R hL hR hd hc z hz).eventMass
        (fun r => |bipartiteConditionalMean G L z r.val -
          (hardCoreLaw G (fun _ => z) (fun _ => hz)).expectation (fun I => (I.card : ℝ))| ≤
            A * Real.sqrt (Fintype.card V)) := by
  obtain ⟨C, hC, hvar⟩ := forest_small_activity_variance
  refine ⟨C + 1, by linarith, ?_⟩
  intro V _ _ G hG L R hL hR hd hc z hz hz1 hn
  have hv := (bipartite_conditional_variance G L R hL hR hd hc z hz).trans
    (hvar G hG (fun _ => z) (fun _ => hz) (fun _ => hz1))
  have hs : 0 < Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs2 : (Real.sqrt (Fintype.card V : ℝ)) ^ 2 = Fintype.card V :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hbound : 2 * (bipartiteMixLaw G L R hL hR hd hc z hz).variance
      (fun r => bipartiteConditionalMean G L z r.val) ≤
      ((C + 1) * Real.sqrt (Fintype.card V : ℝ)) ^ 2 := by
    rw [mul_pow, hs2]
    have h := mul_nonneg (sq_nonneg C) (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
    nlinarith only [hv, h, Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  have h := finiteLaw_central_mass_half (bipartiteMixLaw G L R hL hR hd hc z hz)
    (fun r => bipartiteConditionalMean G L z r.val)
    ((C + 1) * Real.sqrt (Fintype.card V : ℝ)) (by positivity) hbound
  simpa only [bipartite_conditional_mean] using h

end MeanMaximumForests.PeakAnalysis
