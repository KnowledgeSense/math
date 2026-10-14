import MeanMaximumForests.PeakAnalysis.BinomialMixtureGradient
import MeanMaximumForests.PeakAnalysis.MixtureVariance
import MeanMaximumForests.PeakAnalysis.AvailabilityTailBounds
import MeanMaximumForests.PeakAnalysis.ForestBipartition

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

/-- Uniform local mass and adjacent-difference estimates for the genuine cardinality law of every finite forest. -/
theorem forest_integer_mass_bounds : ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∃ N₀ : ℕ,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
    N₀ ≤ Fintype.card V → ∀ (z : ℝ) (hz : (1 / 4 : ℝ) ≤ z), z ≤ 1 →
    ∀ k : ℤ, (hardCoreLaw G (fun _ => z) (fun _ => by linarith)).expectation
      (fun I => (I.card : ℝ)) = (k : ℝ) →
      c ≤ Real.sqrt (Fintype.card V : ℝ) * hardCoreIntegerMass G z (by linarith) k ∧
      (Fintype.card V : ℝ) * |hardCoreIntegerMass G z (by linarith) (k + 1) -
        hardCoreIntegerMass G z (by linarith) k| ≤ D := by
  obtain ⟨A, hA, hconc⟩ := forest_conditional_means_concentration
  let c := Real.exp (-(120 * (32 * A) * (32 * A + 1))) / 24
  let D := 1024 * (6 * (Real.exp 720) ^ 2) + 1024 / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge ((1280 * (32 * A + 1)) ^ 2)
  refine ⟨c, D, hc, hD, max N₁ (1024 * 28802), ?_⟩
  intro V _ _ G hG hN z hz hz1 k hk
  have hz0 : 0 < z := by linarith
  have hnlarge : 1024 * 28802 ≤ Fintype.card V := (le_max_right _ _).trans hN
  have hn0 : 0 < Fintype.card V := by omega
  have hn2048 : 2048 ≤ Fintype.card V := by omega
  have hs0 : 0 ≤ Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (Fintype.card V : ℝ)) ^ 2 = Fintype.card V := Real.sq_sqrt (Nat.cast_nonneg _)
  have hscale : 1280 * (32 * A + 1) ≤ Real.sqrt (Fintype.card V : ℝ) := by
    have hN₁' : (N₁ : ℝ) ≤ Fintype.card V := by exact_mod_cast ((le_max_left _ _).trans hN)
    have ht0 : 0 ≤ 1280 * (32 * A + 1) := by linarith
    nlinarith only [hN₁, hN₁', hs2, hs0, ht0]
  obtain ⟨L, R, hL, hR, hd, hcover, hcount⟩ := forest_good_bipartition G hG
  let w := bipartiteMixLaw G L R hL hR hd hcover z hz0
  let M := fun r : {r : Finset V // r ⊆ R} => (availableIn G L r.val).card
  let a := fun r : {r : Finset V // r ⊆ R} => r.val.card
  have ht := availability_small_probability G L R hL hR hd hcover z hz hz1 hcount
  have htail : w.eventMass (fun r => (M r : ℝ) ≤ (Fintype.card V : ℝ) / 1024) ≤ 1 / 4 :=
    ht.trans (availability_exponential_le_quarter _ hn2048)
  have hscaledtail : (Fintype.card V : ℝ) *
      w.eventMass (fun r => (M r : ℝ) ≤ (Fintype.card V : ℝ) / 1024) ≤ 1024 / Real.log 2 :=
    (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)).trans (availability_exponential_scaled _)
  have hcentr := hconc G hG L R hL hR hd hcover z hz0 hz1 hn0
  rw [hk] at hcentr
  have hcent : (1 / 2 : ℝ) ≤ w.eventMass
      (fun r => |(a r : ℝ) + (M r : ℝ) * z / (1 + z) - (k : ℝ)| ≤
        A * Real.sqrt (Fintype.card V : ℝ)) := hcentr
  have hlow := binomial_mixture_central_lower w M a (Fintype.card V) k z A
    (Real.sqrt (Fintype.card V : ℝ)) hz hz1 hA hscale hs2 (fun r => card_le_univ _) htail hcent
  have hgrad := binomial_mixture_gradient w M a (Fintype.card V) k z (1024 / Real.log 2)
    hz hz1 hnlarge hscaledtail
  have hm (j : ℤ) : hardCoreIntegerMass G z hz0 j =
      w.expectation (fun r => binomialIntegerMass (M r) z (j - a r)) :=
    bipartite_mass_mixture G L R hL hR hd hcover z hz0 j
  rw [← hm k] at hlow
  rw [← hm (k + 1), ← hm k] at hgrad
  constructor
  · dsimp [c]
    linarith only [hlow]
  · exact hgrad

end MeanMaximumForests.PeakAnalysis
