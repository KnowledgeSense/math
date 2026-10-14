import MeanMaximumForests.PeakAnalysis.ForestLocalMass
import MeanMaximumForests.PeakAnalysis.PeakTiltReduction

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

/-- Uniform adjacent-mass comparison at every integer tilted mean, for the actual forest law. -/
theorem forest_integer_adjacent_ratio (η : ℝ) (hη : 0 < η) : ∃ N : ℕ,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      N ≤ Fintype.card V → ∀ (z : ℝ) (hz : (1 / 4 : ℝ) ≤ z), z ≤ 1 →
      ∀ k : ℤ, (hardCoreLaw G (fun _ => z) (fun _ => by linarith)).expectation
        (fun I => (I.card : ℝ)) = (k : ℝ) →
        Real.exp (-η) * hardCoreIntegerMass G z (by linarith) k <
          hardCoreIntegerMass G z (by linarith) (k + 1) := by
  obtain ⟨c, D, hc, hD, N₀, hbounds⟩ := forest_integer_mass_bounds
  let δ := 1 - Real.exp (-η)
  have hδ : 0 < δ := by
    have h : Real.exp (-η) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    dsimp [δ]
    linarith
  let T := D / (δ * c)
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (T ^ 2)
  refine ⟨max N₀ N₁, ?_⟩
  intro V _ _ G hG hN z hz hz1 k hk
  have hz0 : 0 < z := by linarith
  obtain ⟨hlower, hgrad⟩ := hbounds G hG ((le_max_left _ _).trans hN) z hz hz1 k hk
  let s := Real.sqrt (Fintype.card V : ℝ)
  let x := hardCoreIntegerMass G z hz0 k
  let y := hardCoreIntegerMass G z hz0 (k + 1)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Fintype.card V := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsT : T < s := by
    have hN₁' : (N₁ : ℝ) ≤ Fintype.card V := by exact_mod_cast ((le_max_right _ _).trans hN)
    nlinarith only [hN₁, hN₁', hs2, hs0, hT]
  have hspos : 0 < s := hT.trans hsT
  have hnpos : (0 : ℝ) < Fintype.card V := by nlinarith only [hs2, sq_pos_of_pos hspos]
  have hstrict : D < s * (δ * c) := (div_lt_iff₀ (mul_pos hδ hc)).mp hsT
  have hlowscaled := mul_le_mul_of_nonneg_left hlower (mul_nonneg hs0 hδ.le)
  change s * δ * c ≤ s * δ * (s * x) at hlowscaled
  have hbig : (Fintype.card V : ℝ) * |y - x| < (Fintype.card V : ℝ) * (δ * x) := by
    change (Fintype.card V : ℝ) * |y - x| ≤ D at hgrad
    have hlo : s * (δ * c) ≤ (Fintype.card V : ℝ) * (δ * x) := by
      rw [← hs2]
      nlinarith only [hlowscaled]
    exact hgrad.trans_lt (hstrict.trans_le hlo)
  have hclose : |y - x| < δ * x := (mul_lt_mul_iff_right₀ hnpos).mp hbig
  have hyx := (abs_lt.mp hclose).1
  change Real.exp (-η) * x < y
  dsimp [δ] at hyx
  linarith

 theorem hardCoreIntegerMass_exp_nat {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℝ) (k : ℕ) :
    hardCoreIntegerMass G (Real.exp t) (Real.exp_pos t) (k : ℤ) = graphTiltSizeMass G t k := by
  unfold hardCoreIntegerMass graphTiltSizeMass
  congr 1
  funext I
  simp only [Nat.cast_inj]

 theorem forest_tilted_adjacent_ratio (η : ℝ) (hη : 0 < η) : ∃ N : ℕ,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      N ≤ Fintype.card V → ∀ k : ℕ, ∀ t ∈ Set.Icc (Real.log (1 / 4)) 0,
      graphTiltMean G t = k →
      Real.exp (-η) * graphTiltSizeMass G t k < graphTiltSizeMass G t (k + 1) := by
  obtain ⟨N, hN⟩ := forest_integer_adjacent_ratio η hη
  refine ⟨N, ?_⟩
  intro V _ _ G hG hn k t ht hk
  have hz : (1 / 4 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4)]
    exact Real.exp_le_exp.mpr ht.1
  have hz1 : Real.exp t ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr ht.2
  have h := hN G hG hn (Real.exp t) hz hz1 (k : ℤ) (by simpa only [Int.cast_natCast, graphTiltMean] using hk)
  simpa only [← Int.natCast_add, ← Int.natCast_one, hardCoreIntegerMass_exp_nat] using h

end MeanMaximumForests.PeakAnalysis
