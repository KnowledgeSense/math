import SphericalTreeFailures.TailNoise

namespace SphericalTreeFailures
open Finset

noncomputable def tailMeanDifference (k : ℕ) (activity : ℝ) : ℝ :=
  pathMean (2 * k) activity - pathMean (2 * k + 1) activity

noncomputable def totalCenterDensity (p : ℝ) (k : ℕ) (activity : ℝ) : ℝ :=
  2 * stationaryProbability p + pathMean (2 * k + 1) activity +
    tailMeanDifference k activity * stationaryProbability p

noncomputable def totalCenter (p : ℝ) (k m : ℕ) (activity : ℝ) : ℝ :=
  totalCenterDensity p k activity * 2 ^ m - stationaryProbability p

theorem selectedTailMean_affine (k : ℕ) (activity : ℝ) (i : Bool) :
    selectedTailMean k activity i = pathMean (2 * k + 1) activity +
      tailMeanDifference k activity * boolIndicator i := by
  cases i <;> simp [selectedTailMean, tailMeanDifference, boolIndicator]

theorem level_occupation_decomposition (p : ℝ) (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    ∑ v ∈ binaryLevel h, boolIndicator (broadcastState i ω v) =
      census p i h ω + (2 : ℝ) ^ h * stationaryProbability p := by
  simp [census, sum_sub_distrib]

theorem sum_two_pow (m : ℕ) : (∑ h ∈ range (m + 1), (2 : ℝ) ^ h) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [sum_range_succ, ih, pow_succ, pow_succ]; ring

theorem sampledTotalSize_decomposition (p : ℝ) (k m : ℕ) (activity : ℝ)
    (i : Bool) (ω : TotalSizeSpace k) :
    sampledTotalSize k m i ω - totalCenter p k m activity =
      (∑ h ∈ range (m + 1), census p i h ω.1) +
        tailMeanDifference k activity * census p i m ω.1 + tailNoise k m activity i ω := by
  have hs (v : BinaryNode) : selectedTailSize k (broadcastState i ω.1 v) (ω.2 v) =
      tailSampleNoise k activity (broadcastState i ω.1 v) (ω.2 v) +
        (pathMean (2 * k + 1) activity +
          tailMeanDifference k activity * boolIndicator (broadcastState i ω.1 v)) := by
    rw [← selectedTailMean_affine]
    unfold tailSampleNoise
    ring
  unfold sampledTotalSize
  simp_rw [hs, level_occupation_decomposition p]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum,
    level_occupation_decomposition p, ← sum_mul, sum_two_pow]
  simp only [sum_const, nsmul_eq_mul, card_binaryLevel, Nat.cast_pow, Nat.cast_ofNat]
  unfold totalCenter totalCenterDensity tailNoise
  rw [pow_succ]
  ring

end SphericalTreeFailures
